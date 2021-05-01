const util = require('util');
const R = require('ramda');
const pureRandom = require('pure-random');
const {rights} = require('sanctuary');
const {Machine, assign, pure} = require('xstate');
const State = require('crocks/State');
const Pair = require('crocks/Pair');
const { countReset } = require('console');

///// Utilities

const raiseError = msg => { throw new Error(msg); };

const logRet = fn => (...args) => {
  const ret = fn(...args);
  console.log(fn.name, ret);
  return ret;
}

const UINT32_MAX = Math.pow(2, 32) - 1;
const PRIMES = [160481183, 179424673, 198491317, 217645177];

const Rand = {
  _nextSeed: seed => R.append(pureRandom.randUint(seed), R.slice(1, 4, seed)),
  _random: (seed, min, max) => Math.round(min + pureRandom.randUint(seed) / UINT32_MAX * (max - min)),

  makeSeed: (iseed, n) => iseed ? R.reduceRight(R.compose, R.identity, R.repeat(Rand._nextSeed, n || 10))(PRIMES.map(p => p * iseed)) : pureRandom.genSeed(),

  random: (min, max) => State(seed => Pair(Rand._random(seed, min, max), Rand._nextSeed(seed))),

  shuffle: list => list.length <= 1 ? State.of(list) :
    Rand.random(0, list.length - 1).chain(i =>
      Rand.shuffle(R.remove(i, 1, list)).map(tail => R.prepend(list[i], tail)))
};

///// Player

const activePlayerLens = (() => {
  // Context -> Player
  const getter = context => context.players[context.whoseTurn];
  // Context -> Player -> Context
  const setter = (player, context) => R.evolve({players: R.update(context.whoseTurn, player)}, context);

  return R.lens(getter, setter);
})();

const playerLens = idx => {
  // Context -> Player
  const getter = context => context.players[idx];
  // Context -> Player -> Context
  const setter = (player, context) => R.evolve({players: R.update(idx, player)}, context);

  return R.lens(getter, setter);
};

const processing = lens => m => State.get().chain(s0 => {
  const [res, s1] = m.runWith(R.view(lens, s0)).toArray();
  return State.put(R.set(lens, s1, s0)).map(() => res);
});

// Lifts a Rand function to act on a game context
const liftRand = processing(R.lensProp('seed'));
// Lifts a deck function to act on a game context
const liftDeck = processing(R.lensProp('deck'));
// Lifts a player function to act on a game context
const liftPlayer = R.uncurryN(2, idx => processing(playerLens(idx)));

const Player = {
  // Player -> Number
  countInf: R.pipe(
    R.prop('influence'),
    R.reject(R.propEq('revealed', true)),
    R.length),

  // Player -> Boolean
  hasNInf: R.curry((n, player) => Player.countInf(player) == n),

  // Player -> Boolean
  isDead: player => Player.hasNInf(0, player),

  // Number -> Player -> Player
  adjustCash: dcash => R.evolve({cash: R.add(dcash)}),

  kill: R.evolve({'influence': R.map(R.assoc('revealed', true))}),

  revealRole: R.curry((role, player) => {
    const idx = R.findIndex(R.equals({role: role, revealed: false}), player.influence);
    if (idx == -1) raiseError(`Player does not have role ${role}`);
    return R.evolve({influence: R.adjust(idx, R.assoc('revealed', true))}, player);
  }),

  unrevealRole: R.curry((role, player) => {
    const idx = R.findIndex(R.equals({role: role, revealed: true}), player.influence);
    if (idx == -1) raiseError(`Player does not have role ${role}`);
    return R.evolve({influence: R.adjust(idx, R.assoc('revealed', false))}, player);
  }),

  swapRole_s: (oldRole, newRole) => State.get().chain(player => {
    const idx = R.findIndex(R.equals({role: oldRole, revealed: false}), player.influence);
    if (idx == -1) raiseError(`Player does not have role ${oldRole}`);
    return State.put(R.evolve({influence: R.adjust(idx, R.assoc('role', newRole))}, player));
  })
};

///// Game

const Game = {
  isOver: R.pipe(
    R.prop('players'),
    R.reject(Player.isDead),
    R.length(),
    R.equals(1)),

  //checkOver: R.when(Game.isOver, R.set(State.lens, {id: State.GAME_OVER})),

  opponents: game => R.pipe(
    R.prop('players'),
    R.addIndex (R.map) (R.pair),
    R.filter(pair => !Player.isDead(pair[0]) && pair[1] != game.whoseTurn),
    R.map(R.nth(1))
  ) (game),

  pushDeck_s: role => liftDeck(State(deck => Pair(null, R.insert(0, role, deck)))),

  popDeck_s: () => liftDeck(State(deck => Pair(deck[0], R.remove(0, 1, deck)))),

  shuffleDeck_s: () => liftDeck(State.get()).chain(
    deck => liftRand(Rand.shuffle(deck))).chain(
      deck => liftDeck(State.put(deck))),

  turnEq: R.propEq('whoseTurn'),
  actionEq: R.propEq('currentAction'),

  applyRevealAction: context => R.assoc('revealer', context.target, context)
};

Game.applyAction = R.cond([
  [Game.actionEq('income'), R.over(activePlayerLens, Player.adjustCash(1))],
  [Game.actionEq('foreign-aid'), R.over(activePlayerLens, Player.adjustCash(2))],
  [Game.actionEq('tax'), R.over(activePlayerLens, Player.adjustCash(3))],
  [Game.actionEq('assassinate'), Game.applyRevealAction]
]);

class GameDef {
  constructor(roles) {
    this.roles = Object.freeze(roles || ['duke', 'assassin', 'captain', 'ambassador', 'contessa']);
    this.actions = Object.freeze({
      'coup': {
        cost: 7,
        targeted: true
      },
      'income': {
        cost: 0,
        gain: 1
      },
      'foreign-aid': {
        cost: 0,
        gain: 2,
        blockedBy: 'duke'
      },
      'tax': {
        cost: 0,
        gain: 3,
        roles: 'duke'
      },
      'assassinate': {
        cost: 3,
        roles: 'assassin',
        targeted: true,
        blockedBy: 'contessa'
      },
      'steal': {
        cost: 0,
        roles: 'captain',
        targeted: true,
        blockedBy: ['captain', 'ambassador', 'inquisitor']
      },
      'exchange': {
        cost: 0,
        roles: ['ambassador', 'inquisitor']
      },
      'interrogate': {
        cost: 0,
        roles: 'inquisitor',
        targeted: true
      }
    });
  }

  isValidRole(role) {
    return R.includes(role, this.roles);
  }

  isValidAction(action) {
    return action in this.actions;
  }

  getRequiredRoles(action) {
    return R.flatten([this.actions[action].roles || []]);
  }

  getBlockingRoles(action) {
    return R.flatten([this.actions[action].blockedBy || []]);
  }

  isRoleRequired(action) {
    return this.getRequiredRoles(action).length > 0;
  }

  isBlockable(action) {
    return this.getBlockingRoles(action).length > 0;
  }

  isBlockedBy(action, role) {
    return R.includes(role, this.getBlockingRoles(action));
  }

  ifRoleAllowsAction(role, action) {
    return R.includes(role, this.getRequiredRoles(action));
  }

  isTargeted(action) {
    return this.actions[action].targeted;
  }

  makeDeck() {
    return R.flatten(this.roles.map(el => R.repeat(el, 3)));
  }

  [Symbol.for('nodejs.util.inspect.custom')](depth, opts) {
    return `GameDef(${util.inspect(this.roles, false, depth, opts)})`;
  }
}

// Number -> String -> Context -> Context
const redealPlayerRole = R.curry(
  (idx, oldRole, context) => Game.pushDeck_s(oldRole).chain(
    () => Game.shuffleDeck_s()).chain(
      () => Game.popDeck_s()).chain(
        newRole => liftPlayer(idx, Player.swapRole_s(oldRole, newRole))).execWith(context));

// Number -> String -> Context -> Boolean
const playerHasRole = R.uncurryN(3, (idx, role) => R.pipe(
  R.view(playerLens(idx)),
  R.prop('influence'),
  R.any(R.both(
    R.propEq('revealed', false),
    R.propEq('role', role)))
));

// todo: check player is alive
const isValidPlayerIdx = (context, idx) => typeof idx === 'number' && idx >= 0 && idx < context.players.length;

const assertValidPlayer = (context, event, meta) => {
  if (!('player' in event) || !isValidPlayerIdx(context, event.player)) {
    throw new Error(`${event.type} event must specify a valid player`);
  }
  return true;
};

const assertCanStartAction = (context, event, meta) => {
  assertValidPlayer(context, event, meta);
  if (!('action' in event) || !context.def.isValidAction(event.action)) {
    throw new Error(`${event.type} event must specify a valid action`);
  }
  if (event.player !== context.whoseTurn) {
    throw new Error(`${event.type} event not allowed from player ${event.player}`);
  }
  if (context.def.isTargeted(event.action)) {
    if (!('target' in event) || !isValidPlayerIdx(context, event.target)) {
      throw new Error(`${event.type} event must target a valid player`);
    }
    if (event.target === context.whoseTurn) {
      throw new Error(`${event.type} event cannot target player ${event.target}`);
    }
  }
  return true;
};

const assertCanReveal = (context, event, meta) => {
  assertValidPlayer(context, event, meta);
  if (event.player !== context.revealer) {
    throw new Error(`${event.type} event not allowed from player ${event.player}`);
  }
  if (!('role' in event) || !context.def.isValidRole(event.role)) {
    throw new Error(`${event.type} event must specify a valid role`);
  }
  if (!playerHasRole(event.player, event.role, context)) {
    throw new Error(`${event.type} event must specify a role that is held by the player and not yet revealed`);
  }
  return true;
};

const assertValidOpponent = (context, event, meta) => {
  assertValidPlayer(context, event, meta);
  if (event.player === context.whoseTurn) {
    throw new Error(`${event.type} event not allowed from player ${event.player}`);
  }
  return true;
};

const assertCurrentPlayer = (context, event, meta) => {
  assertValidPlayer(context, event, meta);
  if (event.player !== context.whoseTurn) {
    throw new Error(`${event.type} event not allowed from player ${event.player}`);
  }
  return true;
};

const assertCanChallenge = (context, event, meta) => {
  if (context.blocker) {
    assertValidPlayer(context, event, meta);
    // The player who is blocking cannot challenge
    if (event.player === context.blocker) {
      throw new Error(`${event.type} event not allowed from player ${event.player}`);
    }
  } else {
    // The player whose turn it is cannot challenge
    assertValidOpponent(context, event, meta);
    if (!context.def.isRoleRequired(context.currentAction)) {
      throw new Error(`Action ${context.currentAction} cannot be challenged`);
    }
  }
  return true;
};

const assertCanBlock = (context, event, meta) => {
  assertValidOpponent(context, event, meta);
  if (!('role' in event) || (typeof event.role != 'string')) {
    throw new Error(`${event.type} event must specify a valid role`);
  }
  if (!context.def.isBlockedBy(context.currentAction, event.role)) {
    throw new Error(`Action ${context.currentAction} cannot be blocked by role ${event.role}`);
  }
  return true;
};

const ifActionHasResponse = (context, event, meta) =>
  context.def.isRoleRequired(context.currentAction) || context.def.isBlockable(context.currentAction);

const ifActionHasNoResponse = (context, event, meta) => !ifActionHasResponse(context, event, meta);

const ifChallengeIncorrect = (context, event, meta) =>
  context.blocker != null ? context.def.isBlockedBy(context.currentAction, context.revealedRole) :
  context.def.ifRoleAllowsAction(context.revealedRole, context.currentAction);

const ifPendingReveal = context => context.revealer != null && context.revealedRole == null;

const ifActionWasBlocked = context => context.blocker != null;

const allConds = (...conds) => (context, event, meta) => R.all(cond => cond(context, event, meta), conds);

const setCurrentAction = assign({
  currentAction: (context, event) => event.action,
  target: (context, event) => typeof event.target == 'number' ? event.target : null
});

const setChallenger = assign({
  challenger: (context, event) => event.player
});

const setBlocker = assign({
  blocker: (context, event) => event.player
});

const setRevealer = valueGetter => assign({
  revealer: (context, event) => valueGetter(context),
  revealedRole: null
});

const advanceTurn = assign({
  // todo: living players
  whoseTurn: context => (context.whoseTurn + 1) % context.players.length
});

const applyAction = assign(Game.applyAction);

const revealInfluence = assign((context, event) => R.pipe(
  R.over(playerLens(event.player), Player.revealRole(event.role)),
  R.assoc('revealedRole', event.role)
)(context));

const replaceInfluence = assign((context, event) => R.pipe(
  R.over(playerLens(context.revealer), Player.unrevealRole(context.revealedRole)),
  redealPlayerRole(context.revealer, context.revealedRole)
)(context));

const resetContext = assign({
  currentAction: null,
  blocker: null,
  challenger: null,
  revealer: null,
  revealedRole: null
});

const gameMachine = Machine({
  id: 'game',
  strict: true,

  initial: 'StartOfTurn',

  states: {
    StartOfTurn: {
      entry: resetContext,
      on: {
        ACTION: {target: 'WaitForResponse', cond: assertCanStartAction}
      }
    },

    WaitForResponse: {
      entry: setCurrentAction,
      always: [
        {target: 'FinishAction', cond: ifActionHasNoResponse},
      ],
      on: {
        BLOCK: {target: 'Block', cond: assertCanBlock},
        CHALLENGE: {target: 'Challenge', cond: assertCanChallenge},
        ALLOW: {target: 'FinishAction', cond: assertValidOpponent}
      }
    },

    Block: {
      entry: [
        setBlocker
      ],
      on: {
        CHALLENGE: {target: 'Challenge', cond: assertCanChallenge},
        ALLOW: {target: 'EndOfTurn', cond: assertCurrentPlayer}
      }
    },

    Challenge: {
      entry: [
        setChallenger,
        setRevealer(context => ifActionWasBlocked(context) ? context.blocker : context.whoseTurn)
      ],
      on: {
        REVEAL: {target: 'ExecRevealOnChallenge', cond: assertCanReveal}
      }
    },

    ExecRevealOnChallenge: {
      entry: revealInfluence,
      always: [
        {target: 'ChallengeIncorrect', cond: ifChallengeIncorrect},
        // If a block was correctly challenged, the action succeeds
        {target: 'FinishAction', cond: ifActionWasBlocked},
        // Otherwise, an action was correctly challenged, so it does not occur
        'EndOfTurn'
      ]
    },

    ChallengeIncorrect: {
      entry: [
        replaceInfluence,
        setRevealer(context => context.challenger)
      ],
      on: {
        REVEAL: [
          // If a block was incorrectly challenged, the block succeeds
          {target: 'EndOfTurn', cond: allConds(assertCanReveal, ifActionWasBlocked), actions: revealInfluence},
          // Otherwise, an action was incorrectly challenged, so the action succeeds
          {target: 'FinishAction', cond: assertCanReveal, actions: revealInfluence}
        ]
      }
    },

    FinishAction: {
      entry: applyAction,
      always: [
        // A reveal will be pending after 'coup' and 'assassinate' actions
        {target: 'RevealOnAction', cond: ifPendingReveal},
        'EndOfTurn'
      ]
    },

    RevealOnAction: {
      on: {
        REVEAL: {target: 'EndOfTurn', cond: assertCanReveal, actions: revealInfluence}
      }
    },

    EndOfTurn: {
      //todo: check for game over
      exit: advanceTurn,
      always: 'StartOfTurn'
    }
  }
});

const inspectState = state => util.inspect(R.pick(['value', 'changed', 'context'], state), false, null, true);

const logState = state => console.log(inspectState(state));

const assertContext = (state, preds) => R.allPass(R.flatten([preds])) (state.context) || raiseError(`Failed to assert context on ${inspectState(state)}`);

const assertState = (state, id) => state.value == id || raiseError(`Expected state ${id} but was ${inspectState(state)}`);

const arrayHash = hashFn => R.reduce((acc, el) => acc + 23 * hashFn(el), 17);
const intArrayHash = arrayHash(R.identity);
const stringHash = R.pipe(
  R.split(''),
  R.map(char => char.codePointAt(0)),
  intArrayHash);
const stringArrayHash = arrayHash(stringHash);
const deckHash = R.pipe(R.path(['context', 'deck']), stringArrayHash);

const turnEq = R.propEq('whoseTurn');
const actionEq = R.propEq('currentAction');

const playerHasCash = (idx, cash) => R.pipe(
  R.view(playerLens(idx)),
  R.propEq('cash', cash)
);

const playerHasNInf = (idx, n) => R.pipe(
  R.view(playerLens(idx)),
  Player.hasNInf(n)
);

const sampleGame = (seed, context) => {
  const def = new GameDef();
  const deck = def.makeDeck();
  return Game.shuffleDeck_s().execWith(R.mergeLeft(context, {def, seed, deck}))
};

const initialContext = sampleGame(Rand.makeSeed(123), {
  whoseTurn: 0,
  currentAction: null,
  challenger: null,

  players: [
    {
      cash: 2,
      influence: [
        {role: 'duke', revealed: false},
        {role: 'captain', revealed: false}
      ]
    },
    {
      cash: 2,
      influence: [
        {role: 'assassin', revealed: false},
        {role: 'duke', revealed: false}
      ]
    }
  ]
});

const game0 = gameMachine.withContext(initialContext).initialState;
assertState(game0, 'StartOfTurn');
assertContext(game0, [
  turnEq(0),
  actionEq(null),
  playerHasCash(0, 2),
  playerHasCash(1, 2)
]);

const game1 = gameMachine.transition(game0, {type: 'ACTION', action: 'income', player: 0});
assertState(game1, 'StartOfTurn');
assertContext(game1, [
  turnEq(1),
  actionEq(null),
  playerHasCash(0, 3),
  playerHasCash(1, 2)
]);

const game2 = gameMachine.transition(game1, {type: 'ACTION', action: 'tax', player: 1});
assertState(game2, 'WaitForResponse');
assertContext(game2, [
  turnEq(1),
  actionEq('tax')
]);

const game3 = gameMachine.transition(game2, {type: 'ALLOW', player: 0});
assertState(game3, 'StartOfTurn');
assertContext(game3, [
  turnEq(0),
  playerHasCash(1, 5)
]);

const game3a = gameMachine.transition(game2, {type: 'CHALLENGE', player: 0});
assertState(game3a, 'Challenge');
assertContext(game3a, [
  turnEq(1),
  R.propEq('revealer', 1)
]);

// Lose the challenge by revealing a role which is not duke
const game3a_1 = gameMachine.transition(game3a, {type: 'REVEAL', role: 'assassin', player: 1});
assertState(game3a_1, 'StartOfTurn');
assertContext(game3a_1, [
  turnEq(0),
  playerHasNInf(1, 1),        // Player lost an influence
  playerHasCash(1, 2),        // Player did not draw tax
  R.complement(playerHasRole(1, 'assassin'))
]);

// Win the challenge by revealing a duke
const game3a_1a = gameMachine.transition(game3a, {type: 'REVEAL', role: 'duke', player: 1});
assertState(game3a_1a, 'ChallengeIncorrect');
assertContext(game3a_1a, [
  turnEq(1),
  R.propEq('revealer', 0),
  playerHasNInf(1, 2),                      // Player replaced their duke with a new role from the deck
  R.complement(playerHasRole(1, 'duke')),
]);
if (deckHash(game3a_1a) === deckHash(game3a)) raiseError("Expected deck to be shuffled");

// Now the challenger must reveal
const game3a_1a_2 = gameMachine.transition(game3a_1a, {type: 'REVEAL', role: 'duke', player: 0});
assertState(game3a_1a_2, 'StartOfTurn');
assertContext(game3a_1a_2, [
  turnEq(0),
  playerHasNInf(0, 1),
  R.complement(playerHasRole(0, 'duke')),   // Challenger lost their duke
  playerHasCash(1, 5)                       // Player drew tax
]);

// Play foreign aid instead of tax
const game4 = gameMachine.transition(game3, {type: 'ACTION', action: 'foreign-aid', player: 0});
assertState(game4, 'WaitForResponse');
assertContext(game4, [
  turnEq(0),
  actionEq('foreign-aid')
]);

// Block foreign aid with duke
const game5 = gameMachine.transition(game4, {type: 'BLOCK', role: 'duke', player: 1});
assertState(game5, 'Block');
assertContext(game5, [
  turnEq(0),
  actionEq('foreign-aid')
]);

// Allow the block
const game6 = gameMachine.transition(game5, {type: 'ALLOW', player: 0});
assertState(game6, 'StartOfTurn');
assertContext(game6, [
  turnEq(1),
  playerHasCash(0, 3)   // Foreign aid was blocked
]);

// Challenge the block
const game6a = gameMachine.transition(game5, {type: 'CHALLENGE', player: 0});
assertState(game6a, 'Challenge');
assertContext(game6a, [
  turnEq(0),
  R.propEq('revealer', 1),
]);

// Win the challenge by revealing a duke, blocking foreign aid
const game6a_1 = gameMachine.transition(game6a, {type: 'REVEAL', role: 'duke', player: 1});
assertState(game6a_1, 'ChallengeIncorrect');
assertContext(game6a_1, [
  turnEq(0),
  R.propEq('revealer', 0),
  playerHasNInf(1, 2),                      // Player replaced their duke with a new role from the deck
  R.complement(playerHasRole(1, 'duke')),
]);
if (deckHash(game6a_1) === deckHash(game6a)) raiseError("Expected deck to be shuffled");

// Now the challenger must reveal
const game6a_2 = gameMachine.transition(game6a_1, {type: 'REVEAL', role: 'duke', player: 0});
assertState(game6a_2, 'StartOfTurn');
assertContext(game6a_2, [
  turnEq(1),
  playerHasNInf(0, 1),                      // Player lost their duke
  playerHasCash(0, 3)                       // Player did not draw foreign aid
]);

// Lose the challenge by revealing a role other than duke
const game6a_1a = gameMachine.transition(game6a, {type: 'REVEAL', role: 'assassin', player: 1});
assertState(game6a_1a, 'StartOfTurn');
assertContext(game6a_1a, [
  turnEq(1),
  playerHasNInf(1, 1),                      // Challenger lost their assassin
  R.complement(playerHasRole(1, 'assassin')),
  playerHasCash(0, 5)                       // Player drew foreign aid
]);

const game7 = gameMachine.transition(game6, {type: 'ACTION', action: 'assassinate', player: 1, target: 0});
assertState(game7, 'WaitForResponse');

const game8 = gameMachine.transition(game7, {type: 'ALLOW', player: 0});
assertState(game8, 'RevealOnAction');

const game9 = gameMachine.transition(game8, {type: 'REVEAL', role: 'captain', player: 0});
assertState(game9, 'StartOfTurn');
assertContext(game9, [
  turnEq(0),
  playerHasNInf(0, 1),
  R.complement(playerHasRole(0, 'captain'))
]);

console.log('Pass');
