const util = require('util');
const R = require('ramda');
const pureRandom = require('pure-random');
const {Machine, assign} = require('xstate');
const State = require('crocks/State');
const Pair = require('crocks/Pair');

///// Utilities

const raiseError = msg => { throw new Error(msg); };

const logRet = fn => (...args) => {
  const ret = fn(...args);
  console.log(fn.name, ret);
  return ret;
}

const debug = fn => assign(context => (fn(context), context));

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

const processing = lens => m => State.get().chain(s0 => {
  const [res, s1] = m.runWith(R.view(lens, s0)).toArray();
  return State.put(R.set(lens, s1, s0)).map(() => res);
});

// Lifts a Rand function to act on a game context
const liftRand = processing(R.lensProp('seed'));
// Lifts a deck function to act on a game context
const liftDeck = processing(R.lensProp('deck'));
// Lifts a player function to act on a game context
const liftPlayer = R.uncurryN(2, idx => processing(Player.lens(idx)));

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

  getFirstRole: player => R.prop('role', R.find(inf => !inf.revealed, player.influence)),

  swapRole_s: (oldRole, newRole) => State.get().chain(player => {
    const idx = R.findIndex(R.equals({role: oldRole, revealed: false}), player.influence);
    if (idx == -1) raiseError(`Player does not have role ${oldRole}`);
    return State.put(R.evolve({influence: R.adjust(idx, R.assoc('role', newRole))}, player));
  }),

  lens: idx => {
    // Context -> Player
    const getter = context => context.players[idx];
    // Context -> Player -> Context
    const setter = (player, context) => R.evolve({players: R.update(idx, player)}, context);
  
    return R.lens(getter, setter);
  }
};

///// Game

const Game = {
  isOver: R.pipe(
    R.prop('players'),
    R.reject(Player.isDead),
    R.length(),
    R.equals(1)),

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

  applyRevealAction: context => R.assoc('revealer', context.target, context),

  playerHasCash: (idx, cash) => R.pipe(
    R.view(Player.lens(idx)),
    R.propEq('cash', cash)
  ),

  playerCanAffordAction: R.curry((idx, action, context) => {
    const cost = context.def.getCost(action);
    const cash = R.view(Player.lens(idx), context).cash;
    return cost <= cash;
  }),

  playerHasNInf: (idx, n) => R.pipe(
    R.view(Player.lens(idx)),
    Player.hasNInf(n)
  ),

  // Number -> String -> Context -> Boolean
  playerHasRole: R.uncurryN(3, (idx, role) => R.pipe(
    R.view(Player.lens(idx)),
    R.prop('influence'),
    R.any(R.both(
      R.propEq('revealed', false),
      R.propEq('role', role)))
  ))
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
        gain: 1
      },
      'foreign-aid': {
        gain: 2,
        blockedBy: 'duke'
      },
      'tax': {
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
        roles: 'captain',
        targeted: true,
        blockedBy: ['captain', 'ambassador', 'inquisitor']
      },
      'exchange': {
        roles: ['ambassador', 'inquisitor']
      },
      'interrogate': {
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

  getCost(action) {
    return this.actions[action].cost || 0;
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
  if (!Game.playerCanAffordAction(event.player, event.action, context)) {
    throw new Error(`Player ${event.player} cannot afford action ${event.action}`);
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
  if (!Game.playerHasRole(event.player, event.role, context)) {
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
  if (ifActionWasBlocked(context)) {
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

const ifActionHasResponse = context =>
  context.def.isRoleRequired(context.currentAction) || context.def.isBlockable(context.currentAction);

const ifActionHasNoResponse = (context, event, meta) => !ifActionHasResponse(context, event, meta);

const ifChallengeIncorrect = context =>
  context.blocker != null ? context.def.isBlockedBy(context.currentAction, context.revealedRole) :
  context.def.ifRoleAllowsAction(context.revealedRole, context.currentAction);

const ifPendingReveal = context => context.revealer != null && context.revealedRole == null;

const ifBlockableAction = context => context.def.isBlockable(context.currentAction);

const ifActionWasBlocked = context => context.blocker != null;

const ifAutoReveal = context => Game.playerHasNInf(context.revealer, 1)(context);

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

const clearRevealer = assign({
  revealer: null,
  revealedRole: null
});

const advanceTurn = assign({
  // todo: living players
  whoseTurn: context => (context.whoseTurn + 1) % context.players.length
});

const applyAction = assign(Game.applyAction);

const revealInfluence = assign((context, event) => {
  // For auto-reveal there is no event; we reveal the player's only role.
  let role = event.role || R.pipe(
    R.view(Player.lens(context.revealer)),
    Player.getFirstRole
  )(context);
  return R.pipe(
    R.over(Player.lens(context.revealer), Player.revealRole(role)),
    R.assoc('revealedRole', role)
  )(context)
});

const replaceInfluence = assign(context => R.pipe(
  R.over(Player.lens(context.revealer), Player.unrevealRole(context.revealedRole)),
  redealPlayerRole(context.revealer, context.revealedRole)
)(context));

const payActionCost = assign(context => 
  R.over(activePlayerLens, Player.adjustCash(-context.def.getCost(context.currentAction)), context));

const resetContext = assign({
  currentAction: null,
  target: null,
  blocker: null,
  challenger: null,
  revealer: null,
  revealedRole: null
});

const GameMachine = Machine({
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
        BLOCK: {target: 'Block', cond: assertCanBlock, actions: payActionCost},
        CHALLENGE: {target: 'Challenge', cond: assertCanChallenge},
        ALLOW: {target: 'FinishAction', cond: assertValidOpponent, actions: payActionCost}
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
      always: {target: 'ExecRevealOnChallenge', cond: ifAutoReveal},
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
        {target: 'EndOfTurn'}
      ]
    },

    ChallengeIncorrect: {
      entry: [
        replaceInfluence,
        setRevealer(context => context.challenger)
      ],
      always: {target: 'ExecCounterReveal', cond: ifAutoReveal},
      on: {
        REVEAL: {target: 'ExecCounterReveal', cond: assertCanReveal}
      }
    },

    // After an incorrect challenge, the challenger must reveal
    ExecCounterReveal: {
      entry: revealInfluence,
      always: [
        // If a block was incorrectly challenged, the block succeeds
        {target: 'EndOfTurn', cond: ifActionWasBlocked},
        // Otherwise, an action was incorrectly challenged. If the action is blockable, check if the opponent wants to block
        {target: 'WaitForBlock', cond: ifBlockableAction},
        // Otherwise, an action was incorrectly challenged, so the action succeeds
        {target: 'FinishAction'}
      ]
    },

    // Occurs after an action has been unsuccessfully challenged, when there is still a last chance to block
    WaitForBlock: {
      entry: [
        clearRevealer,
        payActionCost
      ],
      on: {
        BLOCK: {target: 'Block', cond: assertCanBlock},
        ALLOW: {target: 'FinishAction', cond: assertValidOpponent}
      }
    },

    FinishAction: {
      entry: [
        clearRevealer,
        applyAction
      ],
      always: [
        // A reveal will be pending after 'coup' and 'assassinate' actions
        {target: 'RevealOnAction', cond: ifPendingReveal},
        'EndOfTurn'
      ]
    },

    RevealOnAction: {
      always: {target: 'EndOfTurn', cond: ifAutoReveal, actions: revealInfluence},
      on: {
        REVEAL: {target: 'EndOfTurn', cond: assertCanReveal, actions: revealInfluence}
      }
    },

    EndOfTurn: {
      always: [
        {target: 'GameOver', cond: Game.isOver},
        {target: 'StartOfTurn', actions: advanceTurn}
      ]
    },

    GameOver: {}
  }
});

module.exports = {Rand, GameDef, Game, Player, GameMachine};
