const util = require('util');
const R = require('ramda');
const pureRandom = require('pure-random');
const {rights} = require('sanctuary');
const {Machine, assign, pure} = require('xstate');

///// Utilities

const raiseError = msg => { throw new Error(msg); };

const Rand = {
  nextSeed: seed => R.append(pureRandom.randUint(seed), R.slice(1, 4, seed)),

  random: (seed, min, max) => [Rand.nextSeed(seed), rights([pureRandom.random(seed, min, max)])[0]],
  
  shuffle: (seed, list) => {
    if (list.length <= 1) {
      return [seed, list];
    } else {
      const [seed1, i] = Rand.random(seed, 0, list.length - 1);
      const [seed2, tail] = Rand.shuffle(seed1, R.remove(i, 1, list));
      return [seed2, R.prepend(list[i], tail)];
    }
  }
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

  restoreRole: R.curry((role, player) => {
    const idx = R.findIndex(R.equals({role: role, revealed: true}), player.influence);
    if (idx == -1) raiseError(`Player does not have role ${role}`);
    return R.evolve({influence: R.adjust(idx, R.assoc('revealed', false))}, player);
  }),

  replaceRole: R.curry((oldRole, newRole, player) => {
    const idx = R.findIndex(R.equals({role: oldRole, revealed: false}), player.influence);
    if (idx == -1) raiseError(`Player does not have role ${oldRole}`);
    return R.evolve({influence: R.adjust(idx, R.assoc('role', newRole))}, player);
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

  random: R.curry((min, max, ctx0) => {
    const [seed, n] = Rand.random(ctx0.seed, min, max);
    return [n, R.assoc('seed', seed, ctx0)];
  }),

  // todo
  replaceRole: (role, context) => context,

  drawRole: context => [context.deck[0], R.evolve({deck: R.remove(0, 1)}, context)],

  turnEq: R.propEq('whoseTurn'),
  actionEq: R.propEq('currentAction')
};

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
        blockedBy: ['duke']
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
        blockedBy: ['contessa']
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

  isRoleRequired(action) {
    return this.getRequiredRoles(action).length > 0;
  }

  ifRoleAllowsAction(role, action) {
    return R.includes(role, this.getRequiredRoles(action));
  }

  makeDeck() {
    return R.flatten(this.roles.map(el => R.repeat(el, 3)));
  }

  [Symbol.for('nodejs.util.inspect.custom')](depth, opts) {
    return `GameDef(${util.inspect(this.roles, false, depth, opts)})`;
  }
}

// Number -> String -> Context -> Context
const redealPlayerRole = R.curry((idx, oldRole, ctx0) => {
  const ctx1 = Game.replaceRole(oldRole, ctx0);
  const [newRole, ctx2] = Game.drawRole(ctx1);
  return R.over(playerLens(idx), Player.replaceRole(oldRole, newRole), ctx2);
});

// Number -> String -> Context -> Boolean
const playerHasRole = R.uncurryN(3, (idx, role) => R.pipe(
  R.view(playerLens(idx)),
  R.prop('influence'),
  R.any(R.both(
    R.propEq('revealed', false),
    R.propEq('role', role)))
));

const assertValidPlayer = (context, event, meta) => {
  if (!('player' in event) || (typeof event.player != 'number') || event.player < 0 || event.player >= context.players.length) {
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

const assertCanChallenge = (context, event, meta) => {
  assertValidPlayer(context, event, meta);
  if (event.player === context.whoseTurn) {
    throw new Error(`${event.type} event not allowed from player ${event.player}`);
  }
  return true;
};

const ifChallengeableAction = (context, event, meta) => context.def.isRoleRequired(context.currentAction);

const ifChallengeIncorrect = (context, event, meta) => context.def.ifRoleAllowsAction(context.revealedRole, context.currentAction);

const setCurrentAction = assign({
  currentAction: (context, event) => event.action
});

const setChallenger = assign({
  challenger: (context, event) => event.player
});

const setRevealer = value => assign({
  revealer: (context, event) => value(context),
  revealedRole: null
});

const advanceTurn = assign({
  // todo: living players
  whoseTurn: context => (context.whoseTurn + 1) % context.players.length
});

const applyAction = assign(R.cond([
  [Game.actionEq('income'), R.over(activePlayerLens, Player.adjustCash(1))],
  [Game.actionEq('tax'), R.over(activePlayerLens, Player.adjustCash(3))]
]));

const revealInfluence = assign((context, event) => R.pipe(
  R.over(playerLens(event.player), Player.revealRole(event.role)),
  R.assoc('revealedRole', event.role)
)(context));

const replaceInfluence = assign((context, event) => R.pipe(
  R.over(playerLens(context.revealer), Player.restoreRole(context.revealedRole)),
  redealPlayerRole(context.revealer, context.revealedRole)
)(context));

const logRet = fn => (...args) => {
  const ret = fn(...args);
  console.log(fn.name, ret);
  return ret;
}

const resetContext = assign({
  currentAction: null,
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
        ACTION: {target: 'StartAction', cond: assertCanStartAction}
      }
    },

    StartAction: {
      entry: setCurrentAction,
      always: [
        {target: 'WaitForChallenge', cond: ifChallengeableAction},
        {target: 'FinishAction'}
      ]
    },

    WaitForChallenge: {
      on: {
        CHALLENGE: {target: 'Challenge', cond: assertCanChallenge}
      }
    },

    Challenge: {
      entry: [
        setChallenger,
        setRevealer(context => context.whoseTurn)
      ],
      on: {
        REVEAL: {target: 'RevealOnChallenge', cond: assertCanReveal}
      }
    },

    RevealOnChallenge: {
      entry: revealInfluence,
      always: [
        {target: 'ChallengeIncorrect', cond: ifChallengeIncorrect},
        {target: 'EndOfTurn', cond: R.complement(ifChallengeIncorrect)}
      ]
    },

    ChallengeIncorrect: {
      entry: [
        replaceInfluence,
        setRevealer(context => context.challenger)
      ],
      on: {
        REVEAL: {target: 'RevealOnIncorrectChallenge', cond: assertCanReveal}
      }
    },

    RevealOnIncorrectChallenge: {
      entry: revealInfluence,
      always: 'FinishAction'
    },

    FinishAction: {
      entry: applyAction,
      always: 'EndOfTurn'
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

const stateEq = R.propEq('value');
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

const sampleGame = (seed0, context) => {
  const def = new GameDef();
  const [seed, deck] = Rand.shuffle(seed0, def.makeDeck());
  return R.mergeLeft(context, {def, seed, deck});
};

const testSeed = [426141121, 700962946, 3633913687, 2605998810];

const initialContext = sampleGame(testSeed, {
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
assertState(game2, 'WaitForChallenge');
assertContext(game2, [
  turnEq(1),
  actionEq('tax')
]);

const game3 = gameMachine.transition(game2, {type: 'CHALLENGE', player: 0});
assertState(game3, 'Challenge');
assertContext(game3, [
  turnEq(1),
  R.propEq('revealer', 1)
]);

const game4 = gameMachine.transition(game3, {type: 'REVEAL', role: 'assassin', player: 1});
assertState(game4, 'StartOfTurn');
assertContext(game4, [
  turnEq(0),
  playerHasCash(1, 2),
  R.complement(playerHasRole(1, 'assassin'))
]);

const game4a = gameMachine.transition(game3, {type: 'REVEAL', role: 'duke', player: 1});
assertState(game4a, 'ChallengeIncorrect');
assertContext(game4a, [
  turnEq(1),
  R.propEq('revealer', 0)
]);

const game4a_1 = gameMachine.transition(game4a, {type: 'REVEAL', role: 'duke', player: 0});
assertState(game4a_1, 'StartOfTurn');
assertContext(game4a_1, [
  turnEq(0),
  playerHasNInf(0, 1),
  R.complement(playerHasRole(0, 'duke')),
  playerHasNInf(1, 2),
  R.complement(playerHasRole(0, 'duke')),
  playerHasCash(1, 5)
]);
console.log('Pass');
