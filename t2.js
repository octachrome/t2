const util = require('util');
const R = require('ramda');

///// Utilities

const raiseError = msg => { throw new Error(msg); };

///// State

const State = {
  START_OF_TURN: 'start-of-turn',
  ACTION_RESPONSE: 'action-response',
  CHALLENGE_RESPONSE: 'challenge-response',
  GAME_OVER: 'game-over',
};

State.getId = R.path(['state', 'id']);

State.eq = R.pathEq(['state', 'id']);

State.lens = R.lensProp('state');

Object.freeze(State);

///// Player

const activePlayerLens = (() => {
  // Game -> Player
  const getActivePlayer = game => game.players[game.whoseTurn];
  // Game -> Player -> Game
  const setActivePlayer = (player, game) => R.evolve({players: R.update(game.whoseTurn, player)}, game);

  return R.lens(getActivePlayer, setActivePlayer);
})();

const Player = {};

// Player -> Number
Player.countInf =  R.pipe(
    R.prop('influence'),
    R.reject(R.propEq('revealed', true)),
    R.length);

// Player -> Boolean
Player.hasOneInf = R.curry(R.pipe(Player.countInf, R.equals(1)));

// Player -> Boolean
Player.isDead = R.curry(R.pipe(Player.countInf, R.equals(0)));

// Number -> Player -> Player
Player.adjustCash = dcash => R.evolve({cash: R.add(dcash)});

Player.kill = R.evolve({'influence': R.map(R.assoc('revealed', true))});

Player.reveal = R.curry((role, player) => {
  const idx = R.findIndex(R.equals({role: role, revealed: false}), player.influence);
  if (idx == -1) raiseError(`Player does not have role ${role}`);
  return R.evolve({influence: R.adjust(idx, R.assoc('revealed', true))}, player);
});

Object.freeze(Player);

///// Game

const Game = {};

Game.isOver = R.pipe(
  R.prop('players'),
  R.reject(Player.isDead),
  R.length(),
  R.equals(1));

Game.checkOver = R.when(Game.isOver, R.set(State.lens, {id: State.GAME_OVER}));

Game.nextTurn = game => R.pipe(
  R.evolve({whoseTurn: turn => (turn + 1) % game.players.length}),
  R.set(State.lens, {id: State.START_OF_TURN})
) (game);

Game.opponents = game => R.pipe(
  R.prop('players'),
  R.addIndex (R.map) (R.pair),
  R.filter(pair => !Player.isDead(pair[0]) && pair[1] != game.whoseTurn),
  R.map(R.nth(1))
) (game);

Game.turnEq = R.propEq('whoseTurn');

Object.freeze(Game);

///// Action

const Action = {};

Action.income = R.always({action: 'income'});
Action.tax = R.always({action: 'tax'});
Action.challenge = challenger => ({action: 'challenge', challenger});
Action.allow = R.always({action: 'allow'});
Action.reveal = role => ({action: 'reveal', role});

Action.typeEq = R.curry((a, b) => a.action == b.action);

Action.listAvailable = R.cond([
  [State.eq(State.START_OF_TURN), game => [
    Action.tax(),
    Action.income(),
  ]],
  [State.eq(State.ACTION_RESPONSE), game => R.flatten([
    R.map(Action.challenge, Game.opponents(game)),
    Action.allow(),
  ])],
  [State.eq(State.CHALLENGE_RESPONSE), R.pipe(
    R.view(activePlayerLens),
    R.prop('influence'),
    R.map(R.prop('role')),
    R.map(Action.reveal)
  )],
  [R.T, game => raiseError(`Unknown state ${State.getId(game)}`)]
]);

const Executor = {};

Executor.assertAvailable = (action, game) => 
  R.contains(action, Action.listAvailable(game)) ||
  raiseError(`Action ${action.action} is not available in state ${State.getId(game)}`);

Executor.claimAction = action => R.set(State.lens, R.mergeLeft(action, {id: State.ACTION_RESPONSE}));

Executor.get = R.cond([
  [Action.typeEq(Action.tax()), action => (
    Executor.claimAction(Action.tax())
  )],
  [Action.typeEq(Action.income()), action => (
    R.pipe(
      R.over(activePlayerLens, Player.adjustCash(1)),
      Game.nextTurn
    )
  )],
  [Action.typeEq(Action.challenge()), action => (
    R.ifElse(
      R.pipe(R.view(activePlayerLens), Player.hasOneInf),
      R.pipe(R.over(activePlayerLens, Player.kill), Game.checkOver),
      R.over(State.lens, R.mergeLeft({id: State.CHALLENGE_RESPONSE, challenger: action.challenger}))
    )
  )],
  [Action.typeEq(Action.reveal()), action => (
    R.pipe(
      R.over(activePlayerLens, Player.reveal(action.role)),
      Game.checkOver,
      Game.nextTurn
      // todo: advance state
    )
  )],
  [R.T, action => raiseError(`Unknown action ${R.prop('action', action)}`)]
]);

Executor.play = (action, game) => {
  Executor.assertAvailable(action, game);
  return Executor.get (action) (game);
};

Object.freeze(Action);

const throws = fn => {
  try {
    fn();
    return false;
  } catch (ignored) {
    return true;
  }
};

const assert = (preds, obj) => R.allPass(R.flatten(preds), obj) || raiseError(`Assert failed on ${util.inspect(obj, false, null, true)}`);

const logPretty = obj => console.log(util.inspect(obj, false, null, true));

const game0 = {
  state: {
    id: State.START_OF_TURN
  },

  whoseTurn: 0,

  players: [
    {
      cash: 2,
      influence: [
        {role: 'duke', revealed: false},
        {role: 'captain', revealed: true}
      ]
    },
    {
      cash: 2,
      influence: [
        {role: 'assassin', revealed: false},
        {role: 'contessa', revealed: false}
      ]
    }
  ]
};

assert(throws, () => Executor.play(Action.reveal('assassin'), game0));
assert(throws, () => Executor.play(Action.challenge(0), game0));
assert(throws, () => Executor.play(Action.allow(), game0));

const game1 = Executor.play(Action.income(), game0);

assert(R.allPass([
  R.propEq('state', {id: State.START_OF_TURN}),
  Game.turnEq(1)
]), game1);

const game2 = Executor.play(Action.tax(), game1);

assert(R.allPass([
  R.propEq('state', {id: State.ACTION_RESPONSE, action: 'tax'}),
  Game.turnEq(1),
]), game2);

assert(throws, () => Executor.play(Action.income(), game2));
assert(throws, () => Executor.play(Action.reveal('assassin'), game2));
assert(throws, () => Executor.play(Action.challenge(1), game2));

const game3 = Executor.play(Action.challenge(0), game2);

assert(R.allPass([
  R.propEq('state', {id: State.CHALLENGE_RESPONSE, action: 'tax', challenger: 0}),
  Game.turnEq(1),
]), game3);

const game4 = Executor.play(Action.reveal('assassin'), game3);

assert(R.allPass([
  R.propEq('state', {id: State.START_OF_TURN}),
  Game.turnEq(0),
]), game4);

console.log('Passed');
