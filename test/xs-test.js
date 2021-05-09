const util = require('util');
const R = require('ramda');
const { Rand, GameDef, Game, Player, GameMachine } = require('../xs');

const inspectState = state => util.inspect(R.pick(['value', 'changed', 'context'], state), false, null, true);

const logState = state => console.log(inspectState(state));

const assertContext = (state, preds) => {
  if (!R.allPass(R.flatten([preds]))(state.context)) {
    throw new Error(`Failed to assert context on ${inspectState(state)}`);
  }
};

const assertState = (state, id) => {
  if (state.value !== id) {
    throw new Error(`Expected state ${id} but was ${inspectState(state)}`);
  }
};

assertThrows = fn => {
  let threw = false;
  try {
    fn();
  } catch (ignored) {
    threw = true;
  }
  if (!threw) {
    throw new Error('Expected an exception to be thrown');
  }
};

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

const sampleGame = (seed, context) => {
  const def = new GameDef();
  const deck = def.makeDeck();
  return Game.shuffleDeck_s().execWith(R.mergeLeft(context, { def, seed, deck }))
};

describe('State machine', () => {
  describe('with two influences', () => {
    let game0;

    beforeEach(() => {
      const initialContext = sampleGame(Rand.makeSeed(123), {
        whoseTurn: 0,

        players: [
          {
            cash: 2,
            influence: [
              { role: 'duke', revealed: false },
              { role: 'captain', revealed: false }
            ]
          },
          {
            cash: 2,
            influence: [
              { role: 'assassin', revealed: false },
              { role: 'duke', revealed: false }
            ]
          }
        ]
      });

      game0 = GameMachine.withContext(initialContext).initialState;
    });

    it('can draw income', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'income', player: 0 });
      assertState(game1, 'StartOfTurn');
      assertContext(game1, [
        turnEq(1),
        actionEq(null),
        Game.playerHasCash(0, 3),
        Game.playerHasCash(1, 2)
      ]);
    });

    it('can draw tax', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'tax', player: 0 });
      assertState(game1, 'WaitForResponse');
      assertContext(game1, [
        turnEq(0),
        actionEq('tax')
      ]);

      const game2 = GameMachine.transition(game1, { type: 'ALLOW', player: 1 });
      assertState(game2, 'StartOfTurn');
      assertContext(game2, [
        turnEq(1),
        Game.playerHasCash(0, 5)
      ]);
    });

    it('can correctly challenge tax', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'tax', player: 0 });
      assertState(game1, 'WaitForResponse');
      assertContext(game1, [
        turnEq(0),
        actionEq('tax')
      ]);

      const game2 = GameMachine.transition(game1, { type: 'CHALLENGE', player: 1 });
      assertState(game2, 'Challenge');
      assertContext(game2, [
        turnEq(0),
        R.propEq('revealer', 0)
      ]);

      // Lose the challenge by revealing a role which is not duke
      const game3 = GameMachine.transition(game2, { type: 'REVEAL', role: 'captain', player: 0 });
      assertState(game3, 'StartOfTurn');
      assertContext(game3, [
        turnEq(1),
        Game.playerHasNInf(0, 1),        // Player lost an influence
        Game.playerHasCash(0, 2),        // Player did not draw tax
        R.complement(Game.playerHasRole(1, 'captain'))
      ]);
    });

    it('can incorrectly challenge tax', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'tax', player: 0 });
      assertState(game1, 'WaitForResponse');
      assertContext(game1, [
        turnEq(0),
        actionEq('tax')
      ]);

      const game2 = GameMachine.transition(game1, { type: 'CHALLENGE', player: 1 });
      assertState(game2, 'Challenge');
      assertContext(game2, [
        turnEq(0),
        R.propEq('revealer', 0)
      ]);

      // Win the challenge by revealing a duke
      const game3 = GameMachine.transition(game2, { type: 'REVEAL', role: 'duke', player: 0 });
      assertState(game3, 'ChallengeIncorrect');
      assertContext(game3, [
        turnEq(0),
        R.propEq('revealer', 1),
        Game.playerHasNInf(0, 2),                      // Player replaced their duke with a new role from the deck
        R.complement(Game.playerHasRole(0, 'duke')),
      ]);
      if (deckHash(game3) === deckHash(game2)) throw new Error("Expected deck to be shuffled");

      // Now the challenger must reveal
      const game4 = GameMachine.transition(game3, { type: 'REVEAL', role: 'duke', player: 1 });
      assertState(game4, 'StartOfTurn');
      assertContext(game4, [
        turnEq(1),
        Game.playerHasNInf(1, 1),
        R.complement(Game.playerHasRole(1, 'duke')),   // Challenger lost their duke
        Game.playerHasCash(0, 5)                       // Player drew tax
      ]);
    });

    it('can block foreign aid', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'foreign-aid', player: 0 });
      assertState(game1, 'WaitForResponse');
      assertContext(game1, [
        turnEq(0),
        actionEq('foreign-aid')
      ]);

      // Block foreign aid with duke
      const game2 = GameMachine.transition(game1, { type: 'BLOCK', role: 'duke', player: 1 });
      assertState(game2, 'Block');
      assertContext(game2, [
        turnEq(0),
        actionEq('foreign-aid')
      ]);

      // Allow the block
      const game6 = GameMachine.transition(game2, { type: 'ALLOW', player: 0 });
      assertState(game6, 'StartOfTurn');
      assertContext(game6, [
        turnEq(1),
        Game.playerHasCash(0, 2)   // Foreign aid was blocked
      ]);
    });

    it('can incorrectly challenge a foreign aid block', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'foreign-aid', player: 0 });
      assertState(game1, 'WaitForResponse');
      assertContext(game1, [
        turnEq(0),
        actionEq('foreign-aid')
      ]);

      // Block foreign aid with duke
      const game2 = GameMachine.transition(game1, { type: 'BLOCK', role: 'duke', player: 1 });
      assertState(game2, 'Block');
      assertContext(game2, [
        turnEq(0),
        actionEq('foreign-aid')
      ]);

      // Challenge the block
      const game3 = GameMachine.transition(game2, { type: 'CHALLENGE', player: 0 });
      assertState(game3, 'Challenge');
      assertContext(game3, [
        turnEq(0),
        R.propEq('revealer', 1),
      ]);

      // Win the challenge by revealing a duke, blocking foreign aid
      const game4 = GameMachine.transition(game3, { type: 'REVEAL', role: 'duke', player: 1 });
      assertState(game4, 'ChallengeIncorrect');
      assertContext(game4, [
        turnEq(0),
        R.propEq('revealer', 0),
        Game.playerHasNInf(1, 2),                      // Player replaced their duke with a new role from the deck
        R.complement(Game.playerHasRole(1, 'duke')),
      ]);
      if (deckHash(game4) === deckHash(game3)) throw new Error("Expected deck to be shuffled");

      // Now the challenger must reveal
      const game5 = GameMachine.transition(game4, { type: 'REVEAL', role: 'duke', player: 0 });
      assertState(game5, 'StartOfTurn');
      assertContext(game5, [
        turnEq(1),
        Game.playerHasNInf(0, 1),                      // Player lost their duke
        Game.playerHasCash(0, 2)                       // Player did not draw foreign aid
      ]);
    });

    it('can correctly challenge a foreign aid block', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'foreign-aid', player: 0 });
      assertState(game1, 'WaitForResponse');
      assertContext(game1, [
        turnEq(0),
        actionEq('foreign-aid')
      ]);

      // Block foreign aid with duke
      const game2 = GameMachine.transition(game1, { type: 'BLOCK', role: 'duke', player: 1 });
      assertState(game2, 'Block');
      assertContext(game2, [
        turnEq(0),
        actionEq('foreign-aid')
      ]);

      // Challenge the block
      const game3 = GameMachine.transition(game2, { type: 'CHALLENGE', player: 0 });
      assertState(game3, 'Challenge');
      assertContext(game3, [
        turnEq(0),
        R.propEq('revealer', 1),
      ]);

      // Lose the challenge by revealing a role other than duke
      const game4 = GameMachine.transition(game3, { type: 'REVEAL', role: 'assassin', player: 1 });
      assertState(game4, 'StartOfTurn');
      assertContext(game4, [
        turnEq(1),
        Game.playerHasNInf(1, 1),                      // Challenger lost their assassin
        R.complement(Game.playerHasRole(1, 'assassin')),
        Game.playerHasCash(0, 4)                       // Player drew foreign aid
      ]);
    });

    it('cannot assassinate if not enough cash', () => {
      assertThrows(() => GameMachine.transition(game0, { type: 'ACTION', action: 'assassinate', player: 0, target: 1 }));
    });

    describe('assassinate', () => {
      let game3;

      beforeEach(() => {
        // Get some cash
        const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'income', player: 0 });
        const game2 = GameMachine.transition(game1, { type: 'ACTION', action: 'income', player: 1 });
        game3 = GameMachine.transition(game2, { type: 'ACTION', action: 'income', player: 0 });
      });

      it('can assassinate', () => {
        const game4 = GameMachine.transition(game3, { type: 'ACTION', action: 'assassinate', player: 1, target: 0 });
        assertState(game4, 'WaitForResponse');
        assertContext(game4, [
          Game.playerHasCash(1, 3)
        ]);

        // Allow the assassination
        const game5 = GameMachine.transition(game4, { type: 'ALLOW', player: 0 });
        assertState(game5, 'RevealOnAction');
        assertContext(game5, [
          Game.playerHasCash(1, 0)
        ]);

        const game6 = GameMachine.transition(game5, { type: 'REVEAL', role: 'captain', player: 0 });
        assertState(game6, 'StartOfTurn');
        assertContext(game6, [
          turnEq(0),
          Game.playerHasNInf(0, 1),
          R.complement(Game.playerHasRole(0, 'captain'))
        ]);
      });

      it('can lose by being correctly challenged on a contessa block', () => {
        const game4 = GameMachine.transition(game3, { type: 'ACTION', action: 'assassinate', player: 1, target: 0 });
        assertState(game4, 'WaitForResponse');

        // Block the assassination
        assertThrows(() => GameMachine.transition(game4, { type: 'BLOCK', role: 'duke', player: 0 }));
        const game5 = GameMachine.transition(game4, { type: 'BLOCK', role: 'contessa', player: 0 });
        assertState(game5, 'Block');
        assertContext(game5, [
          Game.playerHasCash(1, 0)
        ]);

        // Challenge the block
        const game6 = GameMachine.transition(game5, { type: 'CHALLENGE', player: 1 });
        assertState(game6, 'Challenge');

        const game7 = GameMachine.transition(game6, { type: 'REVEAL', role: 'captain', player: 0 });
        assertState(game7, 'GameOver');
      });

      it('no payment for correctly challenged assassination', () => {
        const game4 = GameMachine.transition(game3, { type: 'ACTION', action: 'assassinate', player: 1, target: 0 });
        assertState(game4, 'WaitForResponse');

        const game5 = GameMachine.transition(game4, { type: 'CHALLENGE', player: 0 });
        assertState(game5, 'Challenge');
        assertContext(game5, [
          Game.playerHasCash(1, 3)
        ]);

        const game6 = GameMachine.transition(game5, { type: 'REVEAL', role: 'duke', player: 1 });
        assertState(game6, 'StartOfTurn');
        assertContext(game6, [
          turnEq(0),
          Game.playerHasNInf(1, 1),
          R.complement(Game.playerHasRole(1, 'duke')),
          Game.playerHasCash(1, 3)
        ]);
      });

      it('last chance to block after incorrectly challenging an assassination', () => {
        const game4 = GameMachine.transition(game3, { type: 'ACTION', action: 'assassinate', player: 1, target: 0 });
        assertState(game4, 'WaitForResponse');

        // Lose an influence by incorrectly challenging
        const game5 = GameMachine.transition(game4, { type: 'CHALLENGE', player: 0 });
        assertState(game5, 'Challenge');

        const game6 = GameMachine.transition(game5, { type: 'REVEAL', role: 'assassin', player: 1 });
        assertState(game6, 'ChallengeIncorrect');

        const game7 = GameMachine.transition(game6, { type: 'REVEAL', role: 'captain', player: 0 });
        assertState(game7, 'WaitForBlock');
        assertContext(game7, [
          Game.playerHasCash(1, 0)
        ]);

        const game8 = GameMachine.transition(game7, { type: 'BLOCK', role: 'contessa', player: 0 });
        assertState(game8, 'Block');
      });
    });
  });

  describe('with only one influence', () => {
    let game0;

    beforeEach(() => {
      const initialContext = sampleGame(Rand.makeSeed(123), {
        whoseTurn: 1,

        players: [
          {
            cash: 2,
            influence: [
              { role: 'duke', revealed: true },
              { role: 'contessa', revealed: false }
            ]
          },
          {
            cash: 3,
            influence: [
              { role: 'captain', revealed: true },
              { role: 'duke', revealed: false }
            ]
          }
        ]
      });

      game0 = GameMachine.withContext(initialContext).initialState;
    });

    it('can lose by being correctly challenged', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'assassinate', target: 0, player: 1 });
      assertState(game1, 'WaitForResponse');

      const game2 = GameMachine.transition(game1, { type: 'CHALLENGE', player: 0 });
      assertState(game2, 'GameOver');
      assertContext(game2, [
        Game.playerHasNInf(0, 1),
        Game.playerHasNInf(1, 0)
      ]);
  });

    it('can lose by incorrectly challenging an action', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'tax', player: 1 });
      assertState(game1, 'WaitForResponse');

      const game2 = GameMachine.transition(game1, { type: 'CHALLENGE', player: 0 });
      assertState(game2, 'GameOver');
      assertContext(game2, [
        Game.playerHasNInf(0, 0),
        Game.playerHasNInf(1, 1)
      ]);
    });

    it('can lose by incorrectly challenging a block', () => {
      const game1 = GameMachine.transition(game0, { type: 'ACTION', action: 'assassinate', target: 0, player: 1 });
      assertState(game1, 'WaitForResponse');

      const game2 = GameMachine.transition(game1, { type: 'BLOCK', role: 'contessa', player: 0 });
      assertState(game2, 'Block');

      const game3 = GameMachine.transition(game2, { type: 'CHALLENGE', player: 1 });
      assertState(game3, 'GameOver');
      assertContext(game3, [
        Game.playerHasNInf(0, 1),
        Game.playerHasNInf(1, 0)
      ]);
    });
  });
});
