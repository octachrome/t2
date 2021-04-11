// Functor
//  map   <$>   (fmap, functor map)
// Applicative:
//  of    pure
//  ap    <*>   (map with a wrapped function: needed for functions with >1 arg)
// Monad:
//  of    return
//  chain >>=   (flatMap aka bind, maps then flattens (aka joins) the resulting nested monads)
//              http://www.tomharding.me/2017/05/15/fantas-eel-and-specification-13/
//              ma.chain(f) means take ma (monad containing a), unwrap it to get a, pass it to function f,
//              which returns mb (monad containing b), wrap that back up into mmb (now double wrapped),
//              then flatten out the result to get mb

// lift2(f, a, b) is just b.ap(a.map(f))
// https://stackoverflow.com/questions/7746894/are-there-pronounceable-names-for-common-haskell-operators

// A state monad does not contain a value, it contains a function representing a stateful computation: s -> (a, s)

// instance Monad (State s) where
//     return x = State $ \s -> (x,s)                               ! Preserves the state and returns the plain value.
//                                                                  ! Here f is a kind of augmented computation: it accepts
//                                                                  ! a parameter AND a state, and returns a result and a state.
//                                                                  ! AKA a function which accepts a parameter and returns a computation!
//                                                                  ! >>= creates a new computation c out of a computation h and the function f.
//     (State h) >>= f = State $ \s -> let (a, newState) = h s      ! Applies the first computation (h) to whatever state will be passed to c.
//                                         (State g) = f a          ! Partially applies f to the result of h, which gives a new computation.
//                                     in  g newState

// https://en.wikibooks.org/wiki/Haskell/Understanding_monads/State

const R = require('ramda');
const pureRandom = require('pure-random');
const {State, Pair} = require('crocks');
const daggy = require('daggy');
const fst = require('crocks/Pair/fst');
const snd = require('crocks/Pair/snd');

const UINT32_MAX = Math.pow(2, 32) - 1;
const PRIMES = [160481183, 179424673, 198491317, 217645177];

const nextGen = gen => R.append(pureRandom.randUint(gen), R.slice(1, 4, gen));
const mkStdGen = (seed, n) => seed ? R.reduceRight(R.compose, R.identity, R.repeat(nextGen, n || 10))(PRIMES.map(p => p * seed)) : pureRandom.genSeed();
const random = (seed, min, max) => Math.round(min + pureRandom.randUint(seed) / UINT32_MAX * (max - min));

const foldM = (f, a, list) => {
    const foldMonadicAcc = (f, ma, list) => list.length == 0 ? ma : ma.chain(a => foldMonadicAcc(f, f(a, list[0]), R.remove(0, 1, list)));
    return foldMonadicAcc(f, State.of(a), list);
};

const mapM = (f, list) => list.length == 0 ? State.of([]) :
    f(list[0]).chain(head =>
        mapM(f, R.remove(0, 1, list)).chain(tail =>
            State.of(R.insert(0, head, tail))));

const randomS = (min, max) => State(s => Pair(random(s, min, max), nextGen(s)));

const rollPairS = () => randomS(1, 6).chain(r1 =>
    randomS(1, 6).map(r2 => [r1, r2]));

// console.log(rollPairS().runWith(mkStdGen(3)));

// const push = a => State(s => Pair(null, R.prepend(a, s)));
// const pop = () => State(s => Pair(s[0], R.remove(0, 1, s)));
// const add = () => pop().chain(a => pop().map(b => a + b));
// const op = push(1).chain(() => push(2)).chain(() => add());
// console.log(op.runWith([]));

const addM = (a, b) => State.of(a + b);
const op2 = foldM(addM, 0, [1, 2, 3]);
// console.log(op2.runWith("dummy"));

const rollNM = n => () => mapM(_ => randomS(1, 6), R.range(0, n));
const roll6M = rollNM(6);
// console.log(roll6M().runWith(mkStdGen(1)));

const add2M = R.lift((a, b) => a + b);
// console.log(add2M(State.of(2), State.of(5)).runWith('dummy'));


const TurnState = daggy.taggedSum('TurnState', {
    Locked: [],
    Unlocked: []
});

const TurnIn = daggy.taggedSum('TurnIn', {
    Coin: [],
    Push: []
});

const TurnOut = daggy.taggedSum('TurnOut', {
    Thank: [],
    Open: [],
    Tut: []
});

const coin = () => Pair(TurnOut.Thank, TurnState.Unlocked);

const push = ts => ts.cata({
    Unlocked: () => Pair(TurnOut.Open, TurnState.Locked),
    Locked: () => Pair(TurnOut.Tut, TurnState.Locked)
});

//const coinS = State(coin);
const pushS = State(push);
const coinS = State.put(TurnState.Unlocked).map(() => TurnOut.Thank);

const monday = s0 => {
  let [a1, s1] = coin(s0).toArray(),
      [a2, s2] = push(s1).toArray(),
      [a3, s3] = push(s2).toArray(),
      [a4, s4] = coin(s3).toArray(),
      [a5, s5] = push(s4).toArray();
  return Pair([a1, a2, a3, a4, a5], s5);
};

// console.log(monday(TurnState.Locked));

const mondayS = 
    coinS.chain(a1 =>
    pushS.chain(a2 =>
    pushS.chain(a3 =>
    coinS.chain(a4 =>
    pushS.map(a5 => [a1, a2, a3, a4, a5])))));

// console.log(mondayS.runWith(TurnState.Locked));

const turnS = inp => inp.cata({
    Coin: () => State(() => Pair(TurnOut.Thank, TurnState.Unlocked)),
    Push: () => State(s => s.cata({
        Unlocked: () => Pair(TurnOut.Open, TurnState.Locked),
        Locked: () => Pair(TurnOut.Tut, TurnState.Locked)
    }))
});

// console.log(mapM(turnS, [TurnIn.Coin, TurnIn.Push, TurnIn.Push, TurnIn.Coin, TurnIn.Push]).runWith(TurnState.Locked));

const randomInputS = randomS(0, 1).map(b => b ? TurnIn.Coin : TurnIn.Push);

// console.log(mapM(_ => randomInputS, R.range(0, 4)).runWith(mkStdGen(51)));

// randomTurnS :: State (StdGen, TurnstileState) TurnstileOutput
randomTurnS = State.get().chain(s0 => {
    const [sg0, ts0] = s0.toArray();
    const [inp, sg1] = randomInputS.runWith(sg0).toArray();
    const [out, ts1] = turnS(inp).runWith(ts0).toArray();
    return State.put(Pair(sg1, ts1)).map(() => out);
});

console.log(mapM(_ => randomTurnS, R.range(0, 6)).runWith(Pair(mkStdGen(51), TurnState.Locked)));

const processingFst = m => State.get().chain(s0 => {
    const [res, s1] = m.runWith(s0.fst()).toArray();
    return State.put(Pair(s1, s0.snd())).map(() => res);
});

const processingSnd = m => State.get().chain(s0 => {
    const [res, s1] = m.runWith(s0.snd()).toArray();
    return State.put(Pair(s0.fst(), s1)).map(() => res);
});

randomTurnS2 = processingFst(randomInputS).chain(inp =>
    processingSnd(turnS(inp)));
console.log(mapM(_ => randomTurnS2, R.range(0, 6)).runWith(Pair(mkStdGen(51), TurnState.Locked)));

fstL = R.lens(fst, (value, pair) => pair.bimap(R.always(value), R.identity));
sndL = R.lens(snd, (value, pair) => pair.bimap(R.identity, R.always(value)));

const processing = (lens, m) => State.get().chain(s0 => {
    const [res, s1] = m.runWith(R.view(lens, s0)).toArray();
    return State.put(R.set(lens, s1, s0)).map(() => res);
});

randomTurnS3 = processing(fstL, randomInputS).chain(inp =>
    processing(sndL, turnS(inp)));
console.log(mapM(_ => randomTurnS3, R.range(0, 6)).runWith(Pair(mkStdGen(51), TurnState.Locked)));
