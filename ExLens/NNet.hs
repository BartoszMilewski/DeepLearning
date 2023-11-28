{-# language ScopedTypeVariables #-}
module NNet where
import ExLens

type D = Double
-- Ideally, a counted vector
type V = [D]

data Para = Para
  { weight :: V
  , bias   :: D
  } deriving Show

type ParaBlock = [Para]

-- Additive monoid

instance Semigroup D where
    (<>) = (+)

instance Monoid D where
    mempty = 0.0

instance Semigroup Para where
    (<>) :: Para -> Para -> Para
    p1 <> p2 = Para (zipWith (+) (weight p1) (weight p2)) (bias p1 + bias p2)

instance Monoid Para where
    mempty :: Para
    mempty = Para (repeat 0.0) 0.0

-- Vector space
class Monoid v => VSpace v where
    scale :: D -> v -> v

instance VSpace D where
    scale :: D -> D -> D
    scale a x = a * x

instance VSpace a => VSpace [a] where
    scale :: VSpace a => D -> [a] -> [a]
    scale a = fmap (scale a)

instance VSpace Para where
    scale :: D -> Para -> Para
    scale a p = Para (scale a (weight p)) (scale a (bias p))

linearL :: ExLens V V V V D D
linearL = ExLens fw bw
  where
    fw :: (V, V) -> ((V, V), D)
    -- a = Sum p * s
    fw (p, s) = ((s, p), sum $ zipWith (*) p s)
    -- da/dp = s, da/ds = p
    bw :: ((V, V), D) -> (V, V)
    bw ((s, p), da) = (scale da s  -- da/dp
                      ,scale da p) -- da/ds

biasL :: ExLens D D D D D D
biasL = ExLens fw bw 
  where 
    fw :: (D, D) -> ((), D)
    fw (p, s) = ((), p + s)
    -- da/dp = 1, da/ds = 1
    bw :: ((), D) -> (D, D)
    bw (_, da) = (da, da)

-- Non-linear activation lens using tanh
activ :: Lens D D D D
activ = Lens fw bw
  where
    -- a = tanh s
    fw s = (s, tanh s)
    -- da/ds = 1 + (tanh s)^2
    bw (s, da)= da * (1 - (tanh s)^2) -- a * da/ds

-- Neuron as a composite of linear, bias, and activation
neuron0 :: ExLens (V, D) (V, D) V V D D
neuron0 = composeR (compose linearL biasL) activ

-- Affine parametric lens 
-- (really a composition of linear and bias, but they are always used in combination)

affine :: Int -> ExLens Para Para V V D D
affine m = ExLens fw bw
  where
    fw :: (Para, V) -> ((V, V), D)
    -- a = b + w * s
    fw (p, s) = ((w, s), foldl (+) (bias p) (zipWith (*) w s))
      where w = weight p
    bw :: ((V, V), D) -> (Para, V)
    bw ((w, s), da) = ( Para (scale da s) da  -- (da/dw, da/db)
                      , scale da w) -- da/ds

-- Neuron with m inputs and one output and tanh activation
neuron :: Int -> ExLens Para Para V V D D
neuron m = composeR (affine m) activ

-- Initialize parameters for an affine lens from an infinite stream
initPara :: Int -> [D] -> (Para, [D])
initPara m stm = (Para w b, stm'')
  where
    (w, stm') = splitAt m stm
    ([b], stm'') = splitAt 1 stm'


layer :: Int -> Int -> ExLens [Para] [Para] V V V V
layer nOut mIn = composeL (branch nOut) (vecLens nOut (neuron mIn))

-- Initialize a block of nOut parameters, each for a neuron with mIn inputs
initParaBlock :: Int -> Int -> [D] -> ([Para], [D])
initParaBlock mIn nOut stm = unfoldl nOut (initPara mIn) stm



-- The loss lens, compares results with ground truth
loss :: V -> Lens V V D D
loss gTruth = Lens fw bw 
  where
    fw :: V -> (V, D)
    fw s = (s, delta s gTruth)
    bw :: (V, D) -> V
    -- da/ds = s - g
    bw (s, da) = map (da *) (zipWith (-) s gTruth)
    -- 1/2 Sum (s - g)^2
    delta s g = 0.5 * sum (map (^2) (zipWith (-) s g))

-- Helper function

unfoldl :: Int -> (s -> (a, s)) -> s -> ([a], s)
unfoldl 0 f s = ([], s)
unfoldl n f s = (x : xs, s'')
  where
    (x, s') = f s
    (xs, s'') = unfoldl (n-1) f s'

test2 :: IO ()
test2 = do
    let s = [0, 0.1 .. ]
    let (p, s') = initPara 2 s
    print p
    print $ fst $ unfoldl 3 (initPara 2) s'

test3 :: IO ()
test3 = do
  putStrLn "Compare different implementation of neurons"
  let s = [1, 0.5, 0, 0]
  let (p, s') = initPara 3 s
  let nrn = neuron 3
  let ins = [-1, 0, 1]
  putStrLn "Forward neurons"
  print $ fwd nrn (p, ins)
  putStrLn ""
  print $ fwd neuron0 ((weight p, bias p), ins)
  putStrLn "Backward neurons"
  print $ bwd nrn (p, ins, 1)
  putStrLn ""
  print $ bwd neuron0 ((weight p, bias p), ins, 1)

test4 :: IO ()
test4 = do
  putStrLn "Test backward passes"
  let p = Para [0.5, -0.5] 0.5
  let in1 = [1, 0]
  let in2 = [0, 1]
  let nrn = neuron 2
  print $ fwd nrn (p, in1)
  let (dp, ds) = bwd nrn (p, in1, 1)
  print dp
  print ds
  print $ fwd nrn (p, in2)
  let (dp, ds) = bwd nrn (p, in2, 1)
  print dp
  print ds
