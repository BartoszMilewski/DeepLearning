module NNet where
import PreLens
import Data.Bifunctor ( Bifunctor(second, first, bimap) )

-- Use existential lenses to create more complex neural networks

type D = Double
-- Ideally, a counted vector
type V = [D]

-- Parameters for a single neuron
data Para = Para
  {
    bias   :: D
  , weight :: V
  } deriving Show

mkPara :: (D, V) -> Para
mkPara (b, v) = Para b v

unPara :: Para -> (D, V)
unPara p = (bias p, weight p)

-- Parameters for a layer of neurons
type ParaBlock = [Para]

-- Additive monoid

instance Semigroup D where
    (<>) = (+)

instance Monoid D where
    mempty = 0.0

instance Semigroup Para where
    (<>) :: Para -> Para -> Para
    p1 <> p2 = Para (bias p1 + bias p2) (zipWith (+) (weight p1) (weight p2))

instance Monoid Para where
    mempty :: Para
    mempty = Para 0.0 (repeat 0.0)

-- Parameters form a vector space, we need to scale them and add them

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
    scale a p = Para (scale a (bias p)) (scale a (weight p))

sumN :: Int -> V -> D
sumN 0 _ = 0
sumN n (a : as) = a + sumN (n - 1) as

-- Simple linear lens, scalar product of parameters and inputs
linearL :: Int -> PreLens D D (V, V) (V, V) V V V V
linearL n = PreLens fw bw
  where
    fw :: (V, V) -> ((V, V), D)
    -- a = Sum p * s
    fw (p, s) = ((s, p), sumN n $ zipWith (*) p s)
    -- da/dp = s, da/ds = p
    bw :: ((V, V), D) -> (V, V)
    bw ((s, p), da) = (fmap (da *) s  -- da/dp
                      ,fmap (da *) p) -- da/ds

-- Add bias to input
biasL :: PreLens D D () () D D D D
biasL = PreLens fw bw 
  where 
    fw :: (D, D) -> ((), D)
    fw (p, s) = ((), p + s)
    -- da/dp = 1, da/ds = 1
    bw :: ((), D) -> (D, D)
    bw (_, da) = (da, da)

-- Non-linear activation lens using tanh
activL :: PreLens D D D D () () D D
activL = PreLens fw bw
  where
    -- a = tanh s
    fw (_, s) = (s, tanh s)
    -- da/ds = 1 + (tanh s)^2
    bw (s, da)= ((), da * (1 - (tanh s)^2)) -- a * da/ds

neuronL :: Int -> PreLens D D ((V, V), D) ((V, V), D) Para Para V V
neuronL mIn = PreLens f' b'
  where 
    PreLens f b = preCompose (preCompose (linearL mIn) biasL) activL
    f' :: (Para, V) -> (((V, V), D), D)
    f' (Para bi wt, s) = let (((vv, ()), d), a) = f (((), (bi, wt)), s)
                         in ((vv, d), a)
    b' :: (((V, V), D), D) -> (Para, V)
    b' ((vv, d), da) = let (((), (d', w')), ds) = b (((vv, ()), d), da)
                          in (Para d' w', ds)

-- Convert to TriLens
-- m1 p1 D -> ((V, V), m1) (p1, (V, V)) V
linearT :: Int -> TriLens D D (V, V) (V, V) V V V V
linearT n = toTamb (linearL n)

-- m1 p1 D -> ((), m1) (p1, ()) D
biasT :: TriLens D D () () D D D D
biasT = toTamb biasL

affineT :: Int -> TriLens D D (V, V) (V, V) (D, V) (D, V) V V
affineT n = 
  dimapM (first runit) (first unRunit) .
  triCompose (linearT n) biasT

activT :: TriLens D D D D () () D D
activT = toTamb activL

neuronT :: Int -> TriLens D D ((V, V), D) ((V, V), D) Para Para V V
-- m1 p1 D -> (((V, V), D), m1) (p1, Para) V
neuronT mIn = 
  dimapP (second (unLunit . unPara)) (second (mkPara . lunit)) .
  triCompose (affineT mIn) activT

-- Initialize parameters for an affine lens from an infinite stream
initPara :: Int -> [D] -> (Para, [D])
initPara m stm = (Para b w, stm'')
  where
    (w, stm') = splitAt m stm
    ([b], stm'') = splitAt 1 stm'


-- A layer of nOut identical neurons, each with mIn inputs
-- V [((V, V), D)] [Para] V
layer :: Int -> Int -> TriLens V V [((V, V), D)] [((V, V), D)] [Para] [Para] V V
layer nOut mIn = 
  dimapP (second unRunit) (second runit) .
  dimapM (first lunit) (first unLunit) .
  triCompose (branch nOut) (vecLens nOut (neuronT mIn)) -- m1 p1 V -> (m1, ((), [((V, V), D)])) (([Para], ()), p1) V


-- Initialize a block of nOut parameters, each for a neuron with mIn inputs
initParaBlock :: Int -> Int -> [D] -> ([Para], [D])
initParaBlock mIn nOut stm = unfoldl nOut (initPara mIn) stm

-- Helper function

unfoldl :: Int -> (s -> (a, s)) -> s -> ([a], s)
unfoldl 0 f s = ([], s)
unfoldl n f s = (x : xs, s'')
  where
    (x, s') = f s
    (xs, s'') = unfoldl (n-1) f s'


-- The loss lens, compares results with ground truth
lossL :: PreLens D D (V, V) (V, V) V V V V
lossL = PreLens fw bw 
  where
    fw :: (V, V) -> ((V, V), D)
    fw (gTruth, s) = ((gTruth, s), delta)
      where
        -- 1/2 Sum (s - g)^2
        delta = 0.5 * sum (map (^2) (zipWith (-) s gTruth))
    bw :: ((V, V), D) -> (V, V)
    bw ((gTruth, s), da) = (fmap negate delta', delta')
      -- da/ds = s - g
      -- da/dg = g - s
      where
        delta' = map (da *) (zipWith (-) s gTruth)

lossT :: TriLens D D (V, V) (V, V) V V V V
lossT = toTamb lossL

-- fwd :: TriLens a da m dm p dp s ds -> (p, s) -> a
-- fwd l = let PreLens f b = fromTamb l 
--         in snd . f
-- bwd :: TriLens a da m dm p dp s ds -> (p, s, da) -> (dp, ds)
-- bwd l  (p, s, da) = 
--   let (PreLens f b) = fromTamb l 
--   in b (fst (f (p, s)), da)

-- affineT :: Int -> TriLens D D (V, V) (V, V) (D, V) (D, V) V V
testTriTamb :: IO ()
testTriTamb = do
    putStrLn "forward"
    print $ fwd (affineT 2) ((0.01, [-0.1, 0.1]), [2, 30])
    putStrLn "backward"
    print $ bwd (affineT 2) ((0.1, [1.3, -1.4]), [0.21, 0.33], 1)

    putStrLn "forward neuron"
    print $ fwd (neuronT 2) (Para 0.01 [-0.1, 0.1], [2, 30])
    putStrLn "backward neuron"
    print $ bwd (neuronT 2) (Para 0.1 [1.3, -1.4], [0.21, 0.33], 1)

test2 :: IO ()
test2 = do
    let s = [0, 0.1 .. ]
    let (p, s') = initPara 2 s
    print p
    print $ fst $ unfoldl 3 (initPara 2) s'

nrn3 :: TriLens D D ((V, V), D) ((V, V), D) Para Para V V
nrn3  = neuronT 3

test3 :: IO ()
test3 = do
  putStrLn "Compare different implementation of neurons"
  let s = [1, 0.5, 0, 0]
  let (p, s') = initPara 3 s
  let ins = [-1, 0, 1]
  putStrLn "Forward neurons"
  print $ fwd nrn3 (p, ins)
  putStrLn ""
  let neuron0 = ExLens (neuronL 3)
  print $ fwd' neuron0 (p, ins)
  putStrLn "Backward neurons"
  print $ bwd nrn3 (p, ins, 1)
  putStrLn ""
  print $ bwd' neuron0 (p, ins, 1)


nrn2 :: TriLens D D ((V, V), D) ((V, V), D) Para Para V V
nrn2  = neuronT 2


test4 :: IO ()
test4 = do
  putStrLn "Test backward passes"
  let p = Para 0.5 [0.5, -0.5]
  let in1 = [1, 0]
  let in2 = [0, 1]
  print $ fwd nrn2 (p, in1)
  let (dp, ds) = bwd nrn2 (p, in1, 1)
  print dp
  print ds
  print $ fwd nrn2 (p, in2)
  let (dp, ds) = bwd nrn2 (p, in2, 1)
  print dp
  print ds


test5 :: IO () 
test5 = do
    putStrLn "forward"
    print $ fwd (affineT 2) ((0.1, [-1, 1]), [2, 30])
    putStrLn $ show $ (-2) + 30 + 0.1
    putStrLn "backward"
    print $ bwd (affineT 2) ((0.1, [1.3, -1.4]), [21, 33], 1)
    -- y = q1 * x1 + q2 * x2 + d
    -- dy/dq = (x1, x2), dy/dd = 1, dy/dx = (q1, q2)
    putStrLn $ show $ (Para 1 [21, 33], [1.3, -1.4])
