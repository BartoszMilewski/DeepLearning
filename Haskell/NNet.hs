{-# language ScopedTypeVariables #-}
module NNet where
import PLens

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
    scale s = fmap (scale s)

instance VSpace Para where
    scale :: D -> Para -> Para
    scale a p = Para (scale a (weight p)) (scale a (bias p))

-- Non-linear ctivation lens using tanh
activ :: Lens D D D D
activ = Lens tanh
            (\(s, a) -> a * (1 - (tanh s)^2)) -- a * da/ds


-- Affine parametric lens 
-- (really a composition of linear and bias, but they are always used in combination)

affine :: Int -> PLens Para Para V V D D
affine m = PLens fw bw
  where
    fw :: (Para, V) -> D
    -- a = b + w * s
    fw (p, s) = foldl (+) (bias p) (zipWith (*) (weight p) s)
    bw :: (Para, V, D) -> (Para, V)
    bw (p, s, a) = ( Para (map (a*) s) a  -- (da/dw, da/db)
                   , map (a*) (weight p)) -- da/ds

-- Initialize parameters for an affine lens from an infinite stream
initPara :: Int -> [D] -> (Para, [D])
initPara m stm = (Para w b, stm'')
  where
    (w, stm') = splitAt m stm
    ([b], stm'') = splitAt 1 stm'

-- Neuron with m inputs and one output
neuron :: Int -> PLens Para Para V V D D
neuron m = composeR (affine m) activ

layer :: Int -> Int -> PLens [Para] [Para] V V V V
layer nOut mIn = composeL (branch nOut) (vecLens nOut (neuron mIn))

-- Initialize a block of nOut parameters, each for a neuron with mIn inputs
initParaBlock :: Int -> Int -> [D] -> ([Para], [D])
initParaBlock mIn nOut stm = unfoldl nOut (initPara mIn) stm

-- The loss lens, compares results with ground truth
loss :: V -> Lens V V D D
loss gTruth = Lens fw bw 
  where
    fw :: V -> D
    fw s = delta s gTruth
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
    let s = [1 .. ]
    let (p, s') = initPara 2 s
    print p
    print $ fst $ unfoldl 3 (initPara 2) s'
