module Params where
type D = Double
-- Ideally, a counted vector
type V = [D]

-- Parameters for a single neuron
data Para = Para
  { bias   :: D
  , weight :: V
  } deriving Show

mkPara :: (D, V) -> Para
mkPara (b, v) = Para b v

unPara :: Para -> (D, V)
unPara p = (bias p, weight p)

-- Parameters for a layer of neurons
type ParaBlock = [Para]

-- Parameters form a vector space, we need to scale them and add them

class VSpace v where
  (<+>) :: v -> v -> v
  scale :: D -> v -> v
  vzero :: v

instance VSpace D where
  (<+>) :: D -> D -> D
  (<+>) = (+)
  scale :: D -> D -> D
  scale a x = a * x
  vzero :: D
  vzero = 0.0

instance VSpace a => VSpace [a] where
  (<+>) :: VSpace a => [a] -> [a] -> [a]
  (<+>) = zipWith (<+>)
  scale :: VSpace a => D -> [a] -> [a]
  scale a = fmap (scale a)
  vzero :: VSpace a => [a]
  vzero = repeat vzero

instance VSpace Para where
  (<+>) :: Para -> Para -> Para
  p1 <+> p2 = Para (bias p1 + bias p2) (zipWith (+) (weight p1) (weight p2))
  scale :: D -> Para -> Para
  scale a p = Para (scale a (bias p)) (scale a (weight p))
  vzero :: Para
  vzero = Para 0.0 (repeat 0.0)

sumN :: Int -> V -> D
sumN 0 _ = 0
sumN n [] = error $ "sumN " ++ show n
sumN n (a : as) = a + sumN (n - 1) as

accumulate :: VSpace v => [v] -> v
accumulate = foldr (<+>) vzero 