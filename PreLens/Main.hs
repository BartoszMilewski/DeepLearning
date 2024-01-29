module Main where
import Tambara
import TriLens
import NNet
import Perceptron
import Params
import Data.Int (Int32)
import Data.Bits (shiftR)
import Data.List
import Control.Monad

-- Home-made random number generator, in case no Random library available

random :: Int32 -> [Int32]
random seed = let seed' = 1664525 * seed + 1013904333
              in (seed' `shiftR` 2) : random seed'

rands :: [Double]
rands = map normalize (random 42)
  where
    normalize :: Int32 -> Double
    normalize n = fromIntegral n / 2147483647

testLayer :: IO ()
testLayer = do
    let (paras, _) = initParaBlock 3 2 rands
    print $ fwd lyr (paras, [2, 3, -1])
    putStrLn "Backward:"
    let (dp, ds) = bwd lyr (paras, [2, 3, -1], [1, 1])
    print dp
  where
    lyr :: TriLens V V [((V, V), D)] [((V, V), D)] [Para] [Para] V V
    lyr = layer 3 2 -- 3 in, 2 out

-- Gradient descent
testLearning :: TriLens V V [[((V, V), D)]] [[((V, V), D)]] [[Para]] [[Para]] V V ->
    Double -> [V] -> [V] -> [[Para]] -> IO [[Para]]
testLearning mlp rate xs ys para = do
    let ((_, dp), _) = bwd batchLoss ((ys, para), xs, 1)
    -- Update parameters
    let para1 = para <+> scale (-rate) dp
    putStrLn "\nForward pass: "
    print $ fwd batch (para1, xs)
    putStrLn "Forward pass error: " 
    print $ fwd batchLoss ((ys, para1), xs)
    return para1
  where
    batch :: TriLens [V] [V] [[[((V, V), D)]]] [[[((V, V), D)]]] [[Para]] [[Para]] [V] [V]
    batch = batchN 4 mlp 
    batchLoss :: TriLens D D 
                     ([[[((V, V), D)]]], ([V], [V])) ([[[((V, V), D)]]], ([V], [V]))
                     ([V], [[Para]]) ([V], [[Para]])
                     [V] [V]
    batchLoss = triCompose batch lossT

iterateM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateM 0 _ _ = return []
iterateM n f x = do
    x' <- f x
    (x':) `fmap` iterateM (n-1) f x'

-- Taken from Andrej Karpathy's micrograd tutorial
main :: IO ()
main = do
    let xs = [[2, 3, -1]
             ,[3, -1, 0.5]
             ,[0.5, 1, 1]
             ,[1, 1, -1]]
    let ys = fmap singleton [1, -1, -1, 1]
    let rate = 0.5
    let (para, _) = initParaMlp 3 [4, 4, 1] rands
    paras <- iterateM 25 (testLearning mlp rate xs ys) para 
    return ()
  where
    mlp :: TriLens V V [[((V, V), D)]] [[((V, V), D)]] [[Para]] [[Para]] V V
    mlp = makeMlp 3 [4, 4, 1]
