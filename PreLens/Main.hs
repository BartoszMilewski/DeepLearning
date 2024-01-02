module Main where
import Tambara
import TriLens
import NNet
import Perceptron
import Data.Int (Int32)
import Data.Bits (shiftR)

-- Home-made random number generator, in case no Random library available

random :: Int32 -> [Int32]
random seed = let seed' = 1664525 * seed + 1013904333
              in (seed' `shiftR` 2) : random seed'

rands :: [Double]
rands = map normalize (random 42)
  where
    normalize :: Int32 -> Double
    normalize n = fromIntegral n / 2147483647

lyr :: TriLens V V [((V, V), D)] [((V, V), D)] [Para] [Para] V V
lyr = layer 3 2 -- 3 in, 2 out

testLayer :: IO ()
testLayer = do
  let (paras, _) = initParaBlock 3 2 rands
  print $ fwd lyr (paras, [2, 3, -1])
  putStrLn "Backward:"
  let (dp, ds) = bwd lyr (paras, [2, 3, -1], [1, 1])
  print dp

mlp :: TriLens V V [[((V, V), D)]] [[((V, V), D)]] [[Para]] [[Para]] V V
mlp = makeMlp 3 [4, 4, 1]

testP :: IO ()
testP = 
  let xs = [2, 3, -1]
      (para, _) = initParaMlp 3 [4, 4, 1] rands
  in do
    print $ fwd mlp (para, xs)
    let (dp, ds) = bwd mlp (para, xs, [1])
    putStrLn "Backward params:"
    print dp
    putStrLn "Backward input:"
    print ds

main :: IO ()
main = do
    let xs = [[2, 3, -1]
             ,[3, -1, 0.5]
             ,[0.5, 1, 1]
             ,[1, 1, -1]]
    let ys = [1, -1, -1, 1]
    print $ take 10 rands