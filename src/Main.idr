module Main
import Data.Bits
import Data.Vect
import HVect
import PLens
import NNet

-- Simple random number generator

random : Int32 -> Stream Int32
random seed = let seed' = 1664525 * seed + 1013904333
              in (seed' `shiftR` 2) :: random seed'

-- Stream of pseudo-random doubles [-1, 1]
rands : Stream Double
rands = map normalize (random 42)
  where
    normalize : Int32 -> Double
    normalize n = (fromInteger (cast n)) / fromInteger(2147483647)

main : IO ()
main = do
  let ly : Layout = MkLayout 3 [4, 4, 1]
  let mlp : PLens (MLParas ly) (V (ins ly)) (V (outs ly)) = makeMLP ly
  let paras : MLParas ly = fst (initParaChain ly rands)
  let iput : Vect 3 Double = [2.0, 3.0, -1.0]
  print $ (mlp.fwd) (paras, iput) -- << Can't solve constraint between: 3 and ly .ins
  putStrLn "Done"