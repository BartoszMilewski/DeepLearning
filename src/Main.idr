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


run : (Layout i o) -> Vect i Double -> Vect (Vect.last o) Double
run ly@(MkLayout ins layers) v =
  let mlp   : PLens (MLParas ly) (V ins) (V (last layers)) := makeMLP ly
      paras : MLParas ly := fst (initParaChain ly rands)
   in mlp.fwd (paras, v)

main : IO ()
main = do
  let ly = MkLayout 3 [4,4,1]
  let inpt = [1, 2, 3]
  printLn $ run ly inpt