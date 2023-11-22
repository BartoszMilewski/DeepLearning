module Main
import Data.Bits
import Data.Vect
import HVect
import PLens
import NNet
import Perceptron

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


run : {l : Nat} -> (mIn : Nat) -> (ns : Vect (S l) Nat) -> Vect mIn Double -> Vect (Vect.last ns) Double
run mIn ns v =
  let mlp   : PLens (HVect (ParaChain mIn ns)) (V mIn) (V (last ns)) := makeMLP mIn ns
      paras : HVect (ParaChain mIn ns) := fst (initParaChain mIn ns rands)
   in mlp.fwd (paras, v)



main : IO ()
main = do
  let ns = [4,4,1]
  let inpt = [1, 2, 3]
  printLn $ run {l = 2} 3 ns inpt
