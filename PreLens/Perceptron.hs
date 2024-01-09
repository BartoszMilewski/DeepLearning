module Perceptron where
import PreLens
import Tambara
import TriLens
import Params
import NNet
import Data.Bifunctor ( Bifunctor(second, first, bimap) )
import Data.List

-- Multi-layer perceptron 
-- The first layer contains neurons with mIn inputs each
-- The list [Int] specifies the number of neurons in each layer (staring with the first layer)
-- Each neuron has one output
makeMlp :: Int -> [Int] -> TriLens V V [[((V, V), D)]] [[((V, V), D)]] [[Para]] [[Para]] V V
-- layer : V [((V, V), D)] [Para] V
makeMlp mIn [nOut] = 
    dimapM (first singleton) (first head) .
    dimapP (second head) (second singleton) . 
    layer mIn nOut
makeMlp mIn (n1 : n2 : ns) = 
    dimapM (first cons) (first unCons) .
    dimapP (second (sym . unCons)) (second (cons . sym)) .
    triCompose (layer mIn n1) (makeMlp n1 (n2 : ns)) 
  
-- Initialize parameters for an MLP
initParaMlp :: Int -> [Int] -> [D] -> ([[Para]], [D])
initParaMlp mIn [nOut] stm = 
    let (pb, stm') = initParaBlock mIn nOut stm
    in ([pb], stm')
initParaMlp mIn (n1 : n2 : ns) stm =
    let (pb, stm') = initParaBlock mIn n1 stm
        (pbs, stm'') = initParaMlp n1 (n2 : ns) stm'
    in (pb : pbs, stm'')
