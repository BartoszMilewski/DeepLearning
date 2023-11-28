module Perceptron where
import ExLens
import NNet

makeMlp :: Int -> [Int] -> ExLens  [[Para]] [[Para]] V V V V
makeMlp mIn [nOut] = singleParas $ layer mIn nOut
makeMlp mIn (n1 : n2 : ns) = consParas $ compose ly mlp 
  where ly = layer mIn n1
        mlp = makeMlp n1 (n2 : ns)
  
-- Initialize parameters for an MLP
initParaMlp :: Int -> [Int] -> [D] -> ([[Para]], [D])
initParaMlp mIn [nOut] stm = 
    let (pb, stm') = initParaBlock mIn nOut stm
    in ([pb], stm')
initParaMlp mIn (n1 : n2 : ns) stm =
    let (pb, stm') = initParaBlock mIn n1 stm
        (pbs, stm'') = initParaMlp n1 (n2 : ns) stm'
    in (pb : pbs, stm'')
