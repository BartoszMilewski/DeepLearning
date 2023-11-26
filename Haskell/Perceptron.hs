{-# language ScopedTypeVariables #-}
module Perceptron where
import PLens
import NNet
import Distribution.FieldGrammar (VCat(VCat))
import Language.Haskell.TH (safe)

makeMlp :: Int -> [Int] -> PLens  [[Para]] [[Para]] V V V V
makeMlp mIn [nOut] = PLens fw bw
  where
    ly :: PLens [Para] [Para] V V V V
    ly = layer mIn nOut
    fw ([ps], s) = fwd ly (ps, s)
    bw ([ps], s, da) = 
        let (dp, ds) = bwd ly (ps, s, da)
        in ([dp], ds)
makeMlp mIn (n1 : n2 : ns) = PLens fw bw
  where
    ly :: PLens [Para] [Para] V V V V
    ly = layer mIn n1
    mlp = makeMlp n1 (n2 : ns)
    lns :: PLens ([Para], [[Para]]) ([Para], [[Para]]) V V V V
    lns = compose ly mlp
    fw (p1 : ps, s) = fwd lns ((p1, ps), s)
    bw (p1 : ps, s, da) = 
        let ((p1', ps'), ds) = bwd lns ((p1, ps), s, da)
        in (p1' : ps', ds)

-- Initialize parameters for an MLP
initParaMlp :: Int -> [Int] -> [D] -> ([[Para]], [D])
initParaMlp mIn [nOut] stm = 
    let (pb, stm') = initParaBlock mIn nOut stm
    in ([pb], stm')
initParaMlp mIn (n1 : n2 : ns) stm =
    let (pb, stm') = initParaBlock mIn n1 stm
        (pbs, stm'') = initParaMlp n1 (n2 : ns) stm'
    in (pb : pbs, stm'')
