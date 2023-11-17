module Perceptron
import Data.Vect
import HVect
import PLens
import NNet

-- Chain of parameter blocks
-- Parameters for multi-layer perceptron with mIn inputs
-- A chain of types ParaBlock m n1 :: ParaBlock n1 n2 :: ParaBlock n2 n3 ...
public export
ParaChain : (mIn : Nat) -> (ns : Vect l Nat) -> Vect l Type
ParaChain mIn [] = []
ParaChain mIn (nOut' :: ns') = ParaBlock mIn nOut' :: ParaChain nOut' ns'

-- Chain of vectors of parameter blocks (for batches of perceptrons)
0 VParaChain : (k : Nat) -> (mIn : Nat) -> {l : Nat} -> (ns : Vect l Nat) -> Vect l Type
VParaChain k mIn ns = ReplTypes k (ParaChain mIn ns)

-------------
-- Interfaces
-------------

-- Proof that every type in ParaChain is a Monoid
isMonoChain : {mIn : Nat} -> (ns : Vect l Nat) -> HVect (map Monoid (ParaChain mIn ns))
isMonoChain Nil = Nil
isMonoChain (n' :: ns') = MkMonoid neutral :: isMonoChain ns'

--  in (ParaChain mIn ns), all types are Monoid
collectH : {k : Nat} -> {mIn : Nat} -> {l : Nat} -> {ns : Vect l Nat} -> 
    HVect (VParaChain k mIn ns) -> HVect (ParaChain mIn ns)
collectH hv = concatH {isMono = isMonoChain ns} hv

export
collectParas : {k : Nat} -> {mIn : Nat} -> {l : Nat} -> {ns : Vect l Nat} -> 
    Vect k (HVect (ParaChain mIn ns)) -> HVect (ParaChain mIn ns)
collectParas = collectH . transposeH


-- The architecture is specified by number of inputs mIn and a list of l+1 layers ns
-- mIn    -> [mIn, n1] -> [n1, n2] -> ... [n l, n (l+1)]

public export
data Layout : (ins : Nat) -> (layers : Vect (S m) Nat) -> Type where
  MkLayout : (ins : Nat) -> (layers : Vect (S m) Nat) -> Layout ins layers

export
inN : Layout i ls -> Nat
inN (MkLayout ins _) = ins

export
outN : Layout i ls -> Nat
outN (MkLayout _ layers) = last layers

public export
MLParas : Layout ins layers -> Type
MLParas (MkLayout ins layers) = HVect (ParaChain ins layers)

-- Multi layer perceptron with m inputs and l+1 layers
-- neuron count in each layer is given by (Vect l Nat)

--   1   2 .. n2 [n2]
--   n1  n1   n1
--   |/ \|/  \|
--   1   2 .. n1 [n1] <-n1- [P[m], P[m] .. P[m]]
--   m   m    m
--    \ / \  /
--       m

export
makeMLP : (ly : Layout ins layers) -> 
    PLens (MLParas ly) (V ins) (V (last layers))
makeMLP (MkLayout mIn [nOut]) = MkPLens fwd' bwd'
  where
    lr : PLens (ParaBlock mIn nOut) (V mIn) (V nOut)
    lr = layer nOut mIn
    -- new layout with one layer
    Ly : Layout mIn [nOut] -- must be capitalized or the magic won't happen
    Ly = MkLayout mIn [nOut]

    fwd' : (MLParas Ly, V mIn) -> V (nOut)
    fwd' ([p], v) = lr.fwd (p, v)
    bwd' : (MLParas Ly, V mIn, V nOut) -> (MLParas Ly, V mIn)
    bwd' ([p], v, w) = let (p', v') = lr.bwd (p, v, w)
                       in ([p'], v')
makeMLP (MkLayout mIn (n1 :: n2 :: ns)) =  MkPLens fwd' bwd'
  where
    -- m -> [m, n1] -> [n1, n2] -> ... [n l, n (l+1)]
    -- Layout for the recursive part
    Ly : Layout n1 (n2 :: ns)
    Ly = MkLayout n1 (n2 :: ns)
    mlp' : PLens (MLParas Ly) (V (inN Ly)) (V (outN Ly))
    mlp' = makeMLP Ly --<< recurse
    -- compose with the bottom layer
    mlpComp : PLens (ParaBlock mIn n1, MLParas Ly)
                    (V mIn)
                    (V (last (n2 :: ns)))
    mlpComp = compose (layer n1 mIn) mlp'
    -- New layout for the composite
    Ly' : Layout mIn (n1 :: n2 :: ns)
    Ly' = MkLayout mIn (n1 :: n2 :: ns)

    fwd' : (MLParas Ly', V mIn) -> V (last (n1 :: n2 :: ns))
    fwd' (p1 :: ps, vm) = mlpComp.fwd ((p1, ps), vm)
    bwd' : (MLParas Ly', V mIn, V (last (n1 :: n2 :: ns))) ->
           (MLParas Ly', V mIn)
    bwd' (pmn1 :: pmns, s, a) =
      let ((pmn1', pmns'), s') = mlpComp.bwd ((pmn1, pmns), s, a)
      in (pmn1' :: pmns', s')


-- Initialize parameters for an MLP

export
initParaChain : (ly : Layout ins layers) ->
    Stream Double -> (MLParas ly, Stream Double)
initParaChain (MkLayout mIn ([nOut])) s = 
  let (pb, s') = initParaBlock mIn nOut s
  in ([pb], s')
initParaChain (MkLayout mIn (n1 :: n2 :: ns)) s = 
  let (pb, s') = initParaBlock mIn n1 s 
      (pbs, s'') = initParaChain (MkLayout n1 (n2 :: ns)) s'
  in (pb :: pbs, s'')
