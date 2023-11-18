module Perceptron
import Data.Vect
import HVect
import PLens
import NNet

-- The architecture is specified by number of inputs mIn and a list of l+1 layers ns
-- Where l is zero or more hidden layers
-- mIn    -> [mIn, n1] -> [n1, n2] -> ... [n l, n (l+1)]

public export
data Layout : (mIn : Nat) -> (layers : Vect (S l) Nat) -> Type where
  MkLayout : (mIn : Nat) -> (l : Nat) -> (layers : Vect (S l) Nat) -> Layout mIn layers

export
inN : Layout i ls -> Nat
inN (MkLayout mIn l _) = mIn

export
outN : Layout i ls -> Nat
outN (MkLayout _ l layers) = last layers

-- Chain of parameter blocks
-- Parameters for multi-layer perceptron with mIn inputs
-- A chain of types ParaBlock m n1 :: ParaBlock n1 n2 :: ParaBlock n2 n3 ...
public export
ParaChain : Layout mIn ns -> Vect (length ns) Type
ParaChain ly with (ly)
  _ | (MkLayout m Z [n]) = [ParaBlock m n]
  _ | (MkLayout m (S l) (n1 :: n2 :: ns')) = ParaBlock m n1 :: ParaChain (MkLayout n1 l (n2 :: ns'))

-- Chain of vectors of parameter blocks (for batches of perceptrons)
0 VParaChain : (k : Nat) -> Layout mIn ns -> Vect (Vect.length ns) Type
VParaChain k ly = ReplTypes k (ParaChain ly)

-- Proof that every type in ParaChain is a Monoid
isMonoChain : (ly : Layout mIn ns) -> HVect (map Monoid (ParaChain ly))
isMonoChain ly with (ly)
  _ | (MkLayout m Z [n]) = [MkMonoid neutral]
  _ | (MkLayout m (S l) (n1 :: n2 :: ns')) = MkMonoid neutral :: isMonoChain (MkLayout n1 l (n2 :: ns'))


-- concatH : {k : Nat} -> {l : Nat} -> {ts : Vect l Type} -> {isMono : HVect (map Monoid ts)} -> 
--     HVect (ReplTypes k ts) -> HVect ts

--  in (ParaChain mIn ns), all types are Monoid
collectH : {k : Nat} -> {mIn : Nat} -> {layers : Vect (S l) Nat} -> (ly : Layout mIn layers) -> 
    HVect (VParaChain k ly) -> HVect (ParaChain ly)
collectH ly@(MkLayout mIn l layers) hv = 
  concatH {ts = ParaChain ly} {isMono = isMonoChain ly} hv

-- transposeH : {k : Nat} -> {l : Nat} -> {ts : Vect l Type} -> 
--     Vect k (HVect ts) -> HVect (ReplTypes k ts)

export
collectParas : {k : Nat} -> {mIn : Nat} -> {l : Nat} -> {layers : Vect (S l) Nat} -> 
    (ly : Layout mIn layers) -> 
    Vect k (HVect (ParaChain ly)) -> HVect (ParaChain ly)
collectParas ly@(MkLayout mIn l layers) v = collectH ly (transposeH v)

public export
MLParas : Layout mIn layers -> Type
MLParas ly@(MkLayout m l layers) = HVect (ParaChain ly)

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
makeMLP : (ly : Layout mIn layers) -> 
    PLens (MLParas ly) (V mIn) (V (last layers))
makeMLP (MkLayout mIn Z [nOut]) = MkPLens fwd' bwd'
  where
    lr : PLens (ParaBlock mIn nOut) (V mIn) (V nOut)
    lr = layer nOut mIn
    -- new layout with one layer
    Ly : Layout mIn [nOut] -- must be capitalized or the magic won't happen
    Ly = MkLayout mIn Z [nOut]

    fwd' : (MLParas Ly, V mIn) -> V (nOut)
    fwd' ([p], v) = lr.fwd (p, v)
    bwd' : (MLParas Ly, V mIn, V nOut) -> (MLParas Ly, V mIn)
    bwd' ([p], v, w) = let (p', v') = lr.bwd (p, v, w)
                       in ([p'], v')
makeMLP (MkLayout mIn (S l) (n1 :: n2 :: ns)) =  MkPLens fwd' bwd'
  where
    -- m -> [m, n1] -> [n1, n2] -> ... [n l, n (l+1)]
    -- Layout for the recursive part
    Ly : Layout n1 (n2 :: ns)
    Ly = MkLayout n1 l (n2 :: ns)
    mlp' : PLens (MLParas Ly) (V (inN Ly)) (V (outN Ly))
    mlp' = makeMLP Ly --<< recurse
    -- compose with the bottom layer
    mlpComp : PLens (ParaBlock mIn n1, MLParas Ly)
                    (V mIn)
                    (V (last (n2 :: ns)))
    mlpComp = compose (layer n1 mIn) mlp'
    -- New layout for the composite
    Ly' : Layout mIn (n1 :: n2 :: ns)
    Ly' = MkLayout mIn (S l) (n1 :: n2 :: ns)

    fwd' : (MLParas Ly', V mIn) -> V (last (n1 :: n2 :: ns))
    fwd' (p1 :: ps, vm) = mlpComp.fwd ((p1, ps), vm)
    bwd' : (MLParas Ly', V mIn, V (last (n1 :: n2 :: ns))) ->
           (MLParas Ly', V mIn)
    bwd' (pmn1 :: pmns, s, a) =
      let ((pmn1', pmns'), s') = mlpComp.bwd ((pmn1, pmns), s, a)
      in (pmn1' :: pmns', s')


-- Initialize parameters for an MLP

export
initParaChain : (ly : Layout mIn layers) ->
    Stream Double -> (MLParas ly, Stream Double)
initParaChain (MkLayout m Z ([n])) s = 
  let (pb, s') = initParaBlock m n s
  in ([pb], s')
initParaChain (MkLayout m (S l) (n1 :: n2 :: ns)) s = 
  let (pb, s') = initParaBlock m n1 s 
      (pbs, s'') = initParaChain (MkLayout n1 l (n2 :: ns)) s'
  in (pb :: pbs, s'')

