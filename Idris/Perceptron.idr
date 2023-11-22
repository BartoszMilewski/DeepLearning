module Perceptron
import Data.Vect
import HVect
import PLens
import NNet

-- The architecture is specified by number of inputs mIn and a list of l+1 layers ns
-- Where l is zero or more hidden layers
-- mIn    -> [mIn, n1] -> [n1, n2] -> ... [n l, n (l+1)]
{-
public export
data Layout : (mIn : Nat) -> (layers : Vect (S l) Nat) -> Type where
  MkLayout : (mIn : Nat) -> (l : Nat) -> (layers : Vect (S l) Nat) -> Layout mIn layers

export
inN : Layout i ls -> Nat
inN (MkLayout mIn l _) = mIn

export
outN : Layout i ls -> Nat
outN (MkLayout _ l layers) = last layers
-}

-- Chain of parameter blocks
-- Parameters for multi-layer perceptron with mIn inputs
-- A chain of types:
-- ParaBlock mIn n1 :: ParaBlock n1 n2 :: ParaBlock n2 n3 ...
public export
ParaChain : {l : Nat} -> (mIn : Nat) -> (ns : Vect l Nat) -> Vect l Type
ParaChain mIn [] = Nil
ParaChain mIn (n :: ns') = ParaBlock mIn n :: ParaChain n ns'

-- Chain of vectors of parameter blocks (for batches of perceptrons)
0 VParaChain : {l : Nat} -> (k : Nat) -> (mIn : Nat) -> (ns : Vect l Nat) -> Vect l Type
VParaChain k mIn ns = ReplTypes k (ParaChain mIn ns)

-- Proof that every type in ParaChain is a Monoid
isMonoChain : {l : Nat} -> (mIn : Nat) -> (ns : Vect l Nat) -> HVect (map Monoid (ParaChain mIn ns))
isMonoChain mIn [] = Nil
isMonoChain mIn (n :: ns') = (%search) :: isMonoChain n ns'

-- 
-- concatH : {k : Nat} -> {l : Nat} -> {ts : Vect l Type} -> {isMono : HVect (map Monoid ts)} -> 
--     HVect (ReplTypes k ts) -> HVect ts

--  in (ParaChain mIn ns), all types are Monoid
collectH : {l : Nat} -> {k : Nat} -> {mIn : Nat} -> {ns : Vect l Nat} -> 
    HVect (VParaChain k mIn ns) -> HVect (ParaChain mIn ns)
collectH hv = concatH {isMono = isMonoChain mIn ns} hv

-- transposeH : {k : Nat} -> {l : Nat} -> {ts : Vect l Type} -> 
--     Vect k (HVect ts) -> HVect (ReplTypes k ts)

export
collectParas : {k : Nat} -> {mIn : Nat} -> {l : Nat} -> {ns : Vect l Nat} -> 
    Vect k (HVect (ParaChain mIn ns)) -> HVect (ParaChain mIn ns)
collectParas = collectH . transposeH

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
makeMLP : {l : Nat} -> (mIn : Nat) -> (ns : Vect (S l) Nat) -> 
    PLens (HVect (ParaChain mIn ns)) (V mIn) (V (last ns))
makeMLP mIn ([nOut]) = MkPLens fwd' bwd'
  where
    lr : PLens (ParaBlock mIn nOut) (V mIn) (V nOut)
    lr = layer nOut mIn

    fwd' : (HVect (ParaChain mIn [nOut]), V mIn) -> V (nOut)
    fwd' ([p], v) = lr.fwd (p, v)
    bwd' : (HVect (ParaChain mIn [nOut]), V mIn, V nOut) -> (HVect (ParaChain mIn [nOut]), V mIn)
    bwd' ([p], v, w) = let (p', v') = lr.bwd (p, v, w)
                       in ([p'], v')
makeMLP mIn (n1 :: n2 :: ns) =  MkPLens fwd' bwd'
  where
    -- m -> [m, n1] -> [n1, n2] -> ... [n l, n (l+1)]
    -- Layout for the recursive part
    mlp' : PLens (HVect (ParaChain n1 (n2 :: ns))) (V n1) (V (last (n2 :: ns)))
    mlp' = makeMLP n1 (n2 :: ns) --<< recurse
    -- compose with the bottom layer
    mlpComp : PLens (ParaBlock mIn n1, HVect (ParaChain n1 (n2 :: ns)))
                    (V mIn)
                    (V (last (n2 :: ns)))
    mlpComp = compose (layer n1 mIn) mlp'
    fwd' : (HVect (ParaChain mIn (n1 :: n2 :: ns)), V mIn) -> V (last (n1 :: n2 :: ns))
    fwd' (p1 :: ps, vm) = mlpComp.fwd ((p1, ps), vm)
    bwd' : (HVect (ParaChain mIn (n1 :: n2 :: ns)), V mIn, V (last (n1 :: n2 :: ns))) ->
           (HVect (ParaChain mIn (n1 :: n2 :: ns)), V mIn)
    bwd' (pmn1 :: pmns, s, a) =
      let ((pmn1', pmns'), s') = mlpComp.bwd ((pmn1, pmns), s, a)
      in (pmn1' :: pmns', s')

-- Initialize parameters for an MLP

export
initParaChain : {l : Nat} -> (mIn : Nat) -> (ns : Vect (S l) Nat) ->
    Stream Double -> (HVect (ParaChain mIn ns), Stream Double)
initParaChain mIn ([n]) s = 
  let (pb, s') = initParaBlock mIn n s
  in ([pb], s')
initParaChain mIn (n1 :: n2 :: ns) s = 
  let (pb, s') = initParaBlock mIn n1 s 
      (pbs, s'') = initParaChain n1 (n2 :: ns) s'
  in (pb :: pbs, s'')
