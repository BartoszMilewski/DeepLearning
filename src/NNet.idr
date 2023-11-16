module NNet
import Data.Vect
import HVect
import PLens

-- Vector of Double
public export
0 V : (n : Nat) -> Type
V n = Vect n Double

-- Parameters for an affine lens of 
-- mIn inputs, one output
public export
record Para (mIn : Nat) where
    constructor MkPara
    weight : Vect mIn Double
    bias   : Double

-- ParaBlock mIn nOut, vector of nOut parameters, each mIn wide
-- (nOut * mIn inputs, nOut outputs)
public export
ParaBlock : (mIn : Nat) -> (nOut : Nat) -> Type
ParaBlock mIn nOut = Vect nOut (Para mIn)

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
export
{mIn : Nat} -> Show (Para mIn) where
    show pa = "weight: " ++ show (weight pa) ++ " bias: " ++ show (bias pa) ++ "\n"

-- Semigroup

Semigroup Double where
  x <+> y = x + y

export
Semigroup (Para m) where
    (MkPara w b) <+> (MkPara w' b') = MkPara (zipWith (+) w w') (b + b')

-- Monoid
Monoid Double where
    neutral = 0.0

{m : Nat} -> Monoid (Para m) where
    neutral = MkPara (replicate m 0.0) 0.0

-- Proof that every type in ParaChain is a Monoid
isMonoChain : {mIn : Nat} -> (ns : Vect l Nat) -> HVect (map Monoid (ParaChain mIn ns))
isMonoChain Nil = Nil
isMonoChain (n' :: ns') = MkMonoid neutral :: isMonoChain ns'

-- Vector Space
export
{m : Nat} -> VSpace (Para m) where
  scale a (MkPara w b) = MkPara (map (a *) w) (a * b)

export
{mIn : Nat} -> {nOut : Nat} -> VSpace (ParaBlock mIn nOut) where
    scale a v = map (scale a) v

--  in (ParaChain mIn ns), all types are Monoid
collectH : {k : Nat} -> {mIn : Nat} -> {l : Nat} -> {ns : Vect l Nat} -> 
    HVect (VParaChain k mIn ns) -> HVect (ParaChain mIn ns)
collectH hv = concatH {isMono = isMonoChain ns} hv

export
collectParas : {k : Nat} -> {mIn : Nat} -> {l : Nat} -> {ns : Vect l Nat} -> 
    Vect k (HVect (ParaChain mIn ns)) -> HVect (ParaChain mIn ns)
collectParas = collectH . transposeH

-------------------------------------
------- Vector parametric lenses ----
-------------------------------------

-- activation lens using tanh (no parameters)

activ : Lens Double Double
activ = MkLens (\s => tanh s)
               (\(s, a) => a * (1 - (tanh s)*(tanh s))) -- a * da/ds

-- Affine parametric lens 
-- (really a composition of linear and bias, but they are always used in combination)

affine : (mIn : Nat) -> PLens (Para mIn) (V mIn) Double
affine nOut = MkPLens fwd' bwd'
  where
    fwd' : (Para mIn, V mIn) -> Double
    fwd' (p, s) = foldl (+) (bias p) (zipWith (*) (weight p) s) -- a = b + w * s
    bwd' : (Para mIn, V mIn, Double) -> (Para mIn, V mIn)
    bwd' (p, s, a) = ( MkPara (map (a *) s) a  -- (da/dw, da/db)
                     , map (a *) (weight p))   -- da/ds

-- Initialize parameters for an affine lens
initPara : (mIn : Nat) -> Stream Double -> (Para mIn, Stream Double)
initPara mIn s = 
  let (v, s') = takes mIn s 
      (x, s'') = take1 s'
      in (MkPara v x, s'')


-- Neuron with mIn inputs and one output

-- affine    : PLens (Para mIn) (V mIn) Double
-- activ     : Lens Double Double
-- composite : PLens (Para mIn) (V mIn) Double

export
neuron : (mIn : Nat) -> PLens (Para mIn) (V mIn) Double
neuron mIn = composeR (affine mIn) activ


-- A layer of neurons

-- n neurons with m inputs each
--   1   2 .. n
--   |   |    |
--   m   m    m
--    \ / \  /
--       m
-- ParaBlock m n = Vect n (Para m)
-- neuron m : PLens (Vect n (Para 1)) (V m) (V 1)
-- vecLens n (neuron m): PLens (Vect n (Vect n (Para 1))) (Vect n (V m)) (Vect n (V 1))
-- branch n : Lens (V m) (Vect n (V m))
--                   s        a
-- composeL : Lens s a -> PLens p a b -> PLens p s b
export
layer : (nOut : Nat) -> (mIn : Nat) -> PLens (Vect nOut (Para mIn)) (V mIn) (V nOut)
layer nOut mIn = composeL (branch nOut) (vecLens nOut (neuron mIn))

-- Initialize parameters for a layer of n neurons, each with m inputs
-- ParaBlock mIn nOut, vector of nOut parameters, each mIn wide
initParaBlock : (mIn : Nat) -> (nOut : Nat) -> Stream Double -> 
   (ParaBlock mIn nOut, Stream Double)
initParaBlock mIn nOut s = unfoldl nOut (initPara mIn) s

-- The architecture is specified by number of inputs mIn and a list of l+1 layers ns
-- mIn    -> [mIn, n1] -> [n1, n2] -> ... [n l, n (l+1)]

public export
data Layout : (ins : Nat) -> (layers : Vect (S m) Nat) -> Type where
  MkLayout : (ins : Nat) -> (layers : Vect (S m) Nat) -> Layout ins layers

inN : Layout i ls -> Nat
inN (MkLayout ins _) = ins

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

-- mean square error 0.5 * Sum (si - gi)^2
-- derivative: d/dsi = (si - gi)
delta : V n -> V n -> Double
delta s g = 0.5 * (sum $ map (\x => x * x) (zipWith (-) s g))

-- Sum of squares loss lens
export
loss : V n -> Lens (V n) Double
loss gtruth = MkLens (\s => delta s gtruth)
                     (\(s, a) => backLoss gtruth s a)
  where
    backLoss : V n -> V n -> Double -> V n
    backLoss g s a =  map ( a *) (zipWith (-) s g)
