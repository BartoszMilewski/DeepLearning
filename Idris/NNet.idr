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

-- Vector Space
export
{m : Nat} -> VSpace (Para m) where
  scale a (MkPara w b) = MkPara (map (a *) w) (a * b)

export
{mIn : Nat} -> {nOut : Nat} -> VSpace (ParaBlock mIn nOut) where
    scale a v = map (scale a) v

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
export
initParaBlock : (mIn : Nat) -> (nOut : Nat) -> Stream Double -> 
   (ParaBlock mIn nOut, Stream Double)
initParaBlock mIn nOut s = unfoldl nOut (initPara mIn) s

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
