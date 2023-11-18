module HVect
import Data.Vect
--import Data.Vect.Quantifiers

-- Heterogeneous vector
public export
data HVect : Vect n Type -> Type where
  Nil : HVect Nil
  (::) : h -> HVect t -> HVect (h :: t)

export
Show (HVect []) where
    show Nil = "\n"

export
(Show t, Show (HVect ts)) => Show (HVect (t :: ts)) where
    show (x :: xs) = show x ++ " :: " ++ show xs

export
Semigroup (HVect []) where
    [] <+> [] = []

export
(Semigroup t, Semigroup (HVect ts)) =>  
  Semigroup (HVect (t :: ts)) where
    (a :: as) <+> (b :: bs) = (a <+> b) :: (as <+> bs)

export
Monoid (HVect []) where
    neutral = []

export
(Monoid t, Monoid (HVect ts)) => Monoid (HVect (t :: ts)) where
    neutral = neutral :: neutral


public export
interface (Semigroup v, Monoid v) => VSpace v where
    scale : Double -> v -> v

export
VSpace (HVect []) where
    scale a Nil = Nil

export
(VSpace t, VSpace (HVect ts)) => VSpace (HVect (t :: ts)) where
    scale a (v :: vs) = scale a v :: scale a vs


-- Replicate a vector of types
-- map (Vect k) ts
public export
0 ReplTypes : {l : Nat} -> (k : Nat) -> (ts : Vect l Type) -> Vect l Type
ReplTypes k [] = []
ReplTypes k (t' :: ts') = Vect k t' :: ReplTypes k ts'

-- Concatenate vectors of heterogeneous monoid types
export
concatH : {k : Nat} -> {l : Nat} -> {ts : Vect l Type} -> {isMono : HVect (map Monoid ts)} -> 
    HVect (ReplTypes k ts) -> HVect ts
concatH {l = 0} {ts = []} Nil = Nil
concatH {ts = t' :: ts'} {isMono = (_ :: pfs)} (v :: vs) = concat v :: concatH {isMono = pfs} vs
  
export
emptyVTypes : {l : Nat} -> (ts : Vect l Type) -> HVect (ReplTypes 0 ts)
emptyVTypes [] = Nil
emptyVTypes (t' :: ts') = [] :: emptyVTypes ts'

-- Generalization of zipWith (::)
export
zipCons : {k : Nat} -> {l : Nat} -> {ts : Vect l Type} -> 
    HVect ts -> HVect (ReplTypes k ts) -> HVect (ReplTypes (S k) ts)
zipCons [] [] = []
zipCons (t' :: ts') (vs :: vss) = (t' :: vs) :: zipCons ts' vss

-- Transpose a vector whose entries are heterogeneous vectors
export
transposeH : {k : Nat} -> {l : Nat} -> {ts : Vect l Type} -> 
    Vect k (HVect ts) -> HVect (ReplTypes k ts)
transposeH {k=0} {ts} [] = emptyVTypes ts
transposeH (h :: hs) = zipCons h (transposeH hs)

export
unfoldl : (n : Nat) -> (s -> (a, s)) -> s -> (Vect n a, s)
unfoldl Z f s = (Nil, s)
unfoldl (S k) f s =
  let (x, s') = f s
      (xs, s'') = unfoldl k f s'
  in (x :: xs, s'')

export
takes : (n : Nat) -> Stream a -> (Vect n a, Stream a)
takes Z s = (Nil, s)
takes (S k) (x :: xs) = 
  let (v, s') = takes k xs
  in (x :: v, s')

export
take1 : Stream a -> (a, Stream a)
take1 (x :: xs) = (x, xs)