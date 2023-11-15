module PLens
import Data.Vect
import HVect

----------
-- Parametric lens

-- record PLens p p' s s' a a'
--   fwd : (p, s) -> a 
--   lens1.bwd : (p, s, a') -> (p', s')

public export
record PLens p s a where
    constructor MkPLens
    fwd : (p, s)    -> a
    bwd : (p, s, a) -> (p, s)

-- Special case of parametric lens with p = ()
-- Simplifies composition

public export
record Lens s a where
    constructor MkLens
    fwd0 : s      -> a
    bwd0 : (s, a) -> s

-- Composition of parametric lenses
export
compose : PLens p s a -> PLens q a b ->
            PLens (p, q) s b
  -- lens1.fwd  : (p, s)    -> a
  -- lens1.bwd  : (p, s, a) -> (p, s)
  -- lens2.fwd : (q, a)    -> b
  -- lens2.bwd : (q, a, b) -> (q, a)
compose lens1 lens2 = MkPLens fwd' bwd'
    where
      fwd' : ((p, q), s) -> b
      fwd' ((p, q), s) = lens2.fwd (q, lens1.fwd (p, s))
      bwd' : ((p, q), s, b) -> ((p, q), s)
      bwd' ((p, q), s, b) =
        let (q', a') = lens2.bwd (q, lens1.fwd (p, s), b)
            (p', s') = lens1.bwd (p, s, a')
        in ((p', q'), s')

-- Helpers for composing a parametric lens with a non-parametric one
export
composeR : PLens p s a -> Lens a b ->
           PLens p s b
composeR lens1 lens2 = MkPLens fwd' bwd'
  where
    fwd' : (p, s) -> b
    fwd' (p, s)     = lens2.fwd0 (lens1.fwd (p, s))
    bwd' : (p, s, b) -> (p, s)
    bwd' (p, s, b) =
        let a' = lens2.bwd0 (lens1.fwd (p, s), b)
            (p', s') = lens1.bwd (p, s, a')
        in (p', s')
export
composeL : Lens s a -> PLens p a b ->
           PLens p s b
-- lens1.fwd : s -> a
-- lens1.bwd : (s, a) -> s
-- lens2.fwd : (p, a)    -> b
-- lens2.bwd : (p, a, b) -> (p, a)
composeL lens1 lens2 = MkPLens fwd' bwd'
  where
    fwd' : (p, s) -> b
    fwd' (p, s) = lens2.fwd (p, lens1.fwd0 s)
    bwd' : (p, s, b) -> (p, s)
    bwd' (p, s, b) =
        let (p', a') = lens2.bwd (p, lens1.fwd0 s, b)
            s' = lens1.bwd0 (s, a')
        in (p', s')

-- Product of parametric lenses,
prodLens :
         PLens p s a ->
         PLens p' s' a' ->
         PLens (p, p') (s, s') (a, a')
         -- lens1.fwd : (p, s) -> a
         -- lens1.bwd : (p, s, a) -> (p, s)
prodLens lens1 lens2 =
    MkPLens fwdProd bwdProd
  where
    fwdProd : ((p, p'), (s, s')) -> (a, a')
    fwdProd ((p, p'), (s, s')) = (lens1.fwd (p, s), lens2.fwd (p', s'))

    bwdProd : ((p, p'), (s, s'), (a, a')) -> ((p, p'), (s, s'))
    bwdProd ((p, p'), (s, s'), (a, a')) =
       let (q, t)   = lens1.bwd (p, s, a)
           (q', t') = lens2.bwd (p', s', a')
       in ((q, q'), (t, t'))

-- duplicate a lens in parallel n+1 times
export
vecLens : (n : Nat) -> PLens p s a -> PLens (Vect n p) (Vect n s) (Vect n a)
vecLens Z _ = MkPLens (\(Nil, Nil) => Nil) (\(Nil, Nil, Nil) => (Nil, Nil))
vecLens (S n) lns = MkPLens fwd' bwd'
  where
    lnsN : PLens (Vect n p) (Vect n s) (Vect n a)
    lnsN = vecLens n lns
    fwd' : (Vect (S n) p, Vect (S n) s) -> Vect (S n) a
    fwd' (p :: ps, s :: ss) = lns.fwd (p, s) :: lnsN.fwd (ps, ss)
    bwd' : (Vect (S n) p, Vect (S n) s, Vect (S n) a) -> (Vect (S n) p, Vect (S n) s)
    bwd' (p :: ps, s :: ss, a :: as) =
          let (p', s')   = lns.bwd (p, s, a)
              (ps', ss') = lnsN.bwd (ps, ss, as)
          in (p' :: ps', s' :: ss')

-- A branching combinator
export
branch : Monoid s => (n : Nat) -> Lens s (Vect n s)
branch n = MkLens (replicate n) (\(_, ss) => concat ss) -- pointwise <+>

-- Batch n lenses in parallel sharing the same parameters
-- input and output are n-tupled, parameters are collected
batch :  Monoid p =>
         (n : Nat) ->
         PLens p s a ->
         PLens p (Vect n s) (Vect n a)
batch n lns =
    MkPLens fwdB bwdB
  where
    fwdB : (p, Vect n s) -> Vect n a
    fwdB (p, ss) =  map lns.fwd (zip (replicate n p) ss)
    bwdB : (p, Vect n s, Vect n a) -> (p, Vect n s)
    bwdB (p, ss, as) =
       let (ps', ss') = unzip $ map lns.bwd $ zip3 (replicate n p) ss as
       in (concat ps', ss')



-- xs = [1, 2, 3, 4, 5, 6]
-- vw = [[1, 2, 3], [4, 5, 6]]  m=3 n=2
export
rechunk : (m : Nat) -> (n : Nat) -> Vect (n * m) a -> Vect n (Vect m a)
rechunk m Z  xs  = []
rechunk m (S k) xs  = take m xs :: rechunk m k (drop m xs)

-- A connector lens, flattens a mxn array
export
flatten : {m : Nat} -> {n : Nat} -> Lens (Vect n (Vect m s)) (Vect (n * m) s)
flatten = MkLens fwd' bwd'
  where
    fwd' : Vect n (Vect m s) -> Vect (n*m) s
    fwd' vs = concat vs
    bwd' : {m : Nat} -> {n : Nat} -> (Vect n (Vect m s), Vect (n*m) s) -> (Vect n (Vect m s))
    bwd' {m} {n} (vs, w) = (rechunk m n w)

-- Batches n identical neural networks sharing the same parameters
-- Use it for batch training
export
batchN :  (n : Nat) ->
         (Vect n p -> p) ->
         PLens p s a ->
         PLens p (Vect n s) (Vect n a)
batchN n collectP lns =
    MkPLens fwdB bckB
  where
    fwdB : (p, Vect n s) -> Vect n a
    fwdB (p, ss) =  map lns.fwd (zip (replicate n p) ss)
    bckB : (p, Vect n s, Vect n a) -> (p, Vect n s)
    bckB (p, ss, as) =
       let (ps', ss') = unzip $ map lns.bwd $ zip3 (replicate n p) ss as
       in (collectP ps', ss')

-- Produce a singleton vector
export
single : Lens s (Vect 1 s)
single = MkLens fwd bwd
  where
    fwd : s -> Vect 1 s
    fwd s = [s]
    bwd : (s, Vect 1 s) -> s
    bwd (_, [s]) = s
