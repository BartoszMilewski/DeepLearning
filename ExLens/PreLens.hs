{-# language ScopedTypeVariables #-}
module PreLens where
import Data.Bifunctor ( Bifunctor(second, first, bimap) )

-- Pre-lens, parameterized by 4 monoidal actions m dm and p dp
-- Pre-lens category has objects <s, ds>, etc.
-- Pre-lenses are morphism from <s, ds> to <a, da> 

data PreLens a da m dm p dp s ds =
  PreLens ((p, s)   -> (m, a))
          ((dm, da) -> (dp, ds))

-- Pre-lenses are composable
preCompose ::
    PreLens a da m dm p dp s ds -> PreLens b db n dn q dq a da ->
    PreLens b db (m, n) (dm, dn) (q, p) (dq, dp) s ds
preCompose (PreLens f1 g1) (PreLens f2 g2) = PreLens f3 g3
  where
    -- f3 = assoc_1 . second f2 . assoc . first sym . assoc_1 . second f1 . assoc
    -- g3 = assoc_1 . second g1 . assoc . first sym . assoc_1 . second g2 . assoc
    f3 ((q, p), s) =
      let (m, a) = f1 (p, s)
          (n, b) = f2 (q, a)
      in ((m, n), b)
    g3 ((dm, dn), db) =
      let (dq, da) = g2 (dn, db)
          (dp, ds) = g1 (dm, da)
      in ((dq, dp), ds)

idPreLens :: PreLens a da () () () () a da
idPreLens = PreLens id id

-- Existential lens is a "trace" of a pre-lens
data ExLens a da p dp s ds = forall m. ExLens (PreLens a da m m p dp s ds)

-- Composition of existential lenses follows
-- the composition of pre-lenses
compose ::
    ExLens a da p dp s ds -> ExLens b db q dq a da ->
    ExLens  b db (q, p) (dq, dp) s ds
compose (ExLens pl) (ExLens pl') = ExLens $ preCompose pl pl'

-- A profunctor in three pairs of arguments
class TriProFunctor t where
    dimap   :: (s' -> s) -> (ds -> ds') -> t m dm p dp s ds -> t m  dm  p  dp  s' ds'
    dimap'  :: (p' -> p) -> (dp -> dp') -> t m dm p dp s ds -> t m  dm  p' dp' s  ds
    dimap'' :: (m -> m') -> (dm' -> dm) -> t m dm p dp s ds -> t m' dm' p  dp  s  ds

-- PreLens is a profunctor in three pairs of arguments
instance TriProFunctor (PreLens a da) where
     dimap f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p, s') = fw (p, f s')
             bw' (dm, da) = second g $ bw (dm, da)
     dimap' f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p', s) = fw (f p', s)
             bw' (dm, da) = first g $ bw (dm, da)
     dimap'' f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p, s) = first f $ fw (p, s)
             bw' (dm', da) = bw (g dm', da)

-- A generalization of Tambara modules with three pairs of arguments
class TriProFunctor t => Trimbara t where
    alpha :: t m dm p dp s ds -> t (n, m) (dn, dm) p dp (n, s) (dn, ds)
    beta  :: t m dm p dp (r, s) (dr, ds) -> t m dm (p, r) (dp, dr) s ds

-- PreLens is an example of such a Tambara module
instance Trimbara (PreLens a da) where
    -- fw :: (p, s)   -> (m, a)
    -- bw :: (dm, da) -> (dp, ds)
    alpha :: PreLens a da m dm p dp s ds -> PreLens a da (n, m) (dn, dm) p dp (n, s) (dn, ds)
    alpha (PreLens fw bw) = PreLens fw' bw'
      where
        --fw' :: (p, (n, s)) -> ((n, m)), a)
        fw' (p, (n, s)) = let (m, a) = fw (p, s)
                          in ((n, m), a)
        --bw' :: ((dn, dm), da) -> (dp, (dn, ds))
        bw' ((dn, dm), da) = let (dp, ds) = bw (dm, da)
                             in (dp, (dn, ds))

    beta :: forall m dm p dp s ds a da r dr .
      PreLens a da m dm p dp (r, s) (dr, ds) -> PreLens a da m dm (p, r) (dp, dr) s ds
    -- fw :: (p, (r, s))   -> (m, a)
    -- bw :: (dm, da) -> (dp, (dr, ds))
    beta (PreLens fw bw) = PreLens fw' bw'
      where
        fw' :: ((p, r), s) -> (m, a)
        fw' ((p, r), s) = let (m, a) = fw (p, (r, s))
                        in (m, a)
        bw' :: (dm, da) -> ((dp, dr), ds)
        bw' (dm, da) = let (dp, (dr, ds)) = bw (dm, da)
                    in ((dp, dr), ds)

-- type BiLens p dp s ds a da =
--     forall t. BiTambara t => forall r dr. 
--       t r dr a da -> t (r, p) (dr, dp) s ds

-- This function polymorphic in Trimbara modules is equivalent to a PreLens
type TriLens a da m dm p dp s ds =
    forall t. Trimbara t => forall r dr n dn. 
      t n dn r dr a da -> t (m, n) (dm, dn) (r, p) (dr, dp) s ds

-- t n dn r dr a da -> t (m, n) (dm, dn) (r, p) (dr, dp) s ds
-- t () () () () a da -> t (m, ()) (dm, ()) ((), p) ((), dp) s ds
fromTamb :: forall a da m dm p dp s ds .
  TriLens a da m dm p dp s ds -> PreLens a da m dm p dp s ds
fromTamb pab_pst = dimap'' runit runit_1 $ dimap' lunit_1 lunit $ pab_pst idPreLens 

toTamb :: PreLens a da m dm p dp s ds -> TriLens a da m dm p dp s ds
-- n dn r dr a da -> (n, m) (dn, dm) (r, p) (dr, dp) s ds
-- alpha :: n dn r dr a da -> (n, m) (dn, dm) r dr (m, a) (dm, da)
-- dimap fw bw :: (n, m) (dn, dm) r dr (p, s) (dp, ds)
-- beta :: (n, m) (dn, dm) (r, p) (dr, dp) s ds
toTamb (PreLens fw bw) = beta . dimap fw bw . alpha


triCompose ::
    TriLens a da m dm p dp s ds -> 
    TriLens b db n dn q dq a da ->
    TriLens b db (m, n) (dm, dn) (q, p) (dq, dp) s ds
-- lba :: n' dn' r dr b db -> (n, n') (dn, dn') (r, q) (dr, dq) a da
-- las :: (n, n') (dn, dn') (r, q) (dr, dq) a da -> (m, (n, n')) (dm, (dn, dn')) ((r, q), p) ((dr, dq), dp) s ds
-- lbs :: n' dn' r dr b db -> ((m, n), n') ((dm, dn), dn') (r, (q, p)) (dr, (dq, dp)) s ds
-- dimap'  :: (p' -> p) -> (dp -> dp') -> t m dm p dp s ds -> t m  dm  p' dp' s  ds
-- dimap'' :: (m -> m') -> (dm' -> dm) -> t m dm p dp s ds -> t m' dm' p  dp  s  ds
-- (m, (n, n')) (dm, (dn, dn')) ((r, q), p) ((dr, dq), dp) s ds ->
-- ((m, n), n') ((dm, dn), dn') (r, (q, p)) (dr, (dq, dp)) s ds
triCompose las lba = dimap' assoc_1 assoc . dimap'' assoc_1 assoc . las . lba

lunit_1 q = ((), q)
lunit  :: ((), q) -> q
lunit ((), q) = q
runit_1 :: q -> (q, ())
runit_1 q = (q, ())
runit  :: (q, ()) -> q
runit (q, ()) = q

assoc :: ((a, b), c) -> (a, (b, c))
assoc ((a, b), c) = (a, (b, c))
assoc_1 :: (a, (b, c)) -> ((a, b), c)
assoc_1 (a, (b, c))= ((a, b), c)

sym :: (a, b) -> (b, a)
sym (a, b) = (b, a)

-- Testing

type D = Double
-- Ideally, a counted vector
type V = [D]

-- Simple linear lens, scalar product of parameters and inputs
linearL :: PreLens D D (V, V) (V, V) V V V V
linearL = PreLens fw bw
  where
    fw :: (V, V) -> ((V, V), D)
    -- a = Sum p * s
    fw (p, s) = ((s, p), sum $ zipWith (*) p s)
    -- da/dp = s, da/ds = p
    bw :: ((V, V), D) -> (V, V)
    bw ((s, p), da) = (fmap (da *) s  -- da/dp
                      ,fmap (da *) p) -- da/ds

-- Add bias to input
biasL :: PreLens D D () () D D D D
biasL = PreLens fw bw 
  where 
    fw :: (D, D) -> ((), D)
    fw (p, s) = ((), p + s)
    -- da/dp = 1, da/ds = 1
    bw :: ((), D) -> (D, D)
    bw (_, da) = (da, da)

-- Non-linear activation lens using tanh
activ :: PreLens D D D D () () D D
activ = PreLens fw bw
  where
    -- a = tanh s
    fw (_, s) = (s, tanh s)
    -- da/ds = 1 + (tanh s)^2
    bw (s, da)= ((), da * (1 - (tanh s)^2)) -- a * da/ds

-- Convert both to TriLens
-- p V D D -> p V V V
linearT :: TriLens D D (V, V) (V, V) V V V V
linearT = toTamb linearL
-- p D D D -> p D D D
biasT :: TriLens D D () () D D D D
biasT = toTamb biasL

activT :: TriLens D D D D () () D D
activT = toTamb activ

-- Compose two TriLenses
affineT :: TriLens D D ((V, V), ()) ((V, V), ()) (D, V) (D, V) V V
affineT = triCompose linearT biasT 

-- Compose three TriLenses
neuronT :: TriLens D D (((V, V), ()), D) (((V, V), ()), D) ((), (D, V)) ((), (D, V)) V V
neuronT = triCompose (triCompose linearT biasT) activT

-- Turn the composition back to PreLens
preAffine :: PreLens D D ((V, V), ()) ((V, V), ()) (D, V) (D, V) V V
preAffine = fromTamb affineT

preNeuron :: PreLens D D (((V, V), ()), D) (((V, V), ()), D) ((), (D, V)) ((), (D, V)) V V
preNeuron = fromTamb neuronT

affine :: ExLens D D (D, V) (D, V) V V
affine = ExLens preAffine 

neuron :: ExLens D D ((), (D, V)) ((), (D, V)) V V
neuron = ExLens preNeuron

fwd :: ExLens a da q q' s ds -> (q, s) -> a
fwd (ExLens (PreLens f b)) = snd . f
bwd :: ExLens a da q q' s ds -> (q, s, da) -> (q', ds)
bwd (ExLens (PreLens f b)) (q, s, da)= b (fst (f (q, s)), da)

testTriTamb :: IO ()
testTriTamb = do
    putStrLn "forward"
    print $ fwd affine ((0.01, [-0.1, 0.1]), [2, 30])
    putStrLn "backward"
    print $ bwd affine ((0.1, [1.3, -1.4]), [0.21, 0.33], 1)

    putStrLn "forward neuron"
    print $ fwd neuron (((), (0.01, [-0.1, 0.1])), [2, 30])
    putStrLn "backward neuron"
    print $ bwd neuron (((), (0.1, [1.3, -1.4])), [0.21, 0.33], 1)
