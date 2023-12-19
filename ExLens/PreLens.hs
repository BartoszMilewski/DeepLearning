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



-- A profunctor in three pairs of arguments (Notice: the polarities of m dm are flipped)
class TriProFunctor t where
    dimap   :: (s' -> s) -> (ds -> ds') -> t m dm p dp s ds -> t m  dm  p  dp  s' ds'
    dimapp  :: (p' -> p) -> (dp -> dp') -> t m dm p dp s ds -> t m  dm  p' dp' s  ds
    dimapm  :: (m -> m') -> (dm' -> dm) -> t m dm p dp s ds -> t m' dm' p  dp  s  ds

-- PreLens is a profunctor in three pairs of arguments
instance TriProFunctor (PreLens a da) where
     dimap f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p, s') = fw (p, f s')
             bw' (dm, da) = second g $ bw (dm, da)
     dimapp f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p', s) = fw (f p', s)
             bw' (dm, da) = first g $ bw (dm, da)
     dimapm f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p, s) = first f $ fw (p, s)
             bw' (dm', da) = bw (g dm', da)

-- A generalization of Tambara modules with three pairs of arguments
class TriProFunctor t => Trimbara t where
    -- shorthand: alpha :: m p s -> (m1, m) p (m1, s)
    alpha :: t m dm p dp s ds -> t (m1, m) (dm1, dm) p dp (m1, s) (dm1, ds)
    -- shorthand: beta  :: m p (p1, s) -> m (p, p1) s
    beta  :: t m dm p dp (p1, s) (dp1, ds) -> t m dm (p, p1) (dp, dp1) s ds

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
----------
-- This function polymorphic in Trimbara modules is equivalent to a PreLens
-- shorthand: m1 p1 a -> (m, m1) (p1, p) s
----------
type TriLens a da m dm p dp s ds =
    forall t. Trimbara t => forall p1 dp1 m1 dm1. 
      t m1 dm1 p1 dp1 a da -> t (m, m1) (dm, dm1) (p1, p) (dp1, dp) s ds

-- n r a   -> (m, n)(r, p) s
-- () () a -> (m, ()) ((), p) s
fromTamb :: forall a da m dm p dp s ds .
  TriLens a da m dm p dp s ds -> PreLens a da m dm p dp s ds
fromTamb pab_pst = dimapm runit runit_1 $ 
                   dimapp lunit_1 lunit $ 
                   pab_pst idPreLens 

toTamb :: PreLens a da m dm p dp s ds -> TriLens a da m dm p dp s ds
-- want  :: m1 p1 a -> (m, m1) (p1, p) s
-- alpha :: m1 p1 a -> (m, m1) p1 (m, a)
-- dimap fw bw :: ->   (m, m1) p1 (p, s)
-- beta  ::       ->   (m, m1) (p1, p) s
toTamb (PreLens fw bw) = beta . dimap fw bw . alpha

triCompose ::
    TriLens a da m dm p dp s ds -> 
    TriLens b db n dn q dq a da ->
    TriLens b db (m, n) (dm, dn) (q, p) (dq, dp) s ds
-- lba :: m1 p1 b -> (n, m1) (p1, q) a
-- las :: (n, m1) (p1, q) a -> (m, (n, m1)) ((p1, q), p) s
-- lbs :: m1 p1 b -> ((m, n), m1) (p1, (q, p)) s
-- dimapp :: (p' -> p) -> (dp -> dp') -> m p s -> m  p' s
-- dimapm :: (m -> m') -> (dm' -> dm) -> m p s -> m' p  s
-- las . lba :: m1 p1 b -> (m, (n, m1)) ((p1, q), p) s
triCompose las lba = dimapp assoc_1 assoc . 
                     dimapm assoc_1 assoc . 
                     las . lba

-- Parallel product of TriLenses

-- Show that a TriTambara of products is a TriTambara in both sides of the product

-- Rearrange the wires for Haskell
newtype PRight t m dm p dp s ds m' dm' p' dp' s' ds' = PRight { 
  unPRight :: t (m, m') (dm, dm') (p, p') (dp, dp') (s, s') (ds, ds') }

-- It's a TriProfunctor in these variables
instance (TriProFunctor t) => TriProFunctor (PRight t m dm p dp s ds) where
    dimap f g (PRight t)  = PRight $ dimap  (second f) (second g) t 
    dimapp f g (PRight t) = PRight $ dimapp (second f) (second g) t
    dimapm f g (PRight t) = PRight $ dimapm (second f) (second g) t

-- It's a TriTambara in thes variables
instance (Trimbara t) => Trimbara (PRight t m dm p dp s ds) where
    -- alpha :: m p s -> (m1, m) p (m1, s)
    -- need  :: (m, m')  (p, p') (s, s') -> 
    --          (m, (m1, m')) (p, p') (s, (m1, s'))
    alpha = PRight . 
        dimap (\(s, (m1, s')) -> (m1, (s, s')))
              (\(dm1, (ds, ds')) -> (ds, (dm1, ds'))) .
        dimapm (\(m1, (m, m'))->(m, (m1, m'))) 
               (\(dm, (dm1, dm'))-> (dm1, (dm, dm'))) . 
        alpha .  --  (m1, (m, m')) (p, p') (m1, (s, s'))
        unPRight --   (m, m')      (p, p')      (s, s')

    -- beta  :: m p (p1, s) -> m (p, p1) s
    -- need  :: (m, m') (p, p') (s, (p1, s')) -> (m, m') ((p, (p', p1)) (s, s')
    beta = PRight .
      dimapp (\(p, (p', p1)) -> ((p, p'), p1))  
             (\((dp, dp'), dp1) -> (dp, (dp', dp1))) .
      beta . -- (m, m') ((p, p'), p1) (s, s')
      dimap (\(p1, (s, s')) -> (s, (p1, s'))) 
            (\(s, (dp1, s')) -> (dp1, (s, s'))) . -- (m, m') (p, p') (p1, (s, s'))
      unPRight -- (m, m') (p, p') (s, (p1, s'))

newtype PLeft t m' dm' p' dp' s' ds' m dm p dp s ds = PLeft { 
  unPLeft :: t (m, m') (dm, dm') (p, p') (dp, dp') (s, s') (ds, ds') }

-- It's a TriProfunctor in these variables
instance (TriProFunctor t) => TriProFunctor (PLeft t m dm p dp s ds) where
    dimap f g (PLeft t)  = PLeft $ dimap (first f) (first g) t 
    dimapp f g (PLeft t) = PLeft $ dimapp (first f) (first g) t
    dimapm f g (PLeft t) = PLeft $ dimapm (first f) (first g) t

-- It's a TriTambara in these variables
instance (Trimbara t) => Trimbara (PLeft t m dm p dp s ds) where
    -- alpha :: m p s -> (m1, m) p (m1, s)
    -- need  :: (m, m')  (p, p') (s, s') -> 
    --          ((m1, m), m') (p, p') ((m1, s), s')
    alpha = PLeft .
        dimap (\((m1, s), s') -> (m1, (s, s')))
              (\(dm1, (ds, ds')) -> ((dm1, ds), ds')) .
        dimapm  (\(m1, (m, m'))->((m1, m), m')) 
                (\((dm1, dm), dm')-> (dm1, (dm, dm'))) . 
                alpha . -- (m1, (m, m')) (p, p') (m1, (s, s'))
                unPLeft -- (m, m') (p, p') (s, s')
    -- beta :: m p (p1, s) -> m (p, p1) s
    -- need :: (m, m') (p, p') ((p1, s), s') -> (m, m') ((p, p1), p') (s, s')
    beta = PLeft .
      dimapp (\((p, p1), p') -> ((p, p'), p1))  
             (\((dp, dp'), dp1) -> ((dp, dp1), dp')) .
      beta . -- (m, m') ((p, p'), p1), (s, s')
      dimap  (\(p1, (s, s')) -> ((p1, s), s')) 
             (\((dp1, s), s') -> (dp1, (s, s'))) . -- (m, m') (p, p') (p1, (s, s'))
      unPLeft -- (m, m') (p, p') ((p1, s), s')

prodLens :: TriLens a da m dm q  dq  s  ds -> 
            TriLens a' da' m' dm' q' dq' s' ds' ->
            TriLens (a, a') (da, da') (m, m') (dm, dm') (q, q') (dq, dq') (s, s') (ds, ds')
    -- l1 :: t1 m1 r1 a  -> t1 (m, m1)  (r1, q)  s
    -- l2 :: t2 m2 r2 a' -> t2 (m', m2) (r2, q') s'
    -- l3 :: t  m3            r3           (a, a') -> 
    --       t ((m, m'), m3) (r3, (q, q')) (s, s')
prodLens l1 l2 = 
    dimapp assoc_1 assoc . 
    dimapm assoc_1 assoc . 
    dimapp (second lunit_1) (second lunit) .
    dimapm (first runit) (first runit_1) .
    unPRight . l2 . PRight . unPLeft . l1 . PLeft .
    dimapp runit runit_1 .
    dimapm lunit_1 lunit

-- Monoidal category structure maps
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

preNeuron :: PreLens D D (((V, V), ()), D) (((V, V), ()), D) (D, V) (D, V) V V
preNeuron = dimapp lunit_1 lunit (fromTamb neuronT)

affine :: ExLens D D (D, V) (D, V) V V
affine = ExLens preAffine 

neuron :: ExLens D D (D, V) (D, V) V V
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
    print $ fwd neuron ( (0.01, [-0.1, 0.1]), [2, 30])
    putStrLn "backward neuron"
    print $ bwd neuron ( (0.1, [1.3, -1.4]), [0.21, 0.33], 1)
