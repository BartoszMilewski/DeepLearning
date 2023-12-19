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
    -- f3 = unAssoc . second f2 . assoc . first sym . unAssoc . second f1 . assoc
    -- g3 = unAssoc . second g1 . assoc . first sym . unAssoc . second g2 . assoc
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
    dimapS  :: (s' -> s) -> (ds -> ds') -> t m dm p dp s ds -> t m  dm  p  dp  s' ds'
    dimapP  :: (p' -> p) -> (dp -> dp') -> t m dm p dp s ds -> t m  dm  p' dp' s  ds
    dimapM  :: (m -> m') -> (dm' -> dm) -> t m dm p dp s ds -> t m' dm' p  dp  s  ds

-- PreLens is a profunctor in three pairs of arguments
instance TriProFunctor (PreLens a da) where
     dimapS f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p, s') = fw (p, f s')
             bw' (dm, da) = second g $ bw (dm, da)
     dimapP f g (PreLens fw bw) = PreLens fw' bw'
       where fw' (p', s) = fw (f p', s)
             bw' (dm, da) = first g $ bw (dm, da)
     dimapM f g (PreLens fw bw) = PreLens fw' bw'
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
fromTamb pab_pst = dimapM runit unRunit $ 
                   dimapP unLunit lunit $ 
                   pab_pst idPreLens 

toTamb :: PreLens a da m dm p dp s ds -> TriLens a da m dm p dp s ds
-- want  :: m1 p1 a -> (m, m1) (p1, p) s
-- alpha :: m1 p1 a -> (m, m1) p1 (m, a)
-- dimapS fw bw :: ->   (m, m1) p1 (p, s)
-- beta  ::       ->   (m, m1) (p1, p) s
toTamb (PreLens fw bw) = beta . dimapS fw bw . alpha

triCompose ::
    TriLens a da m dm p dp s ds -> 
    TriLens b db n dn q dq a da ->
    TriLens b db (m, n) (dm, dn) (q, p) (dq, dp) s ds
-- lba :: m1 p1 b -> (n, m1) (p1, q) a
-- las :: (n, m1) (p1, q) a -> (m, (n, m1)) ((p1, q), p) s
-- lbs :: m1 p1 b -> ((m, n), m1) (p1, (q, p)) s
-- dimapP :: (p' -> p) -> (dp -> dp') -> m p s -> m  p' s
-- dimapM :: (m -> m') -> (dm' -> dm) -> m p s -> m' p  s
-- las . lba :: m1 p1 b -> (m, (n, m1)) ((p1, q), p) s
triCompose las lba = dimapP unAssoc assoc . 
                     dimapM unAssoc assoc . 
                     las . lba

-- Parallel product of TriLenses

-- Show that a TriTambara of products is a TriTambara in both sides of the product

-- Rearrange the wires for Haskell
newtype PRight t m dm p dp s ds m' dm' p' dp' s' ds' = PRight { 
  unPRight :: t (m, m') (dm, dm') (p, p') (dp, dp') (s, s') (ds, ds') }

-- It's a TriProfunctor in these variables
instance (TriProFunctor t) => TriProFunctor (PRight t m dm p dp s ds) where
    dimapS f g (PRight t) = PRight $ dimapS  (second f) (second g) t 
    dimapP f g (PRight t) = PRight $ dimapP (second f) (second g) t
    dimapM f g (PRight t) = PRight $ dimapM (second f) (second g) t

-- It's a TriTambara in thes variables
instance (Trimbara t) => Trimbara (PRight t m dm p dp s ds) where
    -- alpha :: m p s -> (m1, m) p (m1, s)
    -- need  :: (m, m')  (p, p') (s, s') -> 
    --          (m, (m1, m')) (p, p') (s, (m1, s'))
    alpha = PRight . 
        dimapS skipRight unSkipRight .
        dimapM skipRight unSkipRight . 
        alpha .  --  (m1, (m, m')) (p, p') (m1, (s, s'))
        unPRight --   (m, m')      (p, p')      (s, s')

    -- beta  :: m p (p1, s) -> m (p, p1) s
    -- need  :: (m, m') (p, p') (s, (p1, s')) -> (m, m') ((p, (p', p1)) (s, s')
    beta = PRight .
      dimapP unAssoc assoc .
      beta . -- (m, m') ((p, p'), p1) (s, s')
      dimapS skipRight unSkipRight . -- (m, m') (p, p') (p1, (s, s'))
      unPRight -- (m, m') (p, p') (s, (p1, s'))

newtype PLeft t m' dm' p' dp' s' ds' m dm p dp s ds = PLeft { 
  unPLeft :: t (m, m') (dm, dm') (p, p') (dp, dp') (s, s') (ds, ds') }

-- It's a TriProfunctor in these variables
instance (TriProFunctor t) => TriProFunctor (PLeft t m dm p dp s ds) where
    dimapS f g (PLeft t) = PLeft $ dimapS (first f) (first g) t 
    dimapP f g (PLeft t) = PLeft $ dimapP (first f) (first g) t
    dimapM f g (PLeft t) = PLeft $ dimapM (first f) (first g) t

-- It's a TriTambara in these variables
instance (Trimbara t) => Trimbara (PLeft t m dm p dp s ds) where
    -- alpha :: m p s -> (m1, m) p (m1, s)
    -- need  :: (m, m')  (p, p') (s, s') -> 
    --          ((m1, m), m') (p, p') ((m1, s), s')
    alpha = PLeft .
        dimapS assoc unAssoc .
        dimapM  unAssoc assoc . 
                alpha . -- (m1, (m, m')) (p, p') (m1, (s, s'))
                unPLeft -- (m, m') (p, p') (s, s')
    -- beta :: m p (p1, s) -> m (p, p1) s
    -- need :: (m, m') (p, p') ((p1, s), s') -> (m, m') ((p, p1), p') (s, s')
    beta = PLeft .
      dimapP skipLeft unSkipLeft .
      beta . -- (m, m') ((p, p'), p1), (s, s')
      dimapS unAssoc assoc . -- (m, m') (p, p') (p1, (s, s'))
      unPLeft -- (m, m') (p, p') ((p1, s), s')

prodLens :: TriLens a da m dm q  dq  s  ds -> 
            TriLens a' da' m' dm' q' dq' s' ds' ->
            TriLens (a, a') (da, da') (m, m') (dm, dm') (q, q') (dq, dq') (s, s') (ds, ds')
    -- l1 :: t1 m1 r1 a  -> t1 (m, m1)  (r1, q)  s
    -- l2 :: t2 m2 r2 a' -> t2 (m', m2) (r2, q') s'
    -- l3 :: t  m3            r3           (a, a') -> 
    --       t ((m, m'), m3) (r3, (q, q')) (s, s')
prodLens l1 l2 = 
    dimapP unAssoc assoc . 
    dimapM unAssoc assoc . 
    dimapP (second unLunit) (second lunit) .
    dimapM (first runit) (first unRunit) .
    unPRight . l2 . PRight . unPLeft . l1 . PLeft .
    dimapP runit unRunit .
    dimapM unLunit lunit

-- Monoidal category structure maps
lunit  :: ((), a) -> a
lunit ((), a) = a
unLunit :: a -> ((), a)
unLunit a = ((), a)
runit  :: (a, ()) -> a
runit (a, ()) = a
unRunit :: a -> (a, ())
unRunit a = (a, ())

assoc :: ((a, b), c) -> (a, (b, c))
assoc ((a, b), c) = (a, (b, c))
unAssoc :: (a, (b, c)) -> ((a, b), c)
unAssoc (a, (b, c))= ((a, b), c)

-- Symmetric monoidal structure maps

sym :: (a, b) -> (b, a)
sym (a, b) = (b, a)

skipRight :: (x, (b, c)) -> (b, (x, c))
skipRight (x, (b, c)) = (b, (x, c))

unSkipRight :: (b, (x, c)) -> (x, (b, c))
unSkipRight (b, (x, c)) = (x, (b, c))

skipLeft :: ((a, b), x) -> ((a, x), b)
skipLeft ((a, b), x) = ((a, x), b)

unSkipLeft :: ((a, x), b) -> ((a, b), x)
unSkipLeft ((a, x), b) = ((a, b), x)
