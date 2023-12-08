{-# language ScopedTypeVariables #-}
module PreLens where
import Data.Bifunctor ( Bifunctor(second, first, bimap) )
import Control.Monad (liftM4)

-- Pre-lens, parameterized by 4 monoidal actions m dm and p dp
-- Pre-lens category has objects <s, ds>
-- Pre-lenses are morphism from <s, ds> to <a, da> 

data PreLens a da m dm p dp s ds =
  PreLens ((p, s)   -> (m, a))
          ((dm, da) -> (dp, ds))

idPreLens :: PreLens a da () () () () a da
idPreLens = PreLens id id

-- Pre-lenses are composable
preCompose ::
    PreLens a da m dm p dp s ds -> PreLens b db n dn q dq a da ->
    PreLens b db (m, n) (dm, dn) (p, q) (dp, dq) s ds
preCompose (PreLens f1 g1) (PreLens f2 g2) = PreLens f3 g3
  where
    f3 ((p, q), s) =
      let (m, a) = f1 (p, s)
          (n, b) = f2 (q, a)
      in ((m, n), b)
    g3 ((dm, dn), db) =
      let (dq, da) = g2 (dn, db)
          (dp, ds) = g1 (dm, da)
      in ((dp, dq), ds)

-- Existential lens is a "trace" of a pre-lens
data ExLens a da p dp s ds = forall m. ExLens (PreLens a da m m p dp s ds)

-- Composition of existential lenses follows
-- the composition of pre-lenses
compose ::
    ExLens a da p dp s ds -> ExLens b db q dq a da ->
    ExLens  b db (p, q) (dp, dq) s ds
compose (ExLens pl) (ExLens pl') = ExLens $ preCompose pl pl'

class TriProFunctor t where
    dimap   :: (s' -> s) -> (ds -> ds') -> t m dm p dp s ds -> t m  dm  p  dp  s' ds'
    dimap'  :: (p' -> p) -> (dp -> dp') -> t m dm p dp s ds -> t m  dm  p' dp' s  ds
    dimap'' :: (m -> m') -> (dm' -> dm) -> t m dm p dp s ds -> t m' dm' p  dp  s  ds

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

class TriProFunctor t => Trimbara t where
    alpha :: t m dm p dp s ds -> t (n, m) (dn, dm) p dp (n, s) (dn, ds)
    beta  :: t m dm p dp (r, s) (dr, ds) -> t m dm (p, r) (dp, dr) s ds

instance Trimbara (PreLens a da) where
    -- fw :: (p, s)   -> (m, a)
    -- bw :: (dm, da) -> (dp, ds)
    alpha (PreLens fw bw) = PreLens fw' bw'
      where
        --fw' :: (p, (n, s)) -> ((n, m), a)
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

type TriLens a da m dm p dp s ds =
    forall t. Trimbara t => forall r dr n dn. t n dn r dr a da -> t (n, m) (dn, dm) (r, p) (dr, dp) s ds

-- t n dn r dr a da -> t (n, m) (dn, dm) (r, p) (dr, dp) s ds
-- t () () () () a da -> t ((), m) ((), dm) ((), p) ((), dp) s ds
fromTamb :: forall a da m dm p dp s ds .
  TriLens a da m dm p dp s ds -> PreLens a da m dm p dp s ds
fromTamb pab_pst = dimap'' lunit lunit_1 $ dimap' lunit_1 lunit $ pab_pst idPreLens 

{-
-- Conversion from ExLens to BiLens
toTamb :: ExLens a da q q' s ds -> BiLens q q' s ds a da
-- p r r' a da -> p (r, q) (r', q') s ds
-- p r r' (m, a) (m, da)
-- p r r' (q, s) (q', ds)
-- p (r, q) (r', q') s ds
toTamb (ExLens fw bw) = beta . dimap fw bw . alpha

-}


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
