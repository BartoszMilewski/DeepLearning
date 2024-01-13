module Tambara where
import PreLens
import Data.Bifunctor ( Bifunctor(second, first, bimap) )

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
