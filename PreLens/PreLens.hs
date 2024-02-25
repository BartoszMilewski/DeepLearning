module PreLens where
import Data.Bifunctor ( Bifunctor(second, first, bimap) )

-- Pre-lens, uses 4 monoidal actions parameterized by m dm and p dp
-- Pre-lens category has objects <a, da> <s, ds>, etc.
-- Pre-lenses are morphism from <s, ds> to <a, da> 

data PreLens a da m dm p dp s ds =
  PreLens ((p, s)   -> (m, a))
          ((dm, da) -> (dp, ds))

-- Pre-lenses are composable
preCompose ::
    PreLens a' da' m dm p dp s ds -> 
    PreLens a da n dn q dq a' da' ->
    PreLens a da (m, n) (dm, dn) (q, p) (dq, dp) s ds
preCompose (PreLens f1 g1) (PreLens f2 g2) = PreLens f3 g3
  where
    f3 = unAssoc . second f2 . assoc . first sym . unAssoc . second f1 . assoc
    g3 = unAssoc . second g1 . assoc . first sym . unAssoc . second g2 . assoc
{- or more verbose:
    f3 ((q, p), s) =
      let (m, a) = f1 (p, s)
          (n, b) = f2 (q, a)
      in ((m, n), b)
    g3 ((dm, dn), db) =
      let (dq, da) = g2 (dn, db)
          (dp, ds) = g1 (dm, da)
      in ((dq, dp), ds)
-}

idPreLens :: PreLens a da () () () () a da
idPreLens = PreLens id id


-- Parallel composition 

-- A pair of lenses in parallel
prodLens ::
    PreLens a da m dm p dp s ds -> PreLens a' da' m' dm' p' dp' s' ds' ->
    PreLens (a, a') (da, da') (m, m') (dm, dm') (p, p') (dp, dp') (s, s') (ds, ds')
prodLens (PreLens f1 g1) (PreLens f2 g2) = PreLens  f3 g3
  where
    f3 ((p, p'), (s, s')) = ((m, m'), (a, a'))
      where (m, a)   = f1 (p, s)
            (m', a') = f2 (p', s')
    g3 ((dm, dm'), (da, da')) = ((dp, dp'), (ds, ds'))
      where
        (dp, ds)   = g1 (dm, da)
        (dp', ds') = g2 (dm', da')

-- An existential lens is a trace over m of a PreLens
-- The tracing can be done after all the compositions

data ExLens a da p dp s ds = forall m. ExLens (PreLens a da m m p dp s ds)

-- Extractors for an existential lens
fwd' :: ExLens a da p dp s ds -> (p, s) -> a
fwd' (ExLens (PreLens f b)) = snd . f
bwd' :: ExLens a da p dp s ds -> (p, s, da) -> (dp, ds)
bwd' (ExLens (PreLens f b)) (p, s, da) = b (fst (f (p, s)), da)

-- Composition of existential lenses follows
-- the composition of pre-lenses
composeL ::
    ExLens a da p dp s ds -> ExLens b db q dq a da ->
    ExLens  b db (q, p) (dq, dp) s ds
composeL (ExLens pl) (ExLens pl') = ExLens $ preCompose pl pl'

-- Combining the two extractors into one function

type ParaLens a da p dp s ds = (p, s) -> (da -> (dp, ds), a)

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

skipLeft :: ((a, b), x) -> ((a, x), b)
skipLeft ((a, b), x) = ((a, x), b)
