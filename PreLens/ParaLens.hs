module ParaLens where
import Data.Bifunctor ( Bifunctor(second, first, bimap) )

-- Parametric lenses and BiTambara modules

-- Parametric lens, get/set or forward/backward representation
data PLens a da p dp s ds = 
  PLens { fwd' :: (p, s) -> a
        , bwd' :: (p, s, da) -> (dp, ds)
        } 

-- Existential representation of parametic lens
data ExLens a da p dp s ds = 
  forall m . ExLens ((p, s)  -> (m, a))  
                    ((m, da) -> (dp, ds))

-- Accessors
fwd :: ExLens a da p dp s ds -> (p, s) -> a
fwd (ExLens f g) (p, s) = snd $ f (p, s)

bwd :: ExLens a da p dp s ds -> (p, s, da) -> (dp, ds)
bwd (ExLens f g) (p, s, da) = g (fst (f (p, s)), da)

-- Serial composition
compose ::
    ExLens  a da p dp s ds -> ExLens b db q dq a da ->
    ExLens   b db (p, q) (dp, dq) s ds
compose (ExLens f1 g1) (ExLens f2 g2) = ExLens f3 g3
  where
    f3 ((p, q), s) =
      let (m, a) = f1 (p, s)
          (n, b) = f2 (q, a)
      in ((m, n), b)
    g3 ((m, n), db) =
      let (dq, da) = g2 (n, db)
          (dp, ds) = g1 (m, da)
      in ((dp, dq), ds)

identityLens :: ExLens a da () () a da
identityLens = ExLens id id

-- Parallel composition 

-- A pair of lenses in parallel
prodLens ::
    ExLens a da p dp s ds -> ExLens a' da' p' dp' s' ds' ->
    ExLens (a, a') (da, da') (p, p') (dp, dp') (s, s') (ds, ds')
prodLens (ExLens f1 g1) (ExLens f2 g2) = ExLens  f3 g3
  where
    f3 ((p, p'), (s, s')) = ((m, m'), (a, a'))
      where (m, a)   = f1 (p, s)
            (m', a') = f2 (p', s')
    g3 ((m, m'), (da, da')) = ((dp, dp'), (ds, ds'))
      where
        (dp, ds)   = g1 (m, da)
        (dp', ds') = g2 (m', da')

-- van Laarhoven representation of parametric lens
-- Not very useful, as it doesn't compose nicely
type VanL a da p dp s ds = forall f. Functor f => 
  (a -> f da) -> (p, s) -> f (dp, ds)

type ParaLens a da p dp s ds = (p, s) -> (da -> (dp, ds), a)

toVLL :: ParaLens a da p dp s ds -> VanL a da p dp s ds
toVLL para f = fmap (uncurry ($)) . strength . second f . para

fromVLL :: VanL a da p dp s ds -> ParaLens a da p dp s ds
fromVLL vll = unF . vll (curry MkF id)

newtype F a da x = MkF { unF :: (da -> x, a) }
  deriving Functor

-- Profunctor representation

-- As a reminder, this is the vanilla Tambara module
class Profunctor p where
  dimapVanilla :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

class  Profunctor p => Tambara p where
  alphaVanilla :: forall a da m. p a da -> p (m, a) (m, da)
--

class BiProfunctor p where
    dimap  :: (a' -> a) -> (b -> b') -> p q q' a b -> p q q' a' b'
    dimap' :: (r -> q) -> (q' -> r') -> p q q' a b -> p r r' a b

-- Parametric version of Tambara module
class  BiProfunctor p => BiTambara p where
    alpha :: p q q' a da -> p q q' (m, a) (m, da)
    beta  :: p r r' (q, s) (q', ds) -> p (r, q) (r', q') s ds

-- Profunctor representation of a parametric lens
type BiLens q q' s ds a da =
    forall p. BiTambara p => forall r r'. p r r' a da -> p (r, q) (r', q') s ds

-- Existential lens is an example of a BiTambara module
instance BiProfunctor (ExLens a da) where
    dimap :: (s' -> s) -> (ds -> ds') -> ExLens a da q q' s ds -> ExLens a da q q' s' ds'
    dimap f g (ExLens fw bw) = ExLens fw' bw'
      where fw' (q, s') = fw (q, f s')
            bw' (m, da) = second g (bw (m, da))
    dimap' :: (r -> q) -> (q' -> r') -> ExLens a da q q' s ds -> ExLens a da r r' s ds
    dimap' f g (ExLens fw bw) = ExLens fw' bw'
      where 
        fw' (r, s) = fw (f r, s)
        bw' (m, da) = first g $ bw (m, da)

instance BiTambara (ExLens a da) where
    alpha :: ExLens a da q q' s ds -> ExLens a da q q' (n, s) (n, ds)
    alpha (ExLens fw bw) = ExLens fw' bw'
      where fw' (q, (n, s)) = first (n,) $ fw (q, s) -- use (n, m) as residue
            bw' ((n, m), da) = second (n,) (bw (m, da))

    beta :: ExLens a da r r' (q, s) (q', ds) -> ExLens a da (r, q) (r', q') s ds
    beta (ExLens fw bw) = ExLens fw' bw' 
      where fw' ((r, q), s) = fw (r, (q, s))
            bw' (m, da) =  let (r', (q', ds)) = bw (m, da)
                           in ((r', q'), ds)

fromTamb :: BiLens q q' s ds a da -> ExLens a da q q' s ds
fromTamb pab_pst = dimap' unLunit lunit $ pab_pst identityLens 

lunit  :: ((), a) -> a
lunit ((), a) = a
unLunit :: a -> ((), a)
unLunit a = ((), a)

-- Conversion from ExLens to BiLens
toTamb :: ExLens a da q q' s ds -> BiLens q q' s ds a da
toTamb (ExLens fw bw) = beta . dimap fw bw . alpha

strength :: Functor f => (a, f b) -> f (a, b)
strength (a, fb) = fmap (a,) fb
