{-# language ScopedTypeVariables #-}
module BiTambara where
import Data.Bifunctor ( Bifunctor(second, first, bimap) )
import Data.Binary.Builder (putInt32be)

data ExLens a da q q' s ds = 
  forall m . ExLens ((q, s)  -> (m, a))  
                    ((m, da) -> (q', ds))

fwd :: ExLens a da q q' s ds -> (q, s) -> a
fwd (ExLens f b) = snd . f
bwd :: ExLens a da q q' s ds -> (q, s, da) -> (q', ds)
bwd (ExLens f b) (q, s, da)= b (fst (f (q, s)), da)

-- Profunctor representation of lens

class BiProfunctor p where
    dimap  :: (a' -> a) -> (b -> b') -> p q q' a b -> p q q' a' b'
    dimap' :: (r -> q) -> (q' -> r') -> p q q' a b -> p r r' a b

class  BiProfunctor p => BiTambara p where
    alpha :: p q q' a da -> p q q' (m, a) (m, da)
    beta  :: p r r' (q, s) (q', ds) -> p (r, q) (r', q') s ds

-- BiTambara lens
type BiLens q q' s ds a da =
    forall p. BiTambara p => forall r r'. p r r' a da -> p (r, q) (r', q') s ds

unitExLens :: ExLens a da () () a da
unitExLens = ExLens id id

instance BiProfunctor (ExLens a da) where
    dimap :: (s' -> s) -> (ds -> ds') -> ExLens a da q q' s ds -> ExLens a da q q' s' ds'
    dimap f g (ExLens fw bw) = ExLens fw' bw'
      where fw' (q, s') = fw (q, f s')
            bw' (m, da) = second g (bw (m, da))
    dimap' :: (r -> q) -> (q' -> r') -> ExLens a da q q' s ds -> ExLens a da r r' s ds
    dimap' f g (ExLens fw bw) = ExLens fw' bw'
      where 
        --fw' :: (r, s) -> (m, a)
        fw' (r, s) = fw (f r, s)
        --bw' :: (m, da) -> (r', ds)
        bw' (m, da) = first g $ bw (m, da)

instance BiTambara (ExLens a da) where
    alpha :: ExLens a da q q' s ds -> ExLens a da q q' (n, s) (n, ds)
    alpha (ExLens fw bw) = ExLens fw' bw'
      where fw' (q, (n, s)) = first (n,) $ fw (q, s) -- use (n, m) as residue
            bw' ((n, m), da) = second (n,) (bw (m, da))

    beta :: ExLens a da r r' (q, s) (q', ds) -> ExLens a da (r, q) (r', q') s ds
    beta (ExLens fw bw) = ExLens fw' bw' 
    -- fw :: (r, (q, s)) -> (m, a)
    -- bw :: (m, da) -> (r', (q', ds))
    -- fw' :: ((r, q), s) -> (m, a)
    -- bw' :: (m, da) -> ((r', q') ds)
      where fw' ((r, q), s) = fw (r, (q, s))
            bw' (m, da) =  let (r', (q', ds)) = bw (m, da)
                           in ((r', q'), ds)

-- Conversion from bi-Tambara lens to ExLens and back

-- p q' q a da -> p (q', q) (q, q') s ds
fromTamb :: BiLens q q' s ds a da -> ExLens a da q q' s ds
fromTamb pab_pst = dimap' lunit_1 lunit $ pab_pst unitExLens 

toTamb :: ExLens a da q q' s ds -> BiLens q q' s ds a da
-- p r r' a da -> p (r, q) (r', q') s ds
-- p r r' (m, a) (m, da)
-- p r r' (q, s) (q', ds)
-- p (r, q) (r', q') s ds
toTamb (ExLens fw bw) = beta . dimap fw bw . alpha

lunit_1 :: q -> ((), q)
lunit_1 q = ((), q)
lunit  :: ((), q) -> q
lunit ((), q) = q



comp :: BiLens q q' s ds a da -> BiLens r r' v dv s ds -> BiLens (q, r) (q', r') v dv a da
-- p z z' a da -> p (z, q) (z', q') s ds
-- p (z, q) (z', q') s ds -> p ((z, q), r) ((z', q'), r') v dv
-- reassoc
-- p z z' a da -> p (z, (q, r)) (z', (q', r') v dv
comp p1 p2 = dimap' assoc_1 assoc . p2 . p1

-- Testing

assoc :: ((a, b), c) -> (a, (b, c))
assoc ((a, b), c) = (a, (b, c))
assoc_1 :: (a, (b, c)) -> ((a, b), c)
assoc_1 (a, (b, c))= ((a, b), c)

type D = Double
-- Ideally, a counted vector
type V = [D]

-- data ExLens a da q q' s ds = 
--   forall m . ExLens ((q, s)  -> (m, a))  
--                     ((m, da) -> (q', ds))

linearL :: ExLens D D V V V V
linearL = ExLens fw bw
  where
    fw :: (V, V) -> ((V, V), D)
    -- a = Sum p * s
    fw (p, s) = ((s, p), sum $ zipWith (*) p s)
    -- da/dp = s, da/ds = p
    bw :: ((V, V), D) -> (V, V)
    bw ((s, p), da) = (fmap (da *) s  -- da/dp
                      ,fmap (da *) p) -- da/ds

biasL :: ExLens D D D D D D
biasL = ExLens fw bw 
  where 
    fw :: (D, D) -> ((), D)
    fw (p, s) = ((), p + s)
    -- da/dp = 1, da/ds = 1
    bw :: ((), D) -> (D, D)
    bw (_, da) = (da, da)

-- p V D D -> p V V V
linearT :: BiLens V V V V D D
linearT = toTamb linearL
-- p D D D -> p D D D
biasT :: BiLens D D D D D D
biasT = toTamb biasL

-- comp :: BiLens q q' s ds a da -> BiLens r r' v dv s ds -> BiLens (q, r) (q', r') v dv a da
neuronT :: BiLens (D, V) (D, V) V V D D
neuronT = comp biasT linearT

-- fromTamb :: BiLens q q' s ds a da -> ExLens a da q q' s ds
affine :: ExLens D D (D, V) (D, V) V V
affine = fromTamb neuronT

testTamb :: IO ()
testTamb = do
    putStrLn "forward"
    print $ fwd affine ((0.1, [-1, 1]), [2, 30])
    putStrLn "backward"
    -- (Para [1.3, -1.4] 0.1, [21, 33], 1)
    print $ bwd affine ((0.1, [1.3, -1.4]), [21, 33], 1)
