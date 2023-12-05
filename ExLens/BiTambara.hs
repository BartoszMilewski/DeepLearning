{-# language ScopedTypeVariables #-}
module BiTambara where
import Data.Bifunctor ( Bifunctor(second, first, bimap) )

lunit_1 :: q -> ((), q)
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

-- Composition

comp :: BiLens q q' s ds a da -> BiLens r r' v dv s ds -> BiLens (q, r) (q', r') v dv a da
-- p z z' a da -> p (z, q) (z', q') s ds
-- p (z, q) (z', q') s ds -> p ((z, q), r) ((z', q'), r') v dv
-- reassoc
-- p z z' a da -> p (z, (q, r)) (z', (q', r') v dv
comp p1 p2 = dimap' assoc_1 assoc . p2 . p1

-- Product

-- Show that a BiTambara of products is a BiTambara on both sides of the product

data PRight p q r a b q' r' a' b' = PRight (p (q, q') (r, r') (a, a') (b, b'))

instance (BiProfunctor p) => BiProfunctor (PRight p q r a b) where
    dimap f g (PRight p) = PRight $ dimap (second f) (second g) p 
    dimap' f g (PRight p) = PRight $ dimap' (second f) (second g) p
--     dimap' :: (r -> q) -> (q' -> r') -> p q q' a b -> p r r' a b

instance (BiTambara p) => BiTambara (PRight p q r a b) where
    -- p (q, q') (r, r') (a, a') (b, b') -alpha->
    -- p (q, q') (r, r') (m, (a, a')) (m, (b, b')) -dimap->
    -- p (q, q') (r, r') (a, (m, a')) (b, (m, b'))
    alpha (PRight p) = PRight $ dimap (\(a, (m, a')) -> (m, (a, a')))
                                      (\(m, (b, b')) -> (b, (m, b'))) $ alpha p  
    -- p (q, q')  (r, r')  (a, (q1, a')) (b, (q1', b')) - dimap->
    -- p (q, q')  (r, r')  (q1, (a, a')) (q1', (b, b')) - beta ->
    -- p ((q, q'), q1) ((r, r'), q1')  (a, a') (b, b') - dimap' ->
    -- p (q, (q', q1)) (r, (r', q1'))   (a, a') (b, b')
    beta (PRight p) = PRight $ 
      dimap' (\(q, (q', q1)) -> ((q, q'), q1))  (\((r, r'), q1') -> (r, (r', q1'))) $
      beta $
      dimap (\(q1, (a, a')) -> (a, (q1, a'))) (\(b, (q1', b')) -> (q1', (b, b'))) p

data PLeft p q' r' a' b' q r a b = PLeft (p (q, q') (r, r') (a, a') (b, b'))

instance (BiProfunctor p) => BiProfunctor (PLeft p q r a b) where
    dimap f g (PLeft p) = PLeft $ dimap (first f) (first g) p 
    dimap' f g (PLeft p) = PLeft $ dimap' (first f) (first g) p

instance (BiTambara p) => BiTambara (PLeft p q r a b) where
    alpha (PLeft p) = PLeft $ dimap (\((m, a), a') -> (m, (a, a')))
                                    (\(m, (b, b')) -> ((m, b), b')) $ alpha p  
    beta (PLeft p) = PLeft $ 
      dimap' (\((q, q1), q') -> ((q, q'), q1)) (\((r, r'), q1') -> ((r, q1'), r')) $
      beta $
      dimap  (\(q1, (a, a')) -> ((q1, a), a')) (\((q1', b), b') -> (q1', (b, b'))) p


prodLens :: BiLens q  dq  s  ds  a  da -> 
            BiLens q' dq' s' ds' a' da' ->
            BiLens (q, q') (dq, dq') (s, s') (ds, ds') (a, a') (da, da')
    -- l1 :: p1 r1 r1' a  da  -> p1 (r1, q)  (r1', dq)  s  ds
    -- l2 :: p2 r2 r2' a' da' -> p2 (r2, q') (r2', dq') s' ds'
    -- l3 :: p r r' (a, a') (da, da') -> p (r, (q, q')) (r', (dq, dq')) (s, s') (ds, ds')
prodLens l1 l2 p0 = 
    let p1 = dimap' runit runit_1 p0 
        pl1 = PLeft p1
        (PLeft pl2) = l1 pl1 
        pr1 = PRight pl2 
        (PRight pr2) = l2 pr1 
        pr3 = dimap' (second lunit_1) (second lunit) pr2
    in dimap' assoc_1 assoc pr3

-- p0 :: (r, ()) (r', ()) (a, a') (da, da') ~ PLeft () () a' da' r r' a da
-- l1 :: PLeft () () a' da' (r, q) (r', dq) s ds
--       PRight (r, q) (r', dq) s ds  () () a' da'
-- l2 :: PRigth (r, q) (r', dq) s ds ((), q') ((), dq') s' ds'
--       ((r, q), q') ((r', dq), dq') (s, s') (ds, ds')
-- data PRight q  r  a  b  q' r' a' b' =  (q, q') (r, r') (a, a') (b, b')
-- data PLeft  q' r' a' b' q  r  a  b  =  (q, q') (r, r') (a, a') (b, b')


-- Testing

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
