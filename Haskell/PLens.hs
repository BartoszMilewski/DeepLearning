{-# language ScopedTypeVariables #-}
module PLens where

data PLens p dp s ds a da = PLens 
  { fwd :: (p, s) -> a
  , bwd :: (p, s, da) -> (dp, ds)
  }

data Lens s ds a da = Lens
  { fwd0 :: s -> a
  , bwd0 :: (s, da) -> ds
  }

compose :: forall p dp q dq s ds a da c dc.
    PLens p dp s ds a da -> PLens q dq a da c dc ->
    PLens (p, q) (dp, dq) s ds c dc
compose pl ql = PLens fw bw
  where
    fw :: ((p, q), s) -> c 
    fw ((p, q), s) = fwd ql $ (q, fwd pl (p, s))
    bw :: ((p, q), s, dc) -> ((dp, dq), ds)
    bw ((p, q), s, dc) = ((dp, dq), ds)
      where 
        a = fwd pl (p, s)
        (dq, da) = bwd ql (q, a, dc)
        (dp, ds) = bwd pl (p, s, da)

composeR :: forall p dp s ds a da c dc.
    PLens p dp s ds a da -> Lens a da c dc ->
    PLens p dp s ds c dc
composeR pl l0 = PLens fw bw
  where
    fw :: (p, s) -> c 
    fw (p, s) = fwd0 l0 $ fwd pl (p, s)
    bw :: (p, s, dc) -> (dp, ds)
    bw (p, s, dc) = (dp, ds)
      where 
        a = fwd pl (p, s)
        da = bwd0 l0 (a, dc)
        (dp, ds) = bwd pl (p, s, da)

composeL :: forall s ds a da q dq c dc.
    Lens s ds a da -> PLens q dq a da c dc ->
    PLens q dq s ds c dc
composeL l0 ql = PLens fw bw
  where
    fw :: (q, s) -> c 
    fw (q, s) = fwd ql $ (q, fwd0 l0 s)
    bw :: (q, s, dc) -> (dq, ds)
    bw (q, s, dc) = (dq, ds)
      where 
        a = fwd0 l0 s
        (dq, da) = bwd ql (q, a, dc)
        ds = bwd0 l0 (s, da)

prodLens :: forall p dp s ds a da p' dp' s' ds' a' da'.
    PLens p dp s ds a da -> PLens p' dp' s' ds' a' da' ->
    PLens (p, p') (dp, dp') (s, s') (ds, ds') (a, a') (da, da')
prodLens pl pl' = PLens fwdProd bwdProd
  where
    fwdProd :: ((p, p'), (s, s')) -> (a, a')
    fwdProd ((p, p'), (s, s')) = (a, a')
      where a  = fwd pl (p, s)
            a' = fwd pl' (p', s')
    bwdProd :: ((p, p'), (s, s'), (da, da')) -> ((dp, dp'), (ds, ds'))
    bwdProd ((p, p'), (s, s'), (da, da')) = ((dp, dp'), (ds, ds'))
      where
        (dp, ds)   = bwd pl (p, s, da)
        (dp', ds') = bwd pl' (p', s', da')

-- Unit wrt product
unitLens :: PLens () () () () () ()
unitLens = PLens (const ()) (const ((), ()))

-- n lenses in parallel
vecLens :: forall p dp s ds a da.
    Int -> PLens p dp s ds a da -> PLens [p] [dp] [s] [ds] [a] [da]
vecLens 0 pl = PLens (const []) (const ([], []))
vecLens n pl = PLens fw bw
  where
    plrec = vecLens (n - 1) pl 
    prod  = prodLens pl plrec
    fw :: ([p], [s]) -> [a]
    fw (p : ps, s : ss) = a : as
      where
        (a, as) = fwd prod ((p, ps), (s, ss))
    bw :: ([p], [s], [da]) -> ([dp], [ds])
    bw (p : ps, s : ss, da : das) = (dp : dps, ds : dss)
      where
        ((dp, dps), (ds, dss)) = bwd prod ((p, ps), (s, ss), (da, das))

branch :: Monoid s => Int -> Lens s s [s] [s]
branch n = Lens (replicate n) (\(_, ss) -> mconcat ss) -- pointwise <+>

-- xs = [1, 2, 3, 4, 5, 6]
-- vw = [[1, 2, 3], [4, 5, 6]]  m = 3 n = 2
rechunk :: Int -> Int -> [a] -> [[a]]
rechunk m 0 xs = []
rechunk m n xs = take m xs : rechunk m (n - 1) (drop m xs)

-- Lens (Vect n (Vect m s)) (Vect (n * m) s)
flatten :: Lens [[s]] [[ds]] [s] [ds]
flatten = Lens fw bw
  where
    fw = concat
    -- (Vect n (Vect m s), Vect (n * m) s) -> (Vect n (Vect m s)
    bw (sss, ds) = rechunk (length (head sss)) (length sss) ds

batchN :: forall p dp s ds a da.
    Int -> ([dp] -> dp) -> PLens p dp s ds a da -> PLens p dp [s] [ds] [a] [da]
batchN n fold lns = PLens fw bw
  where
    fw :: (p, [s]) -> [a]
    fw (px, ss) = fmap (fwd lns) $ zip (replicate n px) ss
    bw :: (p, [s], [da]) -> (dp, [ds])
    bw (px, ss, das) = (fold dps', dss')
      where 
        (dps', dss') = unzip $ fmap (bwd lns) $ zip3 (replicate n px) ss das

toSingleton :: Lens s ds [s] [ds]
toSingleton = Lens (\s -> [s]) (\(_, [ds]) -> ds)

test1 :: IO ()
test1 = do 
  let sss = [[1, 2, 3], [4, 5, 6]]
  let ss = [10, 11, 12, 13, 14, 15, 16]
  putStrLn "flatten forward"
  print $ fwd0 flatten sss
  putStrLn "flatten backward"
  print $ bwd0 flatten (sss, ss)
  putStrLn ""