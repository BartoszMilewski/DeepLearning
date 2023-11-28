module ExLens where

-- Existential parametic lens

data ExLens p dp s ds a da = 
  forall m . ExLens ((p, s)  -> (m, a))  
                   ((m, da) -> (dp, ds))

-- For convenience, a lens with empty (unit) parameter
data Lens s ds a da =
  forall m . Lens (s -> (m, a)) 
                  ((m, da) -> ds)

-- Accessors

fwd :: ExLens p dp s ds a da -> (p, s) -> a
fwd (ExLens f g) (p, s) = snd $ f (p, s)

bwd :: ExLens p dp s ds a da -> (p, s, da) -> (dp, ds)
bwd (ExLens f g) (p, s, da) = g (fst (f (p, s)), da)

fwd0 :: Lens s ds a da -> s -> a
fwd0 (Lens f g) s = snd $ f s

bwd0 :: Lens s ds a da -> (s, da) -> ds
bwd0 (Lens f g) (s, da) = g (fst (f s), da)

compose ::
    ExLens p dp s ds a da -> ExLens q dq a da b db ->
    ExLens  (p, q) (dp, dq) s ds b db
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

-- Convenient special cases

composeR ::
    ExLens p dp s ds a da -> Lens a da b db ->
    ExLens  p dp s ds b db
composeR (ExLens f1 g1) (Lens f2 g2) = ExLens f3 g3
  where
    f3 (p, s) =
      let (m, a) = f1 (p, s)
          (n, b) = f2 a
      in ((m, n), b)
    g3 ((m, n), db) =
      let da = g2 (n, db)
          (dp, ds) = g1 (m, da)
      in (dp, ds)

composeL ::
    Lens s ds a da -> ExLens q dq a da b db ->
    ExLens  q dq s ds b db
composeL (Lens f1 g1) (ExLens f2 g2) = ExLens f3 g3
  where
    f3 (q, s) =
      let (m, a) = f1 s
          (n, b) = f2 (q, a)
      in ((m, n), b)
    g3 ((m, n), db) =
      let (dq, da) = g2 (n, db)
          ds = g1 (m, da)
      in (dq, ds)

-- A pair of lenses in parallel
prodLens ::
    ExLens p dp s ds a da -> ExLens p' dp' s' ds' a' da' ->
    ExLens (p, p') (dp, dp') (s, s') (ds, ds') (a, a') (da, da')
prodLens (ExLens f1 g1) (ExLens f2 g2) = ExLens  f3 g3
  where
    f3 ((p, p'), (s, s')) = ((m, m'), (a, a'))
      where (m, a)   = f1 (p, s)
            (m', a') = f2 (p', s')
    g3 ((m, m'), (da, da')) = ((dp, dp'), (ds, ds'))
      where
        (dp, ds)   = g1 (m, da)
        (dp', ds') = g2 (m', da')

-- A cons function combines a lens with a (parallel) list of lenses
consLens :: 
    ExLens p dp s ds a da -> ExLens [p] [dp] [s] [ds] [a] [da] ->
    ExLens [p] [dp] [s] [ds] [a] [da]
consLens (ExLens f g) (ExLens fs gs) = ExLens fv gv 
  where
    fv (p : ps, s : ss) = ((m, ms), a : as)
      where (m, a) = f (p, s)
            (ms, as) = fs (ps, ss)
    gv ((m, ms), da : das) = (dp : dps, ds : dss)
      where (dp, ds) = g (m, da)
            (dps, dss) = gs (ms, das)

-- Vector lens, combines n identical lenses in parallel
vecLens ::
    Int -> ExLens p dp s ds a da -> ExLens [p] [dp] [s] [ds] [a] [da]
vecLens 0 _ = ExLens (const ([], [])) (const ([], []))
vecLens n lns = consLens lns (vecLens (n - 1) lns)

branch :: Monoid s => Int -> Lens s s [s] [s]
branch n = Lens (\s -> ((), replicate n s)) 
                (\(_, ss) -> mconcat ss) -- pointwise <+>

-- xs = [1, 2, 3, 4, 5, 6]
-- vw = [[1, 2, 3], [4, 5, 6]]  m = 3 n = 2
rechunk :: Int -> Int -> [a] -> [[a]]
rechunk m 0 xs = []
rechunk m n xs = take m xs : rechunk m (n - 1) (drop m xs)

-- Lens (Vect n (Vect m s)) (Vect (n * m) s)
-- Here the existential parameter is (Int, Int)
flatten :: Lens [[s]] [[ds]] [s] [ds]
flatten = Lens f g
  where
    f sss = ((length (head sss), length sss), concat sss)
    -- (Vect n (Vect m s), Vect (n * m) s) -> (Vect n (Vect m s))
    g ((m, n), ds) = rechunk m n ds

-- A batch of lenses in parallel, sharing the same parameters
-- Back propagation combines the parameters
batchN :: (Monoid dp) =>
    Int -> ExLens p dp s ds a da -> ExLens p dp [s] [ds] [a] [da]
batchN n (ExLens f g) = ExLens fv gv
  where
    fv (p, ss) = unzip $ fmap f $ zip (replicate n p) ss
    gv (ms, das) = (mconcat dps, dss)
      where -- g :: (m, da) -> (dp, ds)
        (dps, dss) = unzip $ fmap g $ zip ms das

test1 :: IO ()
test1 = do 
  let sss = [[1, 2, 3], [4, 5, 6]]
  let ss = [10, 11, 12, 13, 14, 15, 16]
  putStrLn "flatten forward"
  print $ fwd0 flatten sss
  putStrLn "flatten backward"
  print $ bwd0 flatten (sss, ss)
  putStrLn ""