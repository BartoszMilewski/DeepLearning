module MLens where
import Distribution.Simple.Setup (GlobalFlags(globalVersion))

-- Existential parametic lens

data MLens p dp s ds a da = 
  forall m . MLens ((p, s)  -> (m, a))  
                   ((m, da) -> (dp, ds))

data Lens s ds a da =
  forall m . Lens (s -> (m, a)) 
                  ((m, da) -> ds)

compose ::
    MLens p dp s ds a da -> MLens q dq a da b db ->
    MLens  (p, q) (dp, dq) s ds b db
compose (MLens f1 g1) (MLens f2 g2) = MLens f3 g3
  where
    f3 ((p, q), s) =
      let (m, a) = f1 (p, s)
          (n, b) = f2 (q, a)
      in ((m, n), b)
    g3 ((m, n), db) =
      let (dq, da) = g2 (n, db)
          (dp, ds) = g1 (m, da)
      in ((dp, dq), ds)

composeR ::
    MLens p dp s ds a da -> Lens a da b db ->
    MLens  p dp s ds b db
composeR (MLens f1 g1) (Lens f2 g2) = MLens f3 g3
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
    Lens s ds a da -> MLens q dq a da b db ->
    MLens  q dq s ds b db
composeL (Lens f1 g1) (MLens f2 g2) = MLens f3 g3
  where
    f3 (q, s) =
      let (m, a) = f1 s
          (n, b) = f2 (q, a)
      in ((m, n), b)
    g3 ((m, n), db) =
      let (dq, da) = g2 (n, db)
          ds = g1 (m, da)
      in (dq, ds)

prodLens ::
    MLens p dp s ds a da -> MLens p' dp' s' ds' a' da' ->
    MLens (p, p') (dp, dp') (s, s') (ds, ds') (a, a') (da, da')
prodLens (MLens f1 g1) (MLens f2 g2) = MLens  f3 g3
  where
    f3 ((p, p'), (s, s')) = ((m, m'), (a, a'))
      where (m, a)   = f1 (p, s)
            (m', a') = f2 (p', s')
    g3 ((m, m'), (da, da')) = ((dp, dp'), (ds, ds'))
      where
        (dp, ds)   = g1 (m, da)
        (dp', ds') = g2 (m', da')

consLens :: 
    MLens p dp s ds a da -> MLens [p] [dp] [s] [ds] [a] [da] ->
    MLens [p] [dp] [s] [ds] [a] [da]
consLens (MLens f g) (MLens fs gs) = MLens fv gv 
  where
    fv (p : ps, s : ss) = ((m, ms), a : as)
      where (m, a) = f (p, s)
            (ms, as) = fs (ps, ss)
    gv ((m, ms), da : das) = (dp : dps, ds : dss)
      where (dp, ds) = g (m, da)
            (dps, dss) = gs (ms, das)

vecLens ::
    Int -> MLens p dp s ds a da -> MLens [p] [dp] [s] [ds] [a] [da]
vecLens 0 _ = MLens (const ([], [])) (const ([], []))
vecLens n lns = consLens lns (vecLens (n - 1) lns)
