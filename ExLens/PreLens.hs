module PreLens where

-- Pre-lens, parameterized by monoidal actions m and p
data PreLens m dm p dp s ds a da =
  PreLens ((p, s)   -> (m, a))
          ((dm, da) -> (dp, ds))

unitPreLens :: PreLens () () () () s ds s ds
unitPreLens = PreLens id id

-- Pre-lenses are composable
preCompose ::
    PreLens m dm p dp s ds a da -> PreLens n dn q dq a da b db ->
    PreLens (m, n) (dm, dn) (p, q) (dp, dq) s ds b db
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

-- Existential lens is a trace of a pre-lens
data ExLens p dp s ds a da = forall m. ExLens (PreLens m m p dp s ds a da)

compose ::
    ExLens p dp s ds a da -> ExLens q dq a da b db ->
    ExLens  (p, q) (dp, dq) s ds b db
compose (ExLens pl) (ExLens pl') = ExLens $ preCompose pl pl'
