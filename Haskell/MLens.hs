{-# language ScopedTypeVariables #-}
module MLens where

-- Existential parametic lens

data MLens p dp s ds a da = 
  forall m . MLens ((p, s) -> (m, a))  ((m, da) -> (dp, ds))

compose :: forall p dp q dq s ds a da b db .
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