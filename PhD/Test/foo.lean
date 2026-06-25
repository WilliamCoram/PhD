import Mathlib

variable (U : Set (Prod ℕ ℝ))

structure lowerConvexHull (s : Set (Prod ℕ ℝ)) where
    x : convexHull ℕ s
    le : ∀ q : convexHull ℕ s, q.1.1 = x.1.1 → x.1.2 ≤ q.1.2
