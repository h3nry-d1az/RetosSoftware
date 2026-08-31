import Mathlib.Data.Real.Basic

/--
Definiciones varias sobre sucesiones, empleadas en los ``Retos Software
Matemático'' de análisis.
-/

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

def SucConvergente (a : ℕ → ℝ) : Prop :=
  ∃ L, LimSuc a L

def SucAcotada (a : ℕ → ℝ) : Prop :=
  ∃ M, ∀ n, |a n| ≤ M
