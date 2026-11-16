import Mathlib.Data.Real.Basic

/-!
Definiciones varias sobre sucesiones, empleadas en los ``Retos Software
Matemático'' de análisis.
-/

def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

def SucConvergente (a : ℕ → ℝ) : Prop :=
  ∃ L, LimSuc a L

def SucAcotada (a : ℕ → ℝ) : Prop :=
  ∃ M, ∀ n, |a n| ≤ M

def CotaSup (a : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ n, a n ≤ M

def CotaInf (a : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ n, M ≤ a n

def SucCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, |a p - a q| < ε

def SubSucesion (v u : ℕ → ℝ) :=
  ∃ φ, StrictMono φ ∧ v = u ∘ φ

/-
Para abreviar exponemos varias notaciones para las definiciones anteriores:
* `a ⟹ L` para `LimSuc a L` (escritp \==>).
* `a ≪ M` para `CotaSup a M` (escrito \ll).
* `a ≫ M` para `CotaInf a M` (escrito \gg).
-/
notation a " ⟹ " L => LimSuc a L
notation a " ≪ " M => CotaSup a M
notation a " ≫ " M => CotaInf a M
