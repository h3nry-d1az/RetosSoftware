import RetosSoftware.RetosSoftware.Sucesiones
import RetosSoftware.RetosSoftware.Reto9
import RetosSoftware.RetosSoftware.Reto21
import Mathlib.Tactic

/-!
Demostrar que si una sucesión tiene dos subsucesiones con límites distintos,
entonces la sucesión no es convergente.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Asumiendo que la sucesión converge a un límite L, tenemos (por el reto 21) que
las dos subsucesiones convergen a L. Por la unicidad del límite (reto 9) los
límites de estas son ambos L, luego son iguales entre sí, lo que contradice la
hipótesis inicial de ser distintos.
-/

theorem Reto22 {a b₁ b₂ : ℕ → ℝ} {L₁ L₂ : ℝ}
  (hb₁ : SubSucesion b₁ a)
  (hb₂ : SubSucesion b₂ a)
  (hL₁ : LimSuc b₁ L₁)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a := by
  intro ha
  apply h
  obtain ⟨L, hL⟩ := ha
  let hb₁ := Reto21 hb₁ hL  -- b₁ → L
  let hb₂ := Reto21 hb₂ hL  -- b₂ → L
  let hLL₁ := Reto9 hb₁ hL₁ -- L = L₁
  let hLL₂ := Reto9 hb₂ hL₂ -- L = L₂
  exact Eq.trans hLL₁.symm hLL₂

#check Reto22
