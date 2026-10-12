import RetosSoftware.RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
Demostrar que la sucesión constante aₙ = L converge a L.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Dado cualquier ε > 0, podemos tomar N = 0, puesto que para todo n ≥ N
  |aₙ - L| = |L - L| = 0 < ε,
como se quería demostrar.
-/

theorem Reto23 {L : ℝ} {a : ℕ → ℝ}
  (ha : ∀ n, a n = L)
  : a ⟹ L := by
  intro ε hε
  use 0
  intro n hn
  calc
    |a n - L| = |L - L| := by rw [ha n]
    _ = 0 := by norm_num
    _ < ε := hε

#check Reto23
