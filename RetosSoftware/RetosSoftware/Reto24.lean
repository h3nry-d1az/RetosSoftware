import RetosSoftware.RetosSoftware.Sucesiones
import RetosSoftware.RetosSoftware.Reto22
import RetosSoftware.RetosSoftware.Reto23
import Mathlib.Tactic

/-!
Usando el Reto 22 (que afirma que si una sucesión tiene dos subsucesiones que
convergen a límites distintos, entonces la sucesión no es convergente) demostrar
que la sucesión definida por 1, -1, 1, -1, ... no es convergente.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

La sucesión a₂ₙ converge a 1, mientras que la sucesión a₂ₙ₊₁ converge a -1,
luego por Reto 22 aₙ diverge.
-/

lemma two_mul_lt_two_mul {a b : ℕ} (hab : a < b) : 2 * a < 2 * b :=
  (Nat.mul_lt_mul_left (a := 2) (b := a) (c := b) zero_lt_two).mpr hab

theorem Reto24 {a : ℕ → ℝ}
  (ha : ∀ n, a n = (-1) ^ n)
  : ¬SucConvergente a := by
  apply Reto22 (b₁ := fun n => 1) (b₂ := fun n => -1) (L₁ := 1) (L₂ := -1)
  -- aₙ = 1 es una subsucesión de aₙ = (-1)ⁿ
  · use (fun n => 2 * n)
    constructor
    -- n ↦ 2n es creciente
    · intro a b hab
      calc
        _ = 2 * a := by rfl
        _ < 2 * b := by rel [two_mul_lt_two_mul hab]
    -- a ∘ (n ↦ 2n) = 1
    · funext n
      symm
      calc
        _ = a (2 * n) := by rfl
        _ = (-1) ^ (2 * n) := ha (2 * n)
        _ = 1 := Even.neg_one_pow (n := 2 * n) ⟨n, two_mul n⟩
  -- aₙ = -1 es una subsucesión de aₙ = (-1)ⁿ
  · use (fun n => 2 * n + 1)
    constructor
    -- n ↦ 2n+1 es creciente
    · intro a b hab
      calc
        _ = 2 * a + 1 := by rfl
        _ < 2 * b + 1 := by rel [two_mul_lt_two_mul hab]
    -- a ∘ (n ↦ 2n+1) = -1
    · funext n
      symm
      calc
        _ = a (2 * n + 1) := by rfl
        _ = (-1) ^ (2 * n + 1) := ha (2 * n + 1)
        _ = (-1) ^ (2 * n) * (-1) ^ 1 := pow_add (-1 : ℝ) (2 * n) 1
        _ = 1 * (-1) := by
          rw [pow_one (-1)]
          rw [Even.neg_one_pow (n := 2 * n) ⟨n, two_mul n⟩]
        _ = -1 := by norm_num
  -- Reto 23 challa los límites
  · exact Reto23 (fun n => (by rfl))
  · exact Reto23 (fun n => (by rfl))
  norm_num

#check Reto24
