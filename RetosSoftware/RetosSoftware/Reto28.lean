import RetosSoftware.RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
# Enunciado
Demostrar que la sucesión aₙ = n no está acotada.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

# Demostración
Asumiendo que |aₙ| ≤ M para algún M ∈ ℝ⁺, tenemos que M+1 ≤ M, que es una
contradicción.
-/

theorem Reto28 {a : ℕ → ℝ} (ha : ∀ n : ℕ, a n = n) : ¬SucAcotada a := by
  intro ⟨M, hM⟩
  have hM_pos : M ≥ 0 := LE.le.trans (abs_nonneg (a 0)) (hM 0)
  have h₁ := hM (Nat.ceil M + 1)
  have h₂ : (Nat.ceil M : ℝ) + 1 > M := calc
    _ ≥ M + 1 := by rel [Nat.le_ceil M]
    _ > M := lt_add_one M
  rw [ha, abs_of_pos (by push_cast; calc
    _ > M := h₂
    M ≥ 0 := hM_pos)] at h₁
  push_cast at h₁
  exact (not_lt_of_ge h₁) h₂

#check Reto28
