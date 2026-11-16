import RetosSoftware.RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
# Enunciado
Demostrar que si la sucesión aₙ converge a L y M es una cota inferior de aₙ (es
decir, M ≤ aₙ para todo n), entonces M ≤ L.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

# Demostración
Por la condición de que lím aₙ = L tenemos que para todo ε > 0 existe N ∈ ℕ tal
que para todo n ≥ N se verifica que aₙ - ε < L, luego como M ≤ aₙ tenemos que
para todo ε > 0, M - ε < L.

Esto último, en definitiva, implica que M ≤ L, ya que si M > L entonces
M - L > 0 y, tomando esta cantidad como ε se llega a que
  L > M - ε = M - (M - L) = L,
que es una contradicción.

Véase el Reto 20, que es análogo a este.
-/

lemma le_of_forall_sub_lt {a b : ℝ}
  (h : ∀ ε > 0, a - ε < b)
  : a ≤ b
  := by
  by_contra hab
  rw [not_le, ← sub_pos] at hab
  apply LT.lt.false (a := b)
  calc
    b = a - (a - b) := by ring
    _ < b := h (a - b) hab

theorem Reto27 {a : ℕ → ℝ} {L M : ℝ}
  (ha : a ⟹ L)
  (hM : a ≫ M)
  : M ≤ L
  := by
  apply le_of_forall_sub_lt
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  calc
    M - ε ≤ a N - ε := by rel [hM N]
    _ < L := by
      obtain ⟨h₁, h₂⟩ := abs_lt.mp (hN N (refl N))
      linarith

#check Reto27
