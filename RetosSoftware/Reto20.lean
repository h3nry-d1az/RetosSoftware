import RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
Demostrar que si la sucesión aₙ converge a L y M es una cota superior de aₙ
(es decir, aₙ ≤ M para todo n), entonces L ≤ M.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Por darse que aₙ → L, entonces para todo ε existe N ∈ ℕ a partir del cual
    L - ε < aₙ ≤ M,
luego L ≤ M, pues de lo contrario se tendría que L > M y por ello
    M ≥ L - (L - M) / 2 > L - (L - M) = M,
que supone una contradicción.
-/

lemma le_forall_epsilon_to_le {a b : ℝ} (hab : ∀ ε > 0, a - ε ≤ b) : a ≤ b
  := by
  by_contra h
  rw [not_le] at h
  apply LT.lt.false (a := a)
  calc
    a ≤ b + (a - b) / 2 := by
      have h' := hab ((a - b) / 2) (half_pos (sub_pos_of_lt h))
      linarith
    _ < b + (a - b) := by linarith
    _ = a := by norm_num

/-- La primera demostración es idéntica a la segunda en concepto, solo que
no utiliza tácticas. -/
theorem Reto20_1 {L M : ℝ} {a : ℕ → ℝ} (hL : LimSuc a L) (hM : CotaSup a M)
  : L ≤ M
  := le_forall_epsilon_to_le fun ε => fun hε =>
    let ⟨N, hN⟩ := hL ε hε
    have h₁ : L - ε ≤ a N :=
      le_of_lt (sub_lt_of_abs_sub_lt_left (hN N (le_refl N)))
    have h₂ : a N ≤ M := hM N
    show _ from (LE.le.trans h₁ h₂)

#check Reto20_1

theorem Reto20_2 {L M : ℝ} {a : ℕ → ℝ} (hL : LimSuc a L) (hM : CotaSup a M)
  : L ≤ M
  := by
  apply le_forall_epsilon_to_le
  intro ε hε
  obtain ⟨N, hN⟩ := hL ε hε
  have h : |a N - L| < ε := hN N (by rfl)
  rw [abs_sub_lt_iff] at h
  calc
    _ ≤ a N := by linarith
    _ ≤ M := hM N

#check Reto20_2
