import Mathlib.Tactic

/--
Demostrar que para todo n ∈ ℕ, n(n+1)(2n+1) es divisible por 6.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.
-/

theorem Reto16 {n : ℕ} : 6 ∣ n * (n + 1) * (2*n + 1) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  generalize (n : ZMod 6) = k
  fin_cases k <;> rfl
