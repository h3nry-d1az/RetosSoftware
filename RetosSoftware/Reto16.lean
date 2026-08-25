import Mathlib.Tactic

/--
Demostrar que para todo n ∈ ℕ, n(n+1)(2n+1) es divisible por 6.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.
-/

-- 1ª forma
theorem Reto16_1 {n : ℕ} : 6 ∣ n * (n + 1) * (2*n + 1) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  generalize (n : ZMod 6) = k
  fin_cases k <;> rfl

#check Reto16_1

-- 2ª forma
theorem Reto16_2 {n : ℕ} : 6 ∣ n * (n + 1) * (2*n + 1) := by
  induction n with
  | zero => norm_num
  | succ m hm =>
    let ⟨t, ht⟩ := hm
    use t + m*m + 2*m + 1
    calc
      _ = m * (m + 1) * (2*m + 1) + 6*m*m + 12*m + 6 := by ring
      _ = 6 * t + 6*(m*m + 2*m + 1) := by rw [ht]; ring
      _ = 6 * (t + m*m + 2*m + 1) := by ring

#check Reto16_2
