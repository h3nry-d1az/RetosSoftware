import Mathlib.Tactic

/--
Demostrar que para todo n ∈ ℕ, 2n + 9 ≤ 2ⁿ⁺⁴

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.
-/

lemma pow_2_n_plus_4_ge_2 {n : ℕ} : 2 ≤ 2^(n + 4) := by
  induction n with
  | zero => trivial
  | succ k hk =>
    calc
      2 ≤ 2 * 2 := by trivial
      _ ≤ 2 * 2^(k + 4) := by rel [hk]
      _ = 2^1 * 2^(k + 4) := by ring
      _ = 2^(1 + (k + 4)) := by rw [← pow_add 2]
      _ = 2^(k + 1 + 4) := by rw [add_comm]

theorem Reto14 {n : ℕ} : 2 * n + 9 ≤ 2 ^ (n + 4) := by
  induction n with
  | zero => trivial
  | succ k hk =>
    calc
      2 * (k + 1) + 9 = 2 * k + 2 + 9 := by rw [mul_add]
      _ = (2 * k + 9) + 2 := by rw [add_comm]
      _ ≤ 2^(k + 4) + 2 := by rel [hk]
      _ ≤ 2^(k + 4) + 2^(k + 4) := by rel [pow_2_n_plus_4_ge_2]
      _ = 2 * 2^(k + 4) := by ring
      _ = 2^1 * 2^(k + 4) := by ring
      _ = 2^(1 + (k + 4)) := by rw [← pow_add 2]
      _ = 2^(k + 1 + 4) := by rw [add_comm]

#check Reto14
