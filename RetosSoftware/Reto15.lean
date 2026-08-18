import Mathlib.Tactic

/--
Demostrar que existe un k ∈ ℕ tal que para todo n ∈ ℕ
  (n + k)² ≤ 2ⁿ⁺ᵏ

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.
-/

lemma two_pow_ge_two_mul_add_one {n : ℕ} : 2 * (n + 3) + 1 ≤ 2^(n + 3) := by
  induction n with
  | zero => norm_num
  | succ k hk =>
    calc
      2 * (k + 1 + 3) + 1 = 2 * (k + 3) + 1 + 2 := by omega
      _ ≤ 2^(k + 3) + 2 := by rel [hk]
      _ = 2^(k + 3) + 2^1 := by norm_num
      _ ≤ 2^(k + 3) + 2^(k + 3) := by omega
      _ = 2^1 * 2^(k + 3) := by rw [← two_mul, pow_one]
      _ = 2^(k + 3 + 1) := by rw [← pow_add, add_comm]

theorem Reto15 : ∃ k : ℕ, ∀ n : ℕ, (n + k)^2 ≤ 2^(n + k) := by
  use 4 -- 3² > 2³, luego ha de tomarse k ≥ 4
  intro n
  induction n with
  | zero => norm_num
  | succ m hm =>
    calc
      (m + 1 + 4)^2 = (m + 4 + 1)^2 := by rw [add_comm]
      _ = (m + 4)^2 + 2 * (m + 4) + 1 := by rw [add_sq, mul_one, one_pow]
      _ ≤ 2^(m + 4) + 2 * (m + 4) + 1 := by rel [hm]
      _ = 2^(m + 4) + 2 * (m + 1 + 3) + 1 := by rw [(by norm_num : 4 = 1 + 3)]
      _ ≤ 2^(m + 4) + 2^(m + 1 + 3) := by
        rw [add_assoc]
        rel [two_pow_ge_two_mul_add_one]
      _ = 2^(m + 4) + 2^(m + 4) := by rw [add_assoc]
      _ = 2^1 * 2^(m + 4) := by rw [← two_mul, pow_one]
      _ = 2^(m + 1 + 4) := by rw [← pow_add, add_comm]

#check Reto15
