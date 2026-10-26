import RetosSoftware.RetosSoftware.Sucesiones
import RetosSoftware.RetosSoftware.Reto21
import Mathlib.Tactic

/-!
Supongamos que la sucesión cₙ es una mezcla de las sucesiones aₙ y bₙ; es decir,
que
  (c₀, c₁, c₂, ⋯ ) = (a₀, b₀, a₁, b₁, a₂, b₂, ⋯ ).
Demostrar que si cₙ converge a L, entonces aₙ y bₙ convergen a L.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Es evidente que a y b son subsucesiones de c, luego por Reto 21 convergen a L.

También puede verse por que como aₙ = c₂ₙ y bₙ = c₂ₙ₊₁, para cada ε basta tomar
el respectivo N de c.
-/


-- Demostración usando el reto 21
theorem Reto25_1 {a b c : ℕ → ℝ} {L : ℝ}
  (hc : ∀ n : ℕ, c n = if Even n then a (n / 2) else b ((n - 1) / 2))
  (hL : c ⟹ L)
  : (a ⟹ L) ∧ (b ⟹ L)
  := by
  constructor
  · apply Reto21 (u := c) (v := a)
    · use fun n => 2 * n
      constructor
      · intro m₁ m₂ hm₁m₂
        calc
          _ = 2 * m₁ := by rfl
          _ < 2 * m₂ := by rel [hm₁m₂]
      · funext m
        symm
        calc
          _ = c (2 * m) := by rfl
          _ = a m := by
            have : Even (2 * m) := ⟨m, two_mul m⟩
            rw [hc]
            simp [this]
    · exact hL
  · apply Reto21 (u := c) (v := b)
    · use fun n => 2 * n + 1
      constructor
      · intro m₁ m₂ hm₁m₂
        calc
          _ = 2 * m₁ + 1 := by rfl
          _ < 2 * m₂ + 1 := by rel [hm₁m₂]
      · funext m
        symm
        calc
          _ = c (2 * m + 1) := by rfl
          _ = b m := by
            rw [hc]
            simp [Nat.not_even_two_mul_add_one m]
    · exact hL

#check Reto25_1


-- Demostración nueva
theorem Reto25_2 {a b c : ℕ → ℝ} {L : ℝ}
  (hc : ∀ n : ℕ, c n = if Even n then a (n / 2) else b ((n - 1) / 2))
  (hL : c ⟹ L)
  : (a ⟹ L) ∧ (b ⟹ L)
  := by
  -- reescribimos aₙ en función de cₙ
  have h_ac (n : ℕ) : a n = c (2 * n) := calc
    a n = a (2 * n / 2) := by norm_num
    _ = c (2 * n) := by
      rw [hc]
      split_ifs with h_even
      · rfl
      · exfalso
        apply h_even
        use n
        exact two_mul n
  -- ídem para bₙ y cₙ
  have h_bc (n : ℕ) : b n = c (2 * n + 1) := calc
    b n = b (((2 * n + 1) - 1) / 2) := by norm_num
    _ = c (2 * n + 1) := by
      rw [hc]
      split_ifs with h_even
      · exfalso
        suffices h_odd : ¬Even (2 * n + 1) from h_odd h_even
        exact Nat.not_even_bit1 n
      · rfl
  -- y ahora demostramos la convergencia de ambas
  constructor
  · intro ε hε
    let ⟨N, hN⟩ := hL ε hε
    use N
    intro n hn
    calc
      |a n - L| = |c (2 * n) - L| := by rw [h_ac n]
      _ < ε := by apply hN; linarith
  · intro ε hε
    let ⟨N, hN⟩ := hL ε hε
    use N
    intro n hn
    calc
      |b n - L| = |c (2 * n + 1) - L| := by rw [h_bc]
      _ < ε := by apply hN; linarith

#check Reto25_2
