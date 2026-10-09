import Mathlib.Tactic

/--
Sea ℕ = {1, 2, 3, ⋯} el conjunto de los enteros positivos. Decimos que una
función f : ℕ → ℕ es _equilibrada_ si satisface las siguientes dos condiciones
para todos a, b ∈ ℕ:

1. Si a ≤ b, entonces f(a) ≤ f(b) (es monótona no decreciente).
2. f(a · f(b)) = b · f(a).

Determinar todas las funciones equilibradas.

Propuesto en la Liga Matemática de la ANEM: jornada 1, problema 3.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.
-/

theorem Jornada1_P3 {f : ℕ → ℕ}
  (hf₀ : ∀ x > 0, f x > 0)
  (hf₁ : ∀ a, ∀ b ≥ a, f a ≤ f b)
  (hf₂ : ∀ a, ∀ b, f (a * f b) = b * f a)
  : f = id := by
  have h₁ : ∀ a, f a = f (a * f 1) := by
    intro a
    rw [← one_mul (f a)]
    symm
    exact hf₂ a 1
    -- O, sin tácticas:
    -- fun a => Eq.mp
    --   (congr_arg (fun _fa => _fa = f (a * f 1)) (one_mul (f a)))
    --   ((hf₂ a 1).symm)
  obtain hf1 | hf1 := lt_or_ge (f 1) 1
  -- si f(1) < 1, entonces f(1) = 0, pero f(x) > 0
  · exfalso
    rw [Order.lt_one_iff] at hf1
    suffices h : ¬(f 1 > 0) from h (hf₀ 1 zero_lt_one)
    exact (LE.le.not_lt_iff_eq zero_le).mpr hf1.symm
  · obtain h | h := le_iff_eq_or_lt.mp hf1
    -- si f(1) = 1, entonces f(f(x)) = x
    · funext x
      have h' : f (f x) = x :=
        calc
          f (f x) = f (1 * f x) := by rw [one_mul]
          _ = x * (f 1) := hf₂ 1 x
          _ = x := by rw [← h, mul_one]
      -- luego f(x) = x
      obtain h'' | h'' := le_or_gt x (f x)
      · apply LE.le.antisymm
        · calc
            f x ≤ f (f x) := hf₁ x (f x) h''
            _ = x := h'
        · exact h''
      · have h'' := le_of_lt h''
        apply LE.le.antisymm
        · exact h''
        · calc
            f x ≥ f (f x) := hf₁ (f x) x h''
            _ = x := h'
    -- si f(1) > 1, entonces f(1) = 0
    · funext x
      have h : ∀ a, ∀ b ≥ a, f a = f b := by
        intro a b hab
        apply LE.le.antisymm
        · exact hf₁ a b hab
        · grind
      exfalso
      grind

#check Jornada1_P3
