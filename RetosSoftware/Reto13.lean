import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/--
Demostrar la desigualdad triangular inversa; es decir, que para cualesquiera
números reales x e y, se cumple la relación
  ||x| - |y|| ≤ |x - y|.

Propuesto por José A. Alonso Jiménez.
-/

theorem Reto13 {x y : ℝ} : |(|x| - |y|)| ≤ |x - y| := by
  obtain hx | hx := le_or_gt 0 x
  -- Caso 1: x ≥ 0
  · rw [abs_of_nonneg hx]
    obtain hy | hy := le_or_gt 0 y
    -- Caso 1.1: y ≥ 0 (trivial)
    · rw [abs_of_nonneg hy]
    -- Caso 1.2: y < 0, transformamos x - -y → x + y
    · rw [abs_of_neg hy, sub_neg_eq_add x y]
      -- La parte derecha es positiva.
      have hxy : 0 < x - y := by
        linarith
      rw [abs_of_pos hxy, abs_le]
      -- Convertimos la desigualdad de valores absolutos
      --   en dos inecuaciones lineales que linarith hace
      --   fácilmente.
      constructor <;> linarith
  -- Caso 2: x < 0
  · rw [abs_of_neg hx]
    obtain hy | hy := le_or_gt 0 y
    -- Caso 2.1: y ≥ 0
    · rw [abs_of_nonneg hy]
      have hxy : 0 < y - x := by
        linarith
      -- |x - y| → |y - x|, porque el último es positivo.
      nth_rw 2 [← abs_neg]
      rw [neg_sub, abs_of_pos hxy, abs_le]
      constructor <;> linarith
      -- Nuevamente, la desigualdad de valores absolutos
      --   pasa a ser un sistema de desigualdades lineales
      --   que resuelve linarith.

    -- Caso 2.2: y < 0
    -- Trivial al transformar |-x - -y| → |x - y|
    · rw [abs_of_neg hy,
        sub_neg_eq_add,
        ← abs_neg,
        add_comm,
        ← sub_eq_add_neg,
        neg_sub]
