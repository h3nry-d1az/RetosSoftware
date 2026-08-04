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
  · rw [abs_of_nonneg hx]
    obtain hy | hy := le_or_gt 0 y
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg hy]
      grind
  · rw [abs_of_neg hx]
    obtain hy | hy := le_or_gt 0 y
    · rw [abs_of_nonneg hy]
      grind
    · rw [abs_of_neg hy]
      grind
