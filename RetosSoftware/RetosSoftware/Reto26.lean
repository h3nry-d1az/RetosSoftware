import RetosSoftware.RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
Demostrar que si la sucesión aₙ converge a 0 y la sucesión bₙ está acotada (no
necesariamente es convergente), entonces la sucesión aₙ·bₙ converge a 0.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Si la cota de bₙ es cero, entonces bₙ = 0 para cualquier n por ser el positivo-
definido el valor absoluto, en cuyo caso el resultado es trivial y podemos
tomar N = 0, por ejemplo.

Asumimos, pues, que la |bₙ| ≤ M para algún M > 0, en cuyo caso podemos tomar el
N resultante de imponer ε' = ε / (2 * M) a aₙ, y de esta forma se verifica que
  |aₙ · bₙ| ≤ ε / (2 * M) * M = ε / 2 < ε,
como se quería demostrar.
-/

theorem Reto26 {a b : ℕ → ℝ}
  (ha : a ⟹ 0)
  (hb : SucAcotada b)
  : (a * b) ⟹ 0
  := by
  intro ε hε
  obtain ⟨M, hM⟩ := hb
  by_cases hM₀ : M = 0
  -- si M = 0, entonces bₙ = 0 y el resultado es trivial
  case pos =>
    have hb₀ : ∀ n, b n = 0 := by
      intro n
      apply abs_eq_zero.mp
      apply le_antisymm
      · exact Eq.subst hM₀ (hM n)
      · exact abs_nonneg (b n)
    use 0
    intro n hn
    calc
      _ = |a n * b n| := by rw [sub_zero]; rfl
      _ = 0 := by rw [hb₀, mul_zero, abs_zero]
      _ < ε := hε
  -- si no, M ha de ser positivo y podemos escoger N sin problemas
  have hM_pos : M > 0 := by
    by_contra h
    obtain h' | h' := le_iff_lt_or_eq.mp (le_of_not_gt h)
    · exfalso
      suffices h : ¬M < 0 from False.elim (h h')
      rw [not_lt]
      exact LE.le.trans (abs_nonneg (b 0)) (hM 0)
    · exact False.elim (hM₀ h')
  obtain ⟨N, hN⟩ := ha (ε / (2 * M)) (by positivity)
  use N
  intro n hn
  calc
    _ = |a n * b n| := by rw [sub_zero]; rfl
    _ = |a n| * |b n| := by rw [abs_mul]
    _ ≤ |a n - 0| * M := by rw [sub_zero]; rel [hM n]
    _ ≤ (ε / (2 * M)) * M := by rel [hN n hn]
    _ = ε / 2 := by field
    _ < ε := half_lt_self hε

#check Reto26
