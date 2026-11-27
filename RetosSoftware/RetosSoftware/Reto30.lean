import RetosSoftware.RetosSoftware.Sucesiones
import RetosSoftware.RetosSoftware.Reto17
import Mathlib.Tactic

/-!
# Enunciado
Demostrar que si una sucesión aₙ es de Cauchy, entonces aₙ está acotada; es
decir, existe un M ∈ ℝ tal que para todo n ∈ ℕ, |aₙ| ≤ M.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

# Demostración
La demostración de esta propiedad es prácticamente idéntica a la del Reto 17.

Por ser aₙ de Cauchy se sabe que para un determinado k, todo
n ≥ k verifica que |aₙ - aₖ| < 1 (el valor 1 es arbitrario); esto nos da una
cota superior (en concreto M₂ := máx(|aₖ - 1|, |aₖ + 1|)) para |aₙ|.

Por otro lado, los casos restantes son finitos, luego puede tomarse el máximo
de |aₙ| cuando n < k como M₁ en esta ocasión; concretamente
M₁ := máx {|aₙ| : n < k}.

Finalmente, para que ambas desigualdades se cumplan se elige M := máx(M₁, M₂).
-/

theorem reto30 {a : ℕ → ℝ} (ha : SucCauchy a) : SucAcotada a := by
  obtain ⟨k, hk⟩ := ha 1 zero_lt_one
  let X := a k
  let S := (Finset.range k.succ).image |a|
  let M₁ := S.max' ⟨|a 0|, by
    rw [Finset.mem_image]
    use 0
    constructor
    · exact Finset.mem_range.mpr (Nat.succ_pos k)
    · rfl⟩
  let M₂ := max |X - 1| |X + 1|
  use max M₁ M₂
  intro n
  obtain hn | hn := lt_or_ge n k
  · apply le_max_of_le_left
    apply Finset.le_max'
    rw [Finset.mem_image]
    use n
    constructor
    · rw [Finset.mem_range]
      apply Nat.lt_succ_iff.mpr
      exact Nat.le_of_lt hn
    · rfl
  · apply le_max_of_le_right
    apply Reto17.abs_le_max_of_abs_sub_le
    apply hk
    · exact hn
    · rfl

#check reto30
