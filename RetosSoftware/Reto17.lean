import RetosSoftware.Sucesiones
import Mathlib.Tactic

/--
Demostrar que las sucesiones convergentes están acotadas; es decir, que si
existe un L ∈ ℝ tal que L es el límite de la sucesión aₙ, entonces existe un
M ∈ ℝ tal que para todo n ∈ ℕ, |aₙ| ≤ M.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Por la existencia de un límite L de aₙ se sabe que para un determinado k, todo
n ≥ k verifica que |aₙ - L| < 1 (el valor 1 es arbitrario); esto nos da una
cota superior (en concreto M₂ := máx(|L - 1|, |L + 1|)) para |aₙ|.

Por otro lado, los casos restantes son finitos, luego puede tomarse el máximo
de |aₙ| cuando n < k como M₁ en esta ocasión; concretamente
M₁ := máx {|aₙ| : n < k}.

Finalmente, para que ambas desigualdades se cumplan se elige M := máx(M₁, M₂).
-/

lemma abs_sub_le_of_abs_le_max {a b c : ℝ} (h : |a - b| < c)
  : |a| ≤ max |b - c| |b + c|
  := by
  obtain ⟨h₁, h₂⟩ := abs_sub_lt_iff.mp h -- |a - b| < c ⊢ b - c < a < b + c
  apply abs_le_max_abs_abs <;> linarith

theorem Reto17 {a : ℕ → ℝ} (ha : SucConvergente a) : SucAcotada a := by
  obtain ⟨L, hL⟩ := ha
  obtain ⟨k, hk⟩ := hL 1 (by norm_num)
  let S := (Finset.range k.succ).image (abs ∘ a) -- S := {|aₙ| : n ≤ k}
  let M₁ := S.max' ⟨|a 0|, by
    rw [Finset.mem_image]
    use 0
    constructor
    · exact Finset.mem_range.mpr (Nat.succ_pos k)
    · rfl⟩
  /- `Finset.max'` requiere una demostración de que el argumento no es el
  conjunto vacío; existe `Finset.max`, pero retorna `WithBot α`, que es similar
  a `Option α` salvo que los resultados inválidos son representados por `⊥` en
  lugar de `none`. -/
  let M₂ := max |L - 1| |L + 1|
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
  · exact le_max_of_le_right (abs_sub_le_of_abs_le_max (hk n hn))

#check Reto17
