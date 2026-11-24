import RetosSoftware.RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
# Enunciado
Una subsucesión se obtiene aplicando a la sucesión original una función de
extracción; es decir, una función φ: ℕ → ℕ estrictamente creciente. Por ejemplo,
la subsucesión
  u₀, u₂, u₄, ⋯
se obtiene con la función de extracción φ definida por φ(n) = 2n.

Demostrar que si
  ∀ n, φ(n) < φ(n + 1),
entonces φ es una función de extracción.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

# Demostración
Mathlib para un φ: α → β, define StrictMono φ como que para todo a, b tal que
a < b se verifique que φ a < φ b. Así, dada la condición podemos proceder
inductivamente para demostrar que φ(n) < φ(n + k) para cualquier k ∈ ℕ, luego
  φ(a) < φ(a + (b - a)) = φ(b).
-/

theorem Reto32 {φ : ℕ → ℝ} (hφ : ∀ n, φ n < φ (n + 1))
  : StrictMono φ
  := by
  intro a b hab
  have (n : ℕ) (k : ℕ) (hk : k > 0) : φ n < φ (n + k) := by
    induction k with
    | zero => exfalso; exact LT.lt.false (a := 0) hk
    | succ k' hφk' =>
      by_cases h : k' = 0
      · rw [h, zero_add]; exact hφ n
      · have : k' > 0 := Nat.pos_of_ne_zero h
        calc
          φ n < φ (n + k')      := hφk' this
          _   < φ (n + k' + 1)  := by rel [hφ (n + k')]
          _   = φ (n + (k'+ 1)) := by rw [add_assoc]
  calc
    φ a < φ (a + (b - a)) := this a (b - a) (Nat.sub_pos_of_lt hab)
    _ = φ b := by rw [Nat.add_sub_cancel' (le_of_lt hab)]

#check Reto32
