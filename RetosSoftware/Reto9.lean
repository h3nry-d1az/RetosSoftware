import RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
Demostrar que si una sucesión aₙ converge tanto a L como a M, entonces L = M.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Por converger aₙ a L se tiene que existe un N₁ a partir del cual |aₙ - L| < ε/2
para todo ε; análogamente existe un N₂ para el que |aₙ - M| < ε/2. Así,
  |L - M| = |(L - aₙ) + (aₙ - M)| ≤ |L - aₙ| + |aₙ - M| = ε,
luego L = M, QED.
-/

lemma abs_sub_le_forall_of_eq {x y : ℝ}
  (hε : ∀ ε > 0, |x - y| ≤ ε)
  : x = y := by
  obtain h | h := LE.le.lt_or_eq (abs_nonneg (x - y))
  · exfalso
    have h₁ : |x - y| ≤ |x - y| / 2 := hε (|x - y| / 2) (half_pos h)
    have h₂ : |x - y| > |x - y| / 2 := half_lt_self h
    exact (LE.le.not_gt h₁) h₂
  · symm at h
    rw [abs_eq_zero] at h
    rw [sub_eq_zero] at h
    exact h

theorem Reto9 {L M : ℝ} {a : ℕ → ℝ}
  (hL : LimSuc a L)
  (hM : LimSuc a M)
  : L = M := by
  apply abs_sub_le_forall_of_eq
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hL (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hM (ε / 2) (half_pos hε)
  let N := max N₁ N₂
  calc
    |L - M| = |(L - a N) + (a N - M)| := by ring_nf
    _ ≤ |L - a N| + |a N - M| := by rel [abs_add_le (L - a N) (a N - M)]
    _ = |a N - L| + |a N - M| := by rw [abs_sub_comm (a N) L]
    _ ≤ ε / 2 + |a N - M| := by rel [hN₁ N (le_max_left N₁ N₂)]
    _ ≤ ε / 2 + ε / 2 := by rel [hN₂ N (le_max_right N₁ N₂)]
    _ = ε := add_halves ε

#check Reto9

