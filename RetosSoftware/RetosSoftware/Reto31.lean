import RetosSoftware.RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
# Enunciado
Sea aₙ la sucesión identidad; es decir, que para todo n ∈ ℕ, aₙ = n.
Demostrar que aₙ no tiene subsucesiones convergentes.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

# Demostración
Asumiendo que existe una subsucesión bₙ de aₙ que es convergente a L, tenemos
que existe un N a partir del cual |bₙ - L| < 1 al reemplazar ε por 1 en la
definición de convergencia. Asimismo, tenemos que para n = máx(N, ⌈L⌉₊ + 1)
se verifica que
  |bₙ - L| = |a(φ(n)) - L| = |φ(n) - L| ≥ |n - L| ≥ |⌈L⌉₊ + 1 - L| = 1,
lo que supone una contradicción.
-/

theorem reto31 {a : ℕ → ℝ} (ha : ∀ n, a n = n)
  : ¬∃ b, SubSucesion b a ∧ SucConvergente b
  := by
  intro ⟨b, ⟨φ, hφ₁, hφ₂⟩, ⟨L, hL⟩⟩
  obtain ⟨N, hN⟩ := hL 1 (one_pos)
  let n := max N (Nat.ceil L + 1)
  suffices h : |b n - L| ≥ 1 from
    (not_lt_of_ge h) (hN n (le_max_left N (Nat.ceil L + 1)))
  suffices h : b n - L ≥ 1 from LE.le.trans (by norm_num : 1 ≤ |(1 : ℝ)|)
    (abs_le_abs h (LE.le.trans (by norm_num : -1 ≤ (1 : ℝ)) h))
  calc
    _ = a (φ n) - L := by rw [hφ₂]; rfl
    _ = φ n - L := by rw [ha]
    _ ≥ n - L := by rel [StrictMono.le_apply hφ₁]
    _ ≥ (Nat.ceil L + 1) - L := by aesop
    _ ≥ L + 1 - L := by rel [Nat.le_ceil L]
    _ = 1 := by rw [add_comm, ← add_sub, sub_self, add_zero]

#check reto31
