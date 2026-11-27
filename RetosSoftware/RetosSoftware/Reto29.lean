import RetosSoftware.RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
# Enunciado
Demostrar que si aₙ y bₙ son sucesiones de Cauchy, entonces su suma aₙ + bₙ
también lo es.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

# Demostración
Fíjese ε > 0; nótese que
  |aₙ + bₙ - aₘ - bₘ| ≤ |aₙ - aₘ| + |bₙ - bₘ|,
luego tomando N = máx(N₁, N₂) donde N₁ y N₂ son aquellos que hacen que ambos
sumandos sean menores que ε/2 se tiene que lo anterior es menor que ε.
-/

theorem reto29 {a b : ℕ → ℝ}
  (ha : SucCauchy a)
  (hb : SucCauchy b)
  : SucCauchy (a + b)
  := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (half_pos hε)
  let N := max N₁ N₂
  have hN₁N : N₁ ≤ N := le_max_left N₁ N₂
  have hN₂N : N₂ ≤ N := le_max_right N₁ N₂
  use N
  intro p hp q hq
  calc
    _ = |(a p + b p) - (a q + b q)| := rfl
    _ = |(a p - a q) + (b p - b q)| := by ring_nf
    _ ≤ |a p - a q| + |b p - b q| := abs_add_le (a p - a q) (b p - b q)
    _ < ε / 2 + ε / 2 := by rel [hN₁ p (trans hp hN₁N) q (trans hq hN₁N),
                                 hN₂ p (trans hp hN₂N) q (trans hq hN₂N)]
    _ = ε := add_halves ε

#check reto29
