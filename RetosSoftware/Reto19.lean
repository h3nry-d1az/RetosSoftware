import RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
Demostrar que las sucesiones convergentes son de Cauchy.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Al ser la sucesión dada convergente, para cualquier ε > 0 se tiene un N ∈ ℕ
a partir del cual todos los elementos de la sucesión están en el intervalo de
radio ε centrado en L; aₙ ∈ (L-ε, L+ε). El diámetro de este intervalo es 2ε,
luego cualesquiera dos valores están a una distancia de a lo sumo esta cantidad
(siempre menos por ser un intervalo abierto). Así, es suficiente con escoger
el N correspondiente a ε/2 en la hipótesis de convergencia.
-/

theorem Reto19 {a : ℕ → ℝ} (ha : SucConvergente a) : SucCauchy a := by
  intro ε hε
  obtain ⟨L, hL⟩ := ha
  obtain ⟨N, hN⟩ := hL (ε/2) (by positivity)
  use N
  -- Desde aquí `grind` puede completar la demostración
  intro p hp q hq
  have h₁ : -(ε/2) < a p - L ∧ a p - L < ε/2 := abs_lt.mp (hN p hp)
  have h₂ : -(ε/2) < a q - L ∧ a q - L < ε/2 := abs_lt.mp (hN q hq)
  rw [abs_lt]
  -- `constructor <;> linarith` termina ambas ramas
  constructor
  · calc
      -ε = -(ε/2) - (ε/2) := by field
      _ < a p - L - (ε/2) := by rel [h₁.left]
      _ < (a p - L) - (a q - L) := by rel [sub_lt_sub_left (c := a p - L) h₂.right]
      _ = a p - a q := by ring
  · calc
      a p - a q = (a p - L) - (a q - L) := by ring
      _ < (ε/2) - (a q - L) := by rel [h₁.right]
      _ < (ε/2) - -(ε/2) := by rel [sub_lt_sub_left (c := ε/2) h₂.left]
      _ = ε := by field

#check Reto19
