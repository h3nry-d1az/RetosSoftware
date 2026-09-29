import RetosSoftware.Sucesiones
import Mathlib.Tactic

/-!
Una subsucesión se obtiene aplicando a la sucesión original una función de
extracción; es decir, una función φ : ℕ → ℕ estrictamente creciente. Por
ejemplo, la subsucesión
  u₀, u₂, u₄, u₆, ⋯
se obtiene con la función de extracción φ definida por φ(n) = 2n.

Demostrar que toda subsucesión de una sucesión convergente converge al mismo
límite que la sucesión.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Nótese en primer lugar que por ser φ monotónica creciente en ℕ es inmediato que
φ(n) ≥ n para cualquier n ∈ ℕ.

Así, se pide que dado ε > 0 encontrar un N para el que |v n - L| = |u(φ(n)) - L|
< ε. Porque lim u = L, existe un N a partir del cual |u(n) - L| < ε, pero por
el primer hecho también |u(φ(n)) - L| < ε, luego es suficiente tomar este N.
Como se quería demostrar.
-/

theorem Reto21 {L : ℝ} {u v : ℕ → ℝ}
  (hv : SubSucesion v u)
  (hL : LimSuc u L)
  : LimSuc v L := by
  intro ε hε
  let ⟨φ, hφ₁, hφ₂⟩ := hv
  let ⟨N, hN⟩ := hL ε hε
  use N
  intro n hn
  rw [hφ₂]
  apply hN
  calc
    φ n ≥ n := StrictMono.le_apply (x := n) hφ₁
    _ ≥ N := hn

#check Reto21

