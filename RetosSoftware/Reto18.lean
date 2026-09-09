import RetosSoftware.Reto17
import Mathlib.Tactic

/--
Demostrar que que si la sucesión aₙ converge a L y bₙ converge a M, entonces
aₙbₙ converge a LM.

Propuesto por José A. Alonso Jiménez.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

----------
Demostración en lenguaje natural:

Se empieza probando el caso particular en el que alguno de los dos límites es
0, sin pérdida de generalidad sea lím aₙ = 0. Se busca que para todo ε > 0
exista N ∈ ℕ tal que n ≥ ℕ implique que
  |aₙbₙ - 0| = |aₙ|·|bₙ| < ε;
como |aₙ| es arbitrariamente pequeño, basta con acotar |bₙ| por un valor
positivo B y tomar |aₙ| ≤ ε/(2B). En particular, por
`abs_sub_le_of_abs_le_max` (véase el reto 17) se consigue lo primero tomando
ε = 1, y en definitiva
  |aₙ|·|bₙ| < ε/(2B)·B = ε/2 < ε.

En el caso general para todo ε > 0, se busca un N ∈ ℕ que satisfaga que si
n ≥ N, |aₙbₙ - LM| < ε. La idea fundamental de la demostración es el hecho de
que, al contar con que aₙ → L, entonces existe N₁ a partir del cual |aₙ - L|
es tan pequeño como se desee (y análogamente un N₂ para bₙ), luego interesa
escribir la cantidad dentro del valor absoluto en término de estos dos.

Así:
  |aₙbₙ - LM| = |(aₙ - L)(bₙ - M) + aₙM + bₙL - 2LM|
             = |(aₙ - L)(bₙ - M) + M(aₙ - L) + L(bₙ - M)|
             ≤ |aₙ - L| |bₙ - M| + |M|·|aₙ - L| + |L|·|bₙ - M|
             = ε₁ε₂ + |M|ε₁ + |L|ε₂
             < ε,
luego tomando ε₁ = ε/(4|M|), ε₂ = ε/(4|L|) se verifica la inecuación para
  ε²/(16|LM|) + ε/2 < ε ↔ ε < 8|LM|;
en cualquier caso, con tomar ε' = min{ε, 4|LM|} y sustituir ε' por ε en la
definición de ε₁ y ε₂ basta.

Finalmente, cada εᵢ garantiza un Nᵢ, luego N = max{N₁, N₂}.
-/

lemma limSuc_zero_prod_limSuc_eq_zero {a b : ℕ → ℝ} {L : ℝ}
  (ha : LimSuc a 0)
  (hb : LimSuc b L)
  : LimSuc (a*b) 0
  := by
  intro ε hε
  let ⟨N₁, hN₁⟩ := hb 1 (by norm_num)
  let B := max |L - 1| |L + 1|
  -- toca demostrar que B > 0; aunque `grind` lo puede hacer también
  have hB₁ : B ≠ 0 := by
    intro hB
    have h₁ : L - 1 = 0 := by
      apply abs_eq_zero.mp
      apply le_antisymm
      · rw [← hB]
        exact le_max_left |L - 1| |L + 1|
      · exact abs_nonneg (L - 1)
    have h₂ : L + 1 = 0 := by
      apply abs_eq_zero.mp
      apply le_antisymm
      · rw [← hB]
        exact le_max_right |L - 1| |L + 1|
      · exact abs_nonneg (L + 1)
    linarith
  have hB₂ : ∀ n ≥ N₁, |b n| ≤ B :=
    fun (n : ℕ) (hn : n ≥ N₁) => abs_sub_le_of_abs_le_max (hN₁ n hn)
  -- cota superior B para |bₙ|, positiva porque |L+1| y |L-1| alguno es >0
  let ⟨N₂, hN₂⟩ := ha (ε / (2 * B)) (by positivity)
  -- la cota superior para |aₙ| es ε / (2*B)
  use max N₁ N₂
  intro n hn
  have hn₁ : n ≥ N₁ := trans hn (le_max_left N₁ N₂)
  have hn₂ : n ≥ N₂ := trans hn (le_max_right N₁ N₂)
  calc
    _ = |a n * b n| := by rw [sub_zero]; rfl
    _ = |a n| * |b n| := by rw [abs_mul]
    _ = |a n - 0| * |b n| := by norm_num
    _ ≤ ε / (2 * B) * |b n| := by rel [hN₂ n hn₂]
    _ ≤ ε / (2 * B) * B := by rel [hB₂ n hn₁]
    _ = ε / 2 := by field
    _ < ε := by linarith

theorem Reto18 {a b : ℕ → ℝ} {L M : ℝ}
  (ha : LimSuc a L)
  (hb : LimSuc b M)
  : LimSuc (a*b) (L*M)
  := by
  by_cases hL : L = 0
  case pos =>
    rw [hL, zero_mul]
    exact limSuc_zero_prod_limSuc_eq_zero (Eq.subst hL ha) hb
  -- si L = 0, el lema anterior resuelve la demostración
  by_cases hM : M = 0
  case pos =>
    rw [hM, mul_zero, mul_comm]
    exact @limSuc_zero_prod_limSuc_eq_zero b a L (Eq.subst hM hb) ha
  -- ídem si M = 0, tenemos así que |L|, |M| > 0
  have hL : |L| > 0 := by positivity
  have hM : |M| > 0 := by positivity
  intro ε₀ hε₀
  let ε := min ε₀ (4 * |L| * |M|)
  have hε : ε > 0 := by positivity
  let ε₁ := ε/(4*|M|)
  let ε₂ := ε/(4*|L|)
  let ⟨N₁, hN₁⟩ := ha ε₁ (by positivity)
  let ⟨N₂, hN₂⟩ := hb ε₂ (by positivity)
  use max N₁ N₂
  intro n hn
  have hnN₁ : n ≥ N₁ := trans hn (le_max_left N₁ N₂)
  have hnN₂ : n ≥ N₂ := trans hn (le_max_right N₁ N₂)
  calc
    _ = |a n * b n - L * M| := rfl
    _ = |(a n - L) * (b n - M) + (M*(a n - L) + L*(b n - M))| := by ring_nf
    _ ≤ |(a n - L) * (b n - M)| + |M * (a n - L) + L * (b n - M)| := by
      rel [abs_add_le ((a n - L) * (b n - M)) (M * (a n - L) + L * (b n - M))]
    _ ≤ |(a n - L) * (b n - M)| + |M * (a n - L)| + |L * (b n - M)| := by
      rw [add_assoc, add_le_add_iff_left |(a n - L) * (b n - M)|]
      rel [abs_add_le (M * (a n - L)) (L * (b n - M))]
    _ = |a n - L| * |b n - M| + |M| * |a n - L| + |L| * |b n - M| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ < ε₁ * ε₂ + |M| * ε₁ + |L| * ε₂ := by rel [hN₁ n hnN₁, hN₂ n hnN₂]
    _ = ε * ε / (16 * |L| * |M|) + ε / 2 := by unfold ε₁ ε₂; field
    _ ≤ ε * (4 * |L| * |M|) / (16 * |L| * |M|) + ε / 2 := by
      rel [min_le_right ε₀ (4 * |L| * |M|)]
    _ = ε / 4 + ε / 2 := by field
    _ < ε := by linarith
    _ ≤ ε₀ := min_le_left ε₀ (4 * |L| * |M|)

#check Reto18
