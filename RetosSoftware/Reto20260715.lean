import Mathlib.Tactic

/--
Sea G un grupo finito de orden n. Una función φ: G → G es un pseudoendomorfismo
si φ(xyz) = φ(x)φ(y)φ(z) para cualesquiera x, y, z ∈ G.

a) Si n es impar, demuéstrese que todo pseudoendomorfismo es un endomorfismo.
b) En el caso general, ¿es todo pseudoendomorfismo un endomorfismo?

Propuesto en la Olimpiada Matemática de Rumanía (2019): duodécimo grado, ronda
de distritos, problema 1.
Solución de Henry Díaz Bordón <henrydiazbordon@gmail.com>.

Para una solución en lenguaje natural, véase mi solución en el canal de
Telegram «Retos Matemáticos»: https://t.me/Retos_Matematicos/1/141633.
-/

theorem pseudoendomorphism_not_endomorphism_existence {G : Type*} [Group G]
  : (∃ φ : G → G, (∀ (x y z : G), φ (x * y * z) = φ (x) * φ (y) * φ (z))
    ∧ (∃ (x y : G), φ (x * y) ≠ φ (x) * φ (y)))
  ↔ (∃ g : G, g ≠ 1 ∧ g * g = 1)
  := by
  apply Iff.intro
  · intro ⟨φ, hφ_pseudo, hφ_not_endo⟩
    use φ (1)
    apply And.intro
    · intro hφ_1_eq_1
      obtain ⟨x, y, hxy⟩ := hφ_not_endo
      have hφ_endo := by
        calc
          φ (x * y) = φ (x * y * 1) := by rw [mul_one]
          _ = φ (x) * φ (y) * φ (1) := by rw [hφ_pseudo]
          _ = φ (x) * φ (y) := by rw [hφ_1_eq_1, mul_one]
      exact hxy hφ_endo
    · calc
        φ (1) * φ (1) = φ (1) * φ (1) * 1 := by rw [mul_one]
        _ = φ (1) * φ (1) * (φ (1) * (φ (1))⁻¹) := by rw [mul_inv_cancel]
        _ = (φ (1) * φ (1) * φ (1)) * (φ (1))⁻¹ := by rw [← mul_assoc]
        _ = (φ (1 * 1 * 1)) * (φ (1))⁻¹ := by rw [← hφ_pseudo]
        _ = φ (1) * (φ (1))⁻¹ := by rw [mul_one, mul_one]
        _ = 1 := by rw [mul_inv_cancel]
  · intro ⟨g, hg1, hg2⟩
    let φ : G → G := fun _ ↦ g
    use φ
    apply And.intro
    · intro x y z
      calc
        φ (x * y * z) = g := by rfl
        _ = g * 1 := by rw [mul_one]
        _ = g * (g * g) := by rw [hg2]
        _ = g * g * g := by rw [mul_assoc]
        _ = φ (x) * φ (y) * φ (z) := by rfl
    · use 1, 1
      intro hφ_endo
      have hg3 : g = 1 := by
        calc
          g = g * 1 := by rw [mul_one]
          _ = g * (g * g⁻¹) := by rw [mul_inv_cancel]
          _ = g * g * g⁻¹ := by rw [mul_assoc]
          _ = φ (1) * φ (1) * g⁻¹ := by rfl
          _ = φ (1 * 1) * g⁻¹ := by rw [← hφ_endo]
          _ = g * g⁻¹ := by rfl
          _ = 1 := by rw [mul_inv_cancel]
      exact hg1 hg3

theorem Reto20260715_a {G : Type*} [Group G] [Fintype G]
  (hG : ¬ (2 ∣ Fintype.card G))
  : ¬ (∃ φ : G → G, (∀ (x y z : G), φ (x * y * z) = φ (x) * φ (y) * φ (z))
        ∧ (∃ (x y : G), φ (x * y) ≠ φ (x) * φ (y)))
  := by
    intro hφ
    obtain ⟨g, hg1, hg2⟩ := pseudoendomorphism_not_endomorphism_existence.mp hφ
    exact hG (by
      -- he aquí el teorema de Lagrange
      have h' : orderOf g ∣ Fintype.card G := orderOf_dvd_card
      rw [← sq] at hg2
      rw [orderOf_eq_prime hg2 hg1] at h'
      exact h')

theorem Reto20260715_b {G : Type*} [Group G] [Fintype G]
  (hG : 2 ∣ Fintype.card G)
  : (∃ φ : G → G, (∀ (x y z : G), φ (x * y * z) = φ (x) * φ (y) * φ (z))
      ∧ (∃ (x y : G), φ (x * y) ≠ φ (x) * φ (y)))
  := by
    apply pseudoendomorphism_not_endomorphism_existence.mpr
    -- y aquí el teorema de Cauchy
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 hG
    use g
    obtain ⟨h1, h2⟩ := orderOf_eq_prime_iff.mp hg
    rw [← sq]
    exact ⟨h2, h1⟩

#check pseudoendomorphism_not_endomorphism_existence
#check Reto20260715_a
#check Reto20260715_b
