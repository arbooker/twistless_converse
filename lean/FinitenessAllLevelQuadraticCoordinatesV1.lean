module

public import FinitenessAllLevelFiniteRowsV1
public import FinitenessAllLevelIndexedConstraintsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelQuadraticCoordinates

open Complex Set Module

abbrev Coeff (n : ℕ) := ℂ × ((Fin n → ℂ) × (Fin n → Fin n → ℂ))

def evaluate {n : ℕ} (v : Fin n → ℂ) : Coeff n →ₗ[ℂ] ℂ where
  toFun c := c.1 + (∑ i, c.2.1 i * v i) + ∑ i, ∑ j, c.2.2 i j * v i * v j
  map_add' c d := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c d := by
    change c * d.1 + (∑ i, (c * d.2.1 i) * v i) +
      (∑ i, ∑ j, (c * d.2.2 i j) * v i * v j) =
        c * (d.1 + (∑ i, d.2.1 i * v i) + ∑ i, ∑ j, d.2.2 i j * v i * v j)
    simp only [mul_add, Finset.mul_sum, mul_assoc]

def constant {n : ℕ} (c : ℂ) : Coeff n := (c, 0, 0)
def linear {n : ℕ} (c : Fin n → ℂ) : Coeff n := (0, c, 0)
def product {n : ℕ} (c d : Fin n → ℂ) : Coeff n := (0, 0, fun i j => c i * d j)

@[simp] theorem evaluate_constant {n : ℕ} (v : Fin n → ℂ) (c : ℂ) :
    evaluate v (constant c) = c := by simp [evaluate, constant]

@[simp] theorem evaluate_linear {n : ℕ} (v c : Fin n → ℂ) :
    evaluate v (linear c) = ∑ i, c i * v i := by simp [evaluate, linear]

theorem evaluate_product {n : ℕ} (v c d : Fin n → ℂ) :
    evaluate v (product c d) = (∑ i, c i * v i) * ∑ j, d j * v j := by
  simp only [evaluate, LinearMap.coe_mk, AddHom.coe_mk, product, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {n : ℕ} (b : Basis (Fin n) ℂ E) {U : Set ℂ}

def Representable (H : ℂ × E → ℂ) : Prop :=
  ∃ c : ℂ → Coeff n, AnalyticOnNhd ℂ c U ∧ ∀ z v, evaluate (b.repr v) (c z) = H (z, v)

theorem represent_constant {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) :
    Representable b (U := U) (fun t => g t.1) := by
  refine ⟨fun z => constant (g z), ?_, fun z v => evaluate_constant _ _⟩
  intro z hz
  exact (hg z hz).prod analyticAt_const

theorem linear_basis_sum (T : E →ₗ[ℂ] ℂ) (v : E) :
    ∑ i, T (b i) * b.repr v i = T v := by
  have he := congrArg T (b.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm (b.repr v _)] using he

theorem represent_linear (T : ℂ → E →ₗ[ℂ] ℂ)
    (hT : ∀ v, AnalyticOnNhd ℂ (fun z => T z v) U) :
    Representable b (U := U) (fun t => T t.1 t.2) := by
  refine ⟨fun z => linear (fun i => T z (b i)), ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.prod ((AnalyticAt.pi (fun i => hT (b i) z hz)).prod analyticAt_const)
  · intro z v
    rw [evaluate_linear]
    exact linear_basis_sum b (T z) v

theorem represent_product (T S : ℂ → E →ₗ[ℂ] ℂ)
    (hT : ∀ v, AnalyticOnNhd ℂ (fun z => T z v) U)
    (hS : ∀ v, AnalyticOnNhd ℂ (fun z => S z v) U) :
    Representable b (U := U) (fun t => T t.1 t.2 * S t.1 t.2) := by
  refine ⟨fun z => product (fun i => T z (b i)) (fun i => S z (b i)), ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.prod (analyticAt_const.prod (AnalyticAt.pi (fun i =>
      AnalyticAt.pi (fun j => (hT (b i) z hz).mul (hS (b j) z hz)))))
  · intro z v
    rw [evaluate_product, linear_basis_sum, linear_basis_sum]

theorem Representable.sub {H G : ℂ × E → ℂ}
    (hH : Representable b (U := U) H) (hG : Representable b (U := U) G) :
    Representable b (U := U) (fun t => H t - G t) := by
  obtain ⟨c, hc, he⟩ := hH
  obtain ⟨d, hd, hf⟩ := hG
  exact ⟨fun z => c z - d z, hc.sub hd, fun z v => by rw [map_sub, he, hf]⟩

theorem Representable.const_mul {H : ℂ × E → ℂ}
    (hH : Representable b (U := U) H) (d : ℂ) :
    Representable b (U := U) (fun t => d * H t) := by
  obtain ⟨c, hc, he⟩ := hH
  refine ⟨fun z => d • c z, analyticOnNhd_const.smul hc, ?_⟩
  intro z v
  rw [map_smul, he, smul_eq_mul]

#print axioms evaluate
#print axioms represent_linear
#print axioms represent_product

end FinitenessAllLevelQuadraticCoordinates
