module

public import FinitenessDiskDecayV1
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace FinitenessDiskJet

open Metric FinitenessDiskDecay

def space : Submodule ℂ (ℂ → ℂ) where
  carrier := {G | DifferentiableOn ℂ G (ball 0 1)}
  zero_mem' := differentiableOn_const _
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun a _ hf => hf.const_smul a

theorem diff_zero (G : space) : DifferentiableAt ℂ G.val 0 :=
  G.property.differentiableAt (ball_mem_nhds _ (by norm_num))

theorem dslope_add (F G : space) : dslope (F.val+G.val) 0 = dslope F.val 0 + dslope G.val 0 := by
  funext w
  by_cases hw : w=0
  · subst w
    simpa only [dslope_same, Pi.add_apply] using deriv_add (diff_zero F) (diff_zero G)
  · simp only [dslope_of_ne _ hw, slope_def_field, Pi.add_apply]
    ring

theorem dslope_smul (a : ℂ) (G : space) : dslope (a • G.val) 0 = a • dslope G.val 0 := by
  funext w
  by_cases hw : w=0
  · subst w
    simp only [dslope_same, Pi.smul_def, smul_eq_mul]
    exact deriv_const_mul a (diff_zero G)
  · simp only [dslope_of_ne _ hw, slope_def_field, Pi.smul_apply, smul_eq_mul]
    ring

noncomputable def shift : space →ₗ[ℂ] space where
  toFun G := ⟨dslope G.val 0,
    (Complex.differentiableOn_dslope (ball_mem_nhds _ (by norm_num))).mpr G.property⟩
  map_add' F G := Subtype.ext (dslope_add F G)
  map_smul' a G := Subtype.ext (dslope_smul a G)

noncomputable def evalZero : space →ₗ[ℂ] ℂ where
  toFun G := G.val 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def coefficient (n : ℕ) : space →ₗ[ℂ] ℂ := evalZero.comp (shift^n)

theorem shift_pow (n : ℕ) (G : space) : ((shift^n) G).val = quotient n G.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ']
      change dslope ((shift^n) G).val 0 = quotient (n+1) G.val
      rw [ih]
      exact (Function.iterate_succ_apply' (fun f : ℂ → ℂ => dslope f 0) n G.val).symm

theorem coefficient_eq (n : ℕ) (G : space) : coefficient n G = quotient n G.val 0 := by
  change ((shift^n) G).val 0 = _
  rw [shift_pow]

noncomputable def jet (n : ℕ) : space →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi (fun i => coefficient i.val)

/-- Any subspace detected by its first n actual holomorphic quotient
coordinates has dimension at most n. -/
theorem dimension_bound (V : Submodule ℂ space) (n : ℕ)
    (hzero : ∀ G : V, (∀ i < n, quotient i G.val.val 0 = 0) → G = 0) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ n := by
  let J : V →ₗ[ℂ] (Fin n → ℂ) := (jet n).comp V.subtype
  have hinj : Function.Injective J := by
    intro G H hGH
    apply sub_eq_zero.mp
    apply hzero (G-H)
    intro i hi
    have hJ : J (G-H) = 0 := by rw [map_sub J G H, hGH, sub_self]
    have he := congrFun hJ ⟨i,hi⟩
    simpa only [J, LinearMap.comp_apply, Submodule.subtype_apply, jet,
      LinearMap.pi_apply, coefficient_eq, Pi.zero_apply] using he
  have hfd : FiniteDimensional ℂ V := FiniteDimensional.of_injective J hinj
  let _ := hfd
  refine ⟨hfd, ?_⟩
  have hh := LinearMap.finrank_le_finrank_of_injective (f := J) hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hh

#print axioms coefficient_eq
#print axioms dimension_bound

end FinitenessDiskJet
