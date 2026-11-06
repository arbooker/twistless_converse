module

public import AsymptoticQuotientNewSpaceV1
public import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
@[expose] public noncomputable section

open InnerProductSpace
open scoped InnerProduct lp

namespace QuantitativeNewGap

/-- A finite-dimensional row has a genuine lower bound on the orthogonal
complement of its kernel. The constant is constructed from the inverse on
that complement; no spectral-gap premise is used. -/
theorem finite_row_gap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) :
    ∃ c : ℝ, 0<c ∧ ∀ v : E, c*‖v-T.ker.starProjection v‖≤‖T v‖ := by
  let S := T.ker
  let A : Sᗮ →ₗ[ℂ] F := T.toLinearMap.comp Sᗮ.subtype
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    apply bot_unique
    intro x hx
    have hxS : (x:E)∈S := hx
    have hz : (x:E)=0 := by
      have hmem : (x:E)∈S⊓Sᗮ := ⟨hxS,x.property⟩
      rw [S.inf_orthogonal_eq_bot] at hmem
      exact hmem
    exact Subtype.ext hz
  obtain ⟨K,hK,hA⟩ := A.injective_iff_antilipschitz.mp hinj
  have hKr : (0:ℝ)<K := hK
  refine ⟨(K:ℝ)⁻¹,inv_pos.mpr hKr,?_⟩
  intro v
  let w : Sᗮ := ⟨v-S.starProjection v,S.sub_starProjection_mem_orthogonal v⟩
  have hb := ZeroHomClass.bound_of_antilipschitz A hA w
  have hzero : T (S.starProjection v)=0 := S.starProjection_apply_mem v
  have he : A w=T v := by simp [A,w,map_sub,hzero]
  change ‖v-S.starProjection v‖≤(K:ℝ)*‖A w‖ at hb
  rw [he] at hb
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hKr.le)
  simpa [← mul_assoc,hKr.ne'] using hh

/-- Two actual rows on a finite-dimensional Hilbert space control distance
to their common kernel. This is the energy form used by old averages. -/
theorem finite_pair_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (B C : E →L[ℂ] E) :
    ∃ γ : ℝ, 0<γ ∧ ∀ v : E,
      γ*‖v-((B.adjoint.comp B)+(C.adjoint.comp C)).ker.starProjection v‖^2 ≤
        ‖B v‖^2+‖C v‖^2 := by
  let T := B.prod C
  obtain ⟨c,hc,hbound⟩ := finite_row_gap T
  have hk : T.ker=((B.adjoint.comp B)+(C.adjoint.comp C)).ker := by
    ext v
    rw [AsymptoticJointKernel.mem_ker_gram_add]
    change (B v,C v)=(0,0) ↔ _
    simp only [Prod.mk.injEq]
  refine ⟨c^2,sq_pos_of_pos hc,?_⟩
  intro v
  have hb := hbound v
  have hb' : c*‖v-((B.adjoint.comp B)+(C.adjoint.comp C)).ker.starProjection v‖≤‖T v‖ := by
    simpa only [hk] using hb
  have hn : ‖T v‖=max ‖B v‖ ‖C v‖ := rfl
  have hs := sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _) |>.mpr hb'
  rw [mul_pow,hn] at hs
  apply hs.trans
  rcases le_total ‖B v‖ ‖C v‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖B v‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖C v‖]

open AsymptoticNestedQuotients AsymptoticQuotientOperators

/-- On a finite coset block the literal two-old-average operator has a
positive gap away from the previously defined exact new projection. -/
theorem finite_coset_old_average_gap {G : Type*} [Group G]
    {H J K : Subgroup G} (hJ : H≤J) (hK : H≤K)
    [H.FiniteIndex] :
    ∃ γ : ℝ, 0<γ ∧ ∀ v : ℓ²(Classes H,ℂ),
      γ*‖v-(newSpace hJ hK).starProjection v‖^2 ≤
        ‖(space hJ).starProjection v‖^2+‖(space hK).starProjection v‖^2 := by
  let : Finite (Classes H) := Finite.of_equiv (G ⧸ H)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  let : Fintype (Classes H) := Fintype.ofFinite _
  let e : ℓ²(Classes H,ℂ) →ₗ[ℂ] (Classes H → ℂ) :=
    LinearMap.pi (fun i => lp.evalₗ (fun _ : Classes H => ℂ) 2 i)
  let : FiniteDimensional ℂ ℓ²(Classes H,ℂ) :=
    FiniteDimensional.of_injective e (fun _ _ h => by ext i; exact congrFun h i)
  exact finite_pair_gap (space hJ).starProjection (space hK).starProjection

#print axioms finite_row_gap
#print axioms finite_pair_gap
#print axioms finite_coset_old_average_gap

end QuantitativeNewGap
