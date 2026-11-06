module

public import AsymptoticStackSubgroupSupportV1
public import AsymptoticPolarRangeV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticMixing

open AsymptoticSubgroupSupport AsymptoticObservationStack AsymptoticPolarIsometry
open AsymptoticRegularTrace ContinuousLinearMap InnerProductSpace
open scoped lp InnerProduct

variable {G ι : Type*} [Group G] [Fintype ι]

theorem translation_norm (a : G) (v : ℓ²(G,ℂ)) : ‖translation a v‖=‖v‖ :=
  (AsymptoticOrbitBranch.reindex (Equiv.mulLeft a)).norm_map v

theorem translation_adjoint (a : G) : (translation a).adjoint=translation a⁻¹ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  have he := (AsymptoticOrbitBranch.reindex (Equiv.mulLeft a)).inner_map_map (translation a⁻¹ v) w
  have hi : translation a (translation a⁻¹ v)=v := by
    ext g
    simp only [translation_apply,← mul_assoc,inv_mul_cancel,one_mul]
  change ⟪translation a (translation a⁻¹ v),translation a w⟫_ℂ=⟪translation a⁻¹ v,w⟫_ℂ at he
  rw [hi] at he
  exact he.symm

theorem translated_inner (a b : G) (v w : ℓ²(G,ℂ)) :
    ⟪translation a v,translation b w⟫_ℂ=⟪v,translation (b*a⁻¹) w⟫_ℂ := by
  rw [← adjoint_inner_right,translation_adjoint]
  congr 1
  ext g
  simp only [translation_apply,mul_assoc]

/-- The sum of translated observation rows. Its labels are retained in
the source stack until the explicit aggregation map is applied. -/
noncomputable def mixed (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := ∑ i,(translation (a i)).comp (L i)

noncomputable def aggregation (a : ι → G) :
    PiLp 2 (fun _ : ι => ℓ²(G,ℂ)) →L[ℂ] ℓ²(G,ℂ) :=
  (stack (fun i => translation (a i)⁻¹)).adjoint

theorem aggregation_comp_stack (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    (aggregation a).comp (stack L)=mixed a L := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  rw [comp_apply,aggregation,adjoint_inner_right,PiLp.inner_apply]
  simp only [stack_apply,mixed,sum_apply,comp_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (translation (a i)⁻¹).adjoint_inner_right,translation_adjoint,inv_inv]

theorem aggregation_norm (a : ι → G) : ‖aggregation a‖≤Real.sqrt (Fintype.card ι) := by
  rw [aggregation,adjoint.norm_map]
  apply opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hs : ‖stack (fun i => translation (a i)⁻¹) v‖^2=(Fintype.card ι:ℝ)*‖v‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [stack_apply,translation_norm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hn : 0≤(Fintype.card ι:ℝ) := Nat.cast_nonneg _
  have he := Real.sq_sqrt hn
  nlinarith [norm_nonneg (stack (fun i => translation (a i)⁻¹) v),
    mul_nonneg (Real.sqrt_nonneg (Fintype.card ι)) (norm_nonneg v)]

noncomputable def normalizedAggregation (a : ι → G) :
    PiLp 2 (fun _ : ι => ℓ²(G,ℂ)) →L[ℂ] ℓ²(G,ℂ) :=
  (((Real.sqrt (Fintype.card ι))⁻¹:ℝ):ℂ) • aggregation a

theorem normalizedAggregation_norm (a : ι → G) : ‖normalizedAggregation a‖≤1 := by
  rw [normalizedAggregation,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (aggregation_norm a) (by positivity)).trans
  by_cases hz : Real.sqrt (Fintype.card ι)=0
  · simp only [hz,inv_zero,mul_zero,zero_le_one]
  · rw [inv_mul_cancel₀ hz]

noncomputable def normalizedMixed (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := (normalizedAggregation a).comp (stack L)

theorem normalizedMixed_formula (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    normalizedMixed a L=(((Real.sqrt (Fintype.card ι))⁻¹:ℝ):ℂ) • mixed a L := by
  simp only [normalizedMixed,normalizedAggregation,smul_comp,aggregation_comp_stack]

theorem normalizedMixed_norm (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    ‖normalizedMixed a L‖≤‖stack L‖ := by
  exact (opNorm_comp_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (normalizedAggregation_norm a) (norm_nonneg (stack L)))

theorem normalizedMixed_polar_norm (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    ‖normalizedMixed a (polarRow L)‖≤1 := by
  apply (normalizedMixed_norm a (polarRow L)).trans
  change ‖stack (component (polar (stack L)))‖≤1
  rw [stack_component]
  exact polar_norm_le (stack L)

theorem normalizedMixed_output_polar (a : ι → G) (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) :
    outputSpace (normalizedMixed a L)=outputSpace (normalizedMixed a (polarRow L)) := by
  change outputSpace ((normalizedAggregation a).comp (stack L))=
    outputSpace ((normalizedAggregation a).comp (stack (component (polar (stack L)))))
  rw [stack_component]
  exact outputSpace_comp_polar (normalizedAggregation a) (stack L)

/-- The exact root energy of the mixed polar rows. Subgroup separation
removes every cross term; no finite support of columns is assumed. -/
theorem mixed_polar_root (S : Subgroup G) (a : ι → G)
    (ha : ∀ i j,i≠j → a j*(a i)⁻¹∉S)
    (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hL : ∀ i,Supported S (L i)) (h : G) :
    ‖mixed a (polarRow L) (delta h)‖^2=(matrix (stack L).kerᗮ.starProjection h h).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
  have he : ⟪mixed a (polarRow L) (delta h),mixed a (polarRow L) (delta h)⟫_ℂ=
      matrix (stack L).kerᗮ.starProjection h h := by
    simp only [mixed,sum_apply,comp_apply,sum_inner,inner_sum,translated_inner]
    rw [Finset.sum_comm]
    exact polar_mixing_root S L hL (fun i j => a j*(a i)⁻¹) (fun i => mul_inv_cancel _) ha h
  exact congrArg Complex.re he

theorem normalizedMixed_polar_root (S : Subgroup G) (a : ι → G)
    (ha : ∀ i j,i≠j → a j*(a i)⁻¹∉S)
    (L : ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (hL : ∀ i,Supported S (L i)) (h : G) :
    ‖normalizedMixed a (polarRow L) (delta h)‖^2=
      (Fintype.card ι:ℝ)⁻¹*(matrix (stack L).kerᗮ.starProjection h h).re := by
  rw [normalizedMixed_formula,smul_apply,norm_smul,mul_pow,mixed_polar_root S a ha L hL h]
  congr 1
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

#print axioms translation_norm
#print axioms translation_adjoint
#print axioms translated_inner
#print axioms aggregation_comp_stack
#print axioms aggregation_norm
#print axioms normalizedAggregation_norm
#print axioms normalizedMixed_formula
#print axioms normalizedMixed_norm
#print axioms normalizedMixed_polar_norm
#print axioms normalizedMixed_output_polar
#print axioms mixed_polar_root
#print axioms normalizedMixed_polar_root

end AsymptoticMixing
