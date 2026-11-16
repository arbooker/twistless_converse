module

public import QuantitativeNinaMaassOldTraceV1
public import QuantitativeNinaMaassOldSpectrumV1
public import QuantitativeNinaMaassEigenRepresentativesV1
public import QuantitativeNinaMaassSmallPeriodsV1
public import AsymptoticClassicalOldIntersectionSimpleGroupV1
public import AsymptoticClassicalOldIntersectionRepeatedV1
public import AsymptoticCoprimeCongruenceIndexV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeMaass
open AsymptoticClassicalCusp AsymptoticCongruenceLabels AsymptoticFreshMatrices
open scoped Topology BigOperators MatrixGroups

/-!
Actual descent of continuous representatives along finite level covers.
The adjoint trace followed by pullback is the covering degree on the old
range. Thus a continuous high-level representative in that range descends
to a continuous, pointwise lower-level representative. No regularity of an
arbitrary preimage vector is assumed.

The simply ramified intersection is treated on actual cuspidal spectral
bands using generated-group symmetries and literal cusp constants. Finite
trace preserves the cusp space by its explicit integral-coset formula.
Repeated-prime overlaps and the full multiplicity formula remain separate
obligations.
-/

namespace QuantitativeNinaMaass

theorem rational_action_continuous (g : AsymptoticRationalGroup.Group) :
    Continuous (fun z : ℍ => g • z) :=
  AsymptoticRationalBranches.action_continuous g

theorem integralLabel_matrix_action (A : SL(2,ℤ)) (z : ℍ) :
    integralLabel A • z = SpecialLinearGroup.mapGL ℝ A • z := by
  have hm : (A : GL (Fin 2) ℝ) = SpecialLinearGroup.mapGL ℝ A := by
    apply Units.ext
    ext i j
    rfl
  exact (integralLabel_action A z).trans
    ((ModularGroup.sl_moeb A z).trans (congrArg (fun a : GL (Fin 2) ℝ => a • z) hm))

def levelTraceRepresentative {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    AutomorphicL2.representatives (gamma M) (quotientMeasure M) := by
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  exact AutomorphicL2.traceRepresentative volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N) f

theorem levelTraceRepresentative_embedding {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    levelTrace hMN (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (levelTraceRepresentative hMN f) :=
  levelTrace_apply hMN f

theorem levelTraceRepresentative_apply {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) (x : ℍ) :
    (levelTraceRepresentative hMN f).val x =
      (let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
       ∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M), f.val (q.out.val⁻¹ • x)) := by
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  exact AutomorphicL2.traceRepresentative_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N) f x

theorem levelTraceRepresentative_continuous {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) : Continuous (levelTraceRepresentative hMN f).val := by
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  have he : (levelTraceRepresentative hMN f).val =
      fun x => ∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M), f.val (q.out.val⁻¹ • x) :=
    funext (levelTraceRepresentative_apply hMN f)
  rw [he]
  exact continuous_finsetSum _ (fun q _ => hf.comp (rational_action_continuous q.out.val⁻¹))

/-- The genuine trace of a pulled-back function is exactly its covering
degree times the original function, first on representatives. -/
theorem levelTraceRepresentative_cover {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M)) :
    levelTraceRepresentative hMN (levelCoverRepresentative hMN f) =
      (Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M)) : ℂ) • f := by
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  apply Subtype.ext
  funext x
  rw [levelTraceRepresentative_apply]
  simp only [levelCoverRepresentative_coe]
  change (∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M), f.val (q.out.val⁻¹ • x)) =
    (Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M)) : ℂ) * f.val x
  have hi (q : gamma M ⧸ (gamma N).subgroupOf (gamma M)) :
      f.val (q.out.val⁻¹ • x) = f.val x := f.property.2.1 q.out⁻¹ x
  simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- The trace-pullback identity on the completed physical Hilbert spaces. -/
theorem levelTrace_cover {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (v : AutomorphicSpace M) :
    levelTrace hMN (levelCover hMN v) =
      (Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M)) : ℂ) • v := by
  have he : (fun x : AutomorphicSpace M => levelTrace hMN (levelCover hMN x)) =
      fun x => (Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M)) : ℂ) • x := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma M) (quotientMeasure M)).equalizer
      ((levelTrace hMN).continuous.comp (levelCover hMN).continuous)
      (continuous_id.const_smul
        (Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M)) : ℂ))
    funext f
    simp only [Function.comp_apply, levelCover_apply, levelTrace_apply]
    change AutomorphicL2.denseEmbedding _ _
      (levelTraceRepresentative hMN (levelCoverRepresentative hMN f)) = _
    rw [levelTraceRepresentative_cover, map_smul]
    rfl
  exact congrFun he v

/-- A high-level representative with the actual lower-level invariance
descends by normalized finite trace. Lower-level square integrability is a
consequence of that trace construction, not an extra assumption. -/
theorem lower_representative_of_invariant {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hi : ∀ g : gamma M, ∀ z : ℍ, f.val (g.val • z) = f.val z) :
    ∃ g : AutomorphicL2.representatives (gamma M) (quotientMeasure M), g.val = f.val := by
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  let d : ℂ := Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Nat.card_pos (α := gamma M ⧸ (gamma N).subgroupOf (gamma M))).ne'
  refine ⟨d⁻¹ • levelTraceRepresentative hMN f, ?_⟩
  funext z
  change d⁻¹ * (levelTraceRepresentative hMN f).val z = f.val z
  rw [levelTraceRepresentative_apply]
  have he (q : gamma M ⧸ (gamma N).subgroupOf (gamma M)) :
      f.val (q.out.val⁻¹ • z) = f.val z := hi q.out⁻¹ z
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  change d⁻¹ * (d * f.val z) = f.val z
  rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]

theorem mem_levelCover_range_of_invariant {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hi : ∀ g : gamma M, ∀ z : ℍ, f.val (g.val • z) = f.val z) :
    AutomorphicL2.denseEmbedding _ _ f ∈ (levelCover hMN).range := by
  obtain ⟨g, hg⟩ := lower_representative_of_invariant hMN f hi
  refine ⟨AutomorphicL2.denseEmbedding _ _ g, ?_⟩
  change levelCover hMN (AutomorphicL2.denseEmbedding _ _ g) =
    AutomorphicL2.denseEmbedding _ _ f
  rw [levelCover_apply]
  apply congrArg (AutomorphicL2.denseEmbedding _ _)
  exact Subtype.ext ((levelCoverRepresentative_coe hMN g).trans hg)

/-- Every summand in the genuine finite trace has vanishing constant term
over the high-level period. The trace's lower-level invariance then changes
that period to M without changing its average. -/
theorem levelTraceRepresentative_constant_zero {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hzero : ∀ s : SL(2,ℤ), ∀ y : ℝ, 0 < y → cuspConstant N s f.val y = 0)
    (s : SL(2,ℤ)) (y : ℝ) (hy : 0 < y) :
    cuspConstant M s (levelTraceRepresentative hMN f).val y = 0 := by
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  have ht := levelTraceRepresentative_continuous hMN f hf
  rw [← cuspConstant_level hN hMN s _ ht (levelTraceRepresentative hMN f).property.2.1]
  have hbranch (q : gamma M ⧸ (gamma N).subgroupOf (gamma M)) :
      cuspConstant N s (fun z => f.val (q.out.val⁻¹ • z)) y = 0 := by
    obtain ⟨A, _hA, hA⟩ := q.out.property
    have he : cuspProfile N s (fun z => f.val (q.out.val⁻¹ • z)) =
        cuspProfile N (A⁻¹ * s) f.val := by
      funext x y
      by_cases hy : 0 < y
      · simp only [cuspProfile, dite_eq_left hy]
        rw [← hA, ← map_inv, integralLabel_action]
        change f.val (SpecialLinearGroup.mapGL ℝ A⁻¹ •
          (SpecialLinearGroup.mapGL ℝ s • _)) = _
        rw [map_mul, mul_smul]
      · simp only [cuspProfile, dite_eq_right hy]
    unfold cuspConstant
    rw [he]
    exact hzero (A⁻¹ * s) y hy
  have hs : cuspConstant N s (levelTraceRepresentative hMN f).val y =
      ∑ q : gamma M ⧸ (gamma N).subgroupOf (gamma M),
        cuspConstant N s (fun z => f.val (q.out.val⁻¹ • z)) y := by
    unfold cuspConstant zeroFourier
    simp only [cuspProfile, dite_eq_left hy, levelTraceRepresentative_apply]
    apply intervalIntegral.integral_finsetSum
    intro q _
    have hc := cuspProfile_continuous N s (fun z => f.val (q.out.val⁻¹ • z))
      (hf.comp (rational_action_continuous q.out.val⁻¹)) y
    simpa only [cuspProfile, dite_eq_left hy] using hc.intervalIntegrable 0 1
  rw [hs]
  exact Finset.sum_eq_zero (fun q _ => hbranch q)

/-- The physical finite-coset trace preserves the entire closed cusp space,
with no hypothesis on a chosen spectral decomposition. -/
theorem levelTrace_mem_cuspidal {M N : ℕ} [NeZero N]
    (hM : 0 < M) (hN : 0 < N) (hMN : M ∣ N)
    (v : AutomorphicSpace N) (hv : v ∈ localCuspidalSpace N hN) :
    levelTrace hMN v ∈ localCuspidalSpace M hM := by
  apply cuspidal_operator_mem_of_continuous N M hN hM (levelTrace hMN) _ v hv
  intro f hf hcusp
  rw [levelTrace_apply]
  change AutomorphicL2.denseEmbedding _ _ (levelTraceRepresentative hMN f) ∈ _
  apply continuous_representative_mem_cuspidal M hM _
    (levelTraceRepresentative_continuous hMN f hf)
  apply levelTraceRepresentative_constant_zero hN hMN f hf
  intro s y hy
  exact localCuspidalSpace_continuous_constant_zero N hN _ hcusp f.val hf
    f.property.2.1 f.property.2.2.coeFn_toLp s y hy

/-- Cuspidality of a pulled-back vector is equivalent to cuspidality of
its preimage. The reverse implication follows from the actual finite trace
and its nonzero covering degree. -/
theorem levelCover_mem_cuspidal_iff {M N : ℕ} [NeZero N]
    (hM : 0 < M) (hN : 0 < N) (hMN : M ∣ N) (v : AutomorphicSpace M) :
    levelCover hMN v ∈ localCuspidalSpace N hN ↔ v ∈ localCuspidalSpace M hM := by
  constructor
  · intro hv
    have ht := levelTrace_mem_cuspidal hM hN hMN (levelCover hMN v) hv
    rw [levelTrace_cover] at ht
    let d : ℂ := Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M))
    have hd : d ≠ 0 := by
      dsimp [d]
      exact_mod_cast (Nat.card_pos (α := gamma M ⧸ (gamma N).subgroupOf (gamma M))).ne'
    change d • v ∈ localCuspidalSpace M hM at ht
    have hh := (localCuspidalSpace M hM).smul_mem d⁻¹ ht
    simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using hh
  · exact levelCover_mem_cuspidal hM hN hMN v

/-- A continuous representative in the actual old range descends as a
literal function. The preimage is constructed by normalized finite trace. -/
theorem continuous_descent_of_mem_cover_range {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hold : AutomorphicL2.denseEmbedding _ _ f ∈ (levelCover hMN).range) :
    ∃ g : AutomorphicL2.representatives (gamma M) (quotientMeasure M),
      Continuous g.val ∧ g.val = f.val := by
  let d : ℂ := Nat.card (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Nat.card_pos (α := gamma M ⧸ (gamma N).subgroupOf (gamma M))).ne'
  let g := d⁻¹ • levelTraceRepresentative hMN f
  have hg : Continuous g.val :=
    continuous_const.smul (levelTraceRepresentative_continuous hMN f hf)
  obtain ⟨v, hv⟩ := hold
  change levelCover hMN v = AutomorphicL2.denseEmbedding _ _ f at hv
  have ht : AutomorphicL2.denseEmbedding _ _ (levelTraceRepresentative hMN f) = d • v := by
    rw [← levelTraceRepresentative_embedding hMN f, ← hv, levelTrace_cover]
  have he : AutomorphicL2.denseEmbedding _ _ g = v := by
    rw [map_smul, ht, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have hl : AutomorphicL2.denseEmbedding _ _ (levelCoverRepresentative hMN g) =
      AutomorphicL2.denseEmbedding _ _ f := by
    rw [← levelCover_apply, he, hv]
  have heq := continuous_representative_unique N (levelCoverRepresentative hMN g) f
    (levelCoverRepresentative_continuous hMN g hg) hf hl
  refine ⟨g, hg, ?_⟩
  exact (levelCoverRepresentative_coe hMN g).symm.trans (congrArg Subtype.val heq)

/-- Pointwise symmetries of an actual function, without holomorphicity or a
slash-weight convention. -/
def pointwiseStabilizer (f : ℍ → ℂ) : Subgroup (GL (Fin 2) ℝ) where
  carrier := {a | ∀ z, f (a • z) = f z}
  one_mem' := by intro z; rw [one_smul]
  mul_mem' := by
    intro a b ha hb z
    rw [mul_smul, ha, hb]
  inv_mem' := by
    intro a ha z
    simpa only [smul_inv_smul] using (ha (a⁻¹ • z)).symm

theorem continuous_old_level_invariant {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hold : AutomorphicL2.denseEmbedding _ _ f ∈ (levelCover hMN).range) :
    level M ≤ pointwiseStabilizer f.val := by
  obtain ⟨g, _, he⟩ := continuous_descent_of_mem_cover_range hMN f hf hold
  rintro a ⟨A, hA, rfl⟩ z
  have hi := g.property.2.1 ⟨integralLabel A, ⟨A, hA, rfl⟩⟩ z
  rw [he] at hi
  simpa only [integralLabel_matrix_action] using hi

/-- Membership in the second completed old range gives invariance under
the honest Fricke-conjugated lower matrix group. -/
theorem continuous_fricke_old_invariant {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hold : AutomorphicL2.denseEmbedding _ _ f ∈
      ((frickeIsometry N hN).toContinuousLinearMap.comp (levelCover hMN)).range) :
    frickeOldLevel N M hN ≤ pointwiseStabilizer f.val := by
  have hfc : Continuous (frickeRepresentative N hN f).val :=
    hf.comp (rational_action_continuous (frickeLabel N hN))
  have hm : AutomorphicL2.denseEmbedding _ _ (frickeRepresentative N hN f) ∈
      (levelCover hMN).range := by
    obtain ⟨v, hv⟩ := hold
    refine ⟨v, ?_⟩
    rw [← frickeIsometry_apply, ← hv]
    exact (frickeIsometry_involutive N hN (levelCover hMN v)).symm
  have hi := continuous_old_level_invariant hMN (frickeRepresentative N hN f) hfc hm
  rintro a ⟨b, hb, rfl⟩ z
  have h := hi hb ((frickeReal N hN)⁻¹ • z)
  change f.val (frickeLabel N hN • (b • ((frickeReal N hN)⁻¹ • z))) =
    f.val (frickeLabel N hN • ((frickeReal N hN)⁻¹ • z)) at h
  rw [frickeLabel_action_real, frickeLabel_action_real, smul_inv_smul] at h
  change f.val ((frickeReal N hN * b * (frickeReal N hN)⁻¹) • z) = f.val z
  simpa only [mul_smul] using h

/-- On continuous physical representatives the completed cover range is
exactly the actual lower-level invariance condition. -/
theorem continuous_cover_range_iff {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    AutomorphicL2.denseEmbedding _ _ f ∈ (levelCover hMN).range ↔
      level M ≤ pointwiseStabilizer f.val := by
  constructor
  · exact continuous_old_level_invariant hMN f hf
  · intro hi
    apply mem_levelCover_range_of_invariant hMN f
    rintro ⟨g, A, hA, rfl⟩ z
    rw [integralLabel_matrix_action]
    exact hi ⟨A, hA, rfl⟩ z

/-- The analogous converse for the Fricke-conjugated actual old image. -/
theorem continuous_fricke_cover_range_iff {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    AutomorphicL2.denseEmbedding _ _ f ∈
      ((frickeIsometry N hN).toContinuousLinearMap.comp (levelCover hMN)).range ↔
      frickeOldLevel N M hN ≤ pointwiseStabilizer f.val := by
  constructor
  · exact continuous_fricke_old_invariant hN hMN f hf
  · intro hi
    have hg : AutomorphicL2.denseEmbedding _ _ (frickeRepresentative N hN f) ∈
        (levelCover hMN).range := by
      apply mem_levelCover_range_of_invariant hMN
      rintro ⟨g, A, hA, rfl⟩ z
      change f.val (frickeLabel N hN • (integralLabel A • z)) =
        f.val (frickeLabel N hN • z)
      rw [integralLabel_matrix_action, frickeLabel_action_real, frickeLabel_action_real]
      have hh : frickeReal N hN * SpecialLinearGroup.mapGL ℝ A * (frickeReal N hN)⁻¹ ∈
          frickeOldLevel N M hN := ⟨SpecialLinearGroup.mapGL ℝ A, ⟨A, hA, rfl⟩, rfl⟩
      have he := hi hh (frickeReal N hN • z)
      simpa only [mul_smul, inv_smul_smul] using he
    obtain ⟨v, hv⟩ := hg
    change levelCover hMN v =
      AutomorphicL2.denseEmbedding _ _ (frickeRepresentative N hN f) at hv
    refine ⟨v, ?_⟩
    change frickeIsometry N hN (levelCover hMN v) = _
    rw [hv, ← frickeIsometry_apply, frickeIsometry_involutive N hN _]

/-- The repeated-prime group-generation identity applies to actual Maass
old vectors. Its index hypothesis is a finite group condition, used for
the admissible powers of 2, rather than an assumed spectral overlap. -/
theorem continuous_repeated_old_invariant (L p : ℕ) [NeZero (p * (p * L))]
    (hL : 0 < L) (hp : p.Prime)
    (hr : ((level (p * L)).relIndex (level L)).Prime)
    (f : AutomorphicL2.representatives (gamma (p * (p * L)))
      (quotientMeasure (p * (p * L)))) (hf : Continuous f.val)
    (hold : AutomorphicL2.denseEmbedding _ _ f ∈
      (levelCover (Nat.dvd_mul_left (p * L) p)).range ⊓
      ((frickeIsometry (p * (p * L)) (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))).toContinuousLinearMap.comp
        (levelCover (Nat.dvd_mul_left (p * L) p))).range) :
    dilationLevel L p hp.pos ≤ pointwiseStabilizer f.val := by
  have hl := continuous_old_level_invariant (Nat.dvd_mul_left (p * L) p) f hf hold.1
  have hh := continuous_fricke_old_invariant (Nat.mul_pos hp.pos (Nat.mul_pos hp.pos hL))
    (Nat.dvd_mul_left (p * L) p) f hf hold.2
  rw [frickeOldLevel_eq_dilationLevel (p * L) p (Nat.mul_pos hp.pos hL) hp.pos] at hh
  rw [← repeated_old_join_eq L p hL hp hr]
  exact sup_le hl hh

/-- The intervening index needed for repeated 2-old intersections is
always prime: it is 2 at an even lower level and 3 at an odd one. Thus the
group-generation input adds no hypothesis at levels 4m or 8m. -/
theorem two_level_relIndex_prime (L : ℕ) (hL : 0 < L) :
    ((level (2 * L)).relIndex (level L)).Prime := by
  rw [level_relIndex]
  by_cases h2 : 2 ∣ L
  · rw [AsymptoticRamifiedCosets.projective_index L 2 hL (by decide) h2]
    exact Nat.prime_two
  · have hc : Nat.Coprime 2 L := Nat.prime_two.coprime_iff_not_dvd.mpr h2
    rw [AsymptoticRamifiedCosets.projective_index_coprime L 2 hL Nat.prime_two hc]
    norm_num

/-- Accumulating actual lower-unipotent symmetries kill a continuous vector
in the geometric cusp space. The S-cusp constant, rather than a holomorphic
identity theorem, eliminates the horizontal constant. -/
theorem continuous_cusp_zero_of_small_lower_symmetries (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hcusp : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) (hne : ∀ n, r n ≠ 0)
    (hsym : ∀ n z, f.val (lowerTranslation (r n) • z) = f.val z) : f.val = 0 := by
  let S := SpecialLinearGroup.mapGL ℝ ModularGroup.S
  let g : ℍ → ℂ := fun z => f.val (S • z)
  have hg : Continuous g := hf.comp (continuous_const_smul S)
  have htrans (a : ℝ) (z : ℍ) : AsymptoticMobiusFold.translation a • z = a +ᵥ z := by
    apply UpperHalfPlane.ext
    rw [AsymptoticMobiusFold.translation_action, UpperHalfPlane.coe_vadd, add_comm]
  have hp (n : ℕ) (z : ℍ) : g (-r n +ᵥ z) = g z := by
    change f.val (S • (-r n +ᵥ z)) = f.val (S • z)
    rw [← htrans, ← mul_smul]
    change f.val ((SpecialLinearGroup.mapGL ℝ ModularGroup.S *
      AsymptoticMobiusFold.translation (-r n)) • z) = _
    rw [S_translation_intertwine, mul_smul, hsym]
  have hconst (z : ℍ) (x : ℝ) : g (x +ᵥ z) = g z :=
    horocycle_constant_of_small_periods g hg (fun n => -r n)
      (by simpa only [neg_zero] using hr.neg) (fun n => neg_ne_zero.mpr (hne n)) hp z x
  have hbase (x y : ℝ) (hy : 0 < y) :
      horocyclePoint x y hy = x +ᵥ horocyclePoint 0 y hy := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [horocyclePoint, UpperHalfPlane.coe_vadd]
  have hz : g = 0 := by
    funext z
    change g z = 0
    let b := horocyclePoint 0 z.im z.im_pos
    have hc := localCuspidalSpace_continuous_constant_zero N hN
      (AutomorphicL2.denseEmbedding _ _ f) hcusp f.val hf f.property.2.1
      f.property.2.2.coeFn_toLp ModularGroup.S z.im z.im_pos
    have hpoint (x : ℝ) :
        f.val (SpecialLinearGroup.mapGL ℝ ModularGroup.S •
          horocyclePoint ((N : ℝ) * x) z.im z.im_pos) = g b := by
      change g (horocyclePoint ((N : ℝ) * x) z.im z.im_pos) = g b
      rw [hbase]
      exact hconst b _
    simp only [cuspConstant, zeroFourier, cuspProfile, dite_eq_left z.im_pos, hpoint,
      intervalIntegral.integral_const, sub_zero, one_smul] at hc
    have hzpoint : z = z.re +ᵥ b := by
      apply UpperHalfPlane.ext
      apply Complex.ext <;> simp [b, horocyclePoint, UpperHalfPlane.coe_vadd]
    rw [hzpoint, hconst]
    exact hc
  funext z
  have h := congrFun hz (S⁻¹ • z)
  change f.val (S • (S⁻¹ • z)) = 0 at h
  simpa only [smul_inv_smul, Pi.zero_apply] using h

/-- The pointwise conclusion for a continuous cuspidal representative in
both genuine old images. The following spectral corollaries construct that
representative rather than assuming its existence. -/
theorem continuous_simple_old_intersection_zero (M p : ℕ) [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (f : AutomorphicL2.representatives (gamma (p * M)) (quotientMeasure (p * M)))
    (hf : Continuous f.val)
    (hcusp : AutomorphicL2.denseEmbedding _ _ f ∈
      localCuspidalSpace (p * M) (Nat.mul_pos hp.pos hM))
    (hold : AutomorphicL2.denseEmbedding _ _ f ∈ (levelCover (Nat.dvd_mul_left M p)).range ⊓
      ((frickeIsometry (p * M) (Nat.mul_pos hp.pos hM)).toContinuousLinearMap.comp
        (levelCover (Nat.dvd_mul_left M p))).range) : AutomorphicL2.denseEmbedding _ _ f = 0 := by
  have hleft := continuous_old_level_invariant (Nat.dvd_mul_left M p) f hf hold.1
  have hright := continuous_fricke_old_invariant (Nat.mul_pos hp.pos hM)
    (Nat.dvd_mul_left M p) f hf hold.2
  rw [frickeOldLevel_eq_dilationLevel M p hM hp.pos] at hright
  have hjoin : level M ⊔ dilationLevel M p hp.pos ≤ pointwiseStabilizer f.val :=
    sup_le hleft hright
  let q : ℝ := 1 / (p : ℝ)^2
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hqpos : 0 < q := one_div_pos.mpr (sq_pos_of_pos (by linarith))
  have hqlt : q < 1 := by
    apply (div_lt_one (sq_pos_of_pos (by linarith : (0 : ℝ) < p))).mpr
    nlinarith
  have hzero : f.val = 0 := continuous_cusp_zero_of_small_lower_symmetries
    (p * M) (Nat.mul_pos hp.pos hM) f hf hcusp
    (fun n => (M : ℝ) * q^n)
    (by simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hqpos.le hqlt))
    (fun n => mul_ne_zero (by exact_mod_cast hM.ne') (pow_ne_zero n hqpos.ne'))
    (fun n => hjoin (small_lower_mem_join M p hp.pos hcp n))
  have hfzero : f = 0 := Subtype.ext hzero
  rw [hfzero, map_zero]

/-- At a simply ramified prime, the two genuine old images have zero
intersection on every actual cuspidal Friedrichs eigenspace. -/
theorem simple_old_eigen_intersection_zero (M p : ℕ) [NeZero (p * M)]
    (hM : 0 < M) (hp : p.Prime) (hcp : p.Coprime M)
    (v : AutomorphicSpace (p * M))
    (hcusp : v ∈ localCuspidalSpace (p * M) (Nat.mul_pos hp.pos hM))
    (e : ℝ) (he : 0 ≤ e) (hgraph : FriedrichsGraph (p * M) v ((e : ℂ) • v))
    (hold : v ∈ (levelCover (Nat.dvd_mul_left M p)).range ⊓
      ((frickeIsometry (p * M) (Nat.mul_pos hp.pos hM)).toContinuousLinearMap.comp
        (levelCover (Nat.dvd_mul_left M p))).range) : v = 0 := by
  obtain ⟨f, hf, hfv⟩ := exists_continuous_eigen_representative (p * M) v e he hgraph
  have hz := continuous_simple_old_intersection_zero M p hM hp hcp f hf
    (by rw [hfv]; exact hcusp) (by rw [hfv]; exact hold)
  rwa [hfv] at hz

#print axioms rational_action_continuous
#print axioms integralLabel_matrix_action
#print axioms levelTraceRepresentative_embedding
#print axioms levelTraceRepresentative_apply
#print axioms levelTraceRepresentative_continuous
#print axioms levelTraceRepresentative_cover
#print axioms levelTrace_cover
#print axioms lower_representative_of_invariant
#print axioms mem_levelCover_range_of_invariant
#print axioms levelTraceRepresentative_constant_zero
#print axioms levelTrace_mem_cuspidal
#print axioms levelCover_mem_cuspidal_iff
#print axioms continuous_descent_of_mem_cover_range
#print axioms continuous_old_level_invariant
#print axioms continuous_fricke_old_invariant
#print axioms continuous_cover_range_iff
#print axioms continuous_fricke_cover_range_iff
#print axioms continuous_repeated_old_invariant
#print axioms two_level_relIndex_prime
#print axioms continuous_cusp_zero_of_small_lower_symmetries
#print axioms continuous_simple_old_intersection_zero
#print axioms simple_old_eigen_intersection_zero

end QuantitativeNinaMaass
