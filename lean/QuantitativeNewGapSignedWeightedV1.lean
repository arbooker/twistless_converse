module

public import QuantitativeNewGapIndexedV1
public import QuantitativeNewGapFrickeSignGapV1
public import QuantitativeSpectralExceptionalFrickeOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticSubspaceIntersection
open AsymptoticPolarIsometry QuantitativeArithmeticCrossPrime UpperHalfPlane
open QuantitativeSpectralExceptionalFricke
open scoped lp

def signedNewSpace (N : ℕ) (hN : 0<N) (s : ℝ) :
    Submodule ℂ ℓ²(Classes (gamma N),ℂ) :=
  inter (AsymptoticTotalNewCorner.space N hN) (permutationSignSpace (globalFrickeEquiv N hN) s)

instance signedNewSpace_complete (N : ℕ) (hN : 0<N) (s : ℝ) :
    CompleteSpace (signedNewSpace N hN s) := inferInstanceAs
      (CompleteSpace (inter (AsymptoticTotalNewCorner.space N hN)
        (permutationSignSpace (globalFrickeEquiv N hN) s)))

def signedNewInduction (N : ℕ) (hN : 0<N) (s : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    signedNewSpace N hN s →ₗᵢ[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (AsymptoticCongruenceQuotient.induction N hε ht z).comp (signedNewSpace N hN s).subtypeₗᵢ

def signedNewStripSpace (N : ℕ) (hN : 0<N) (s : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  (signedNewInduction N hN s hε ht z).toLinearMap.range

instance signedNewStripSpace_complete (N : ℕ) (hN : 0<N) (s : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    CompleteSpace (signedNewStripSpace N hN s hε ht z) :=
  AsymptoticIsometryRange.range_complete _

theorem signedNewStripSpace_projection (N : ℕ) (hN : 0<N) (s : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    (signedNewStripSpace N hN s hε ht z).starProjection=
      AsymptoticCongruenceQuotient.compression N hε ht (signedNewSpace N hN s).starProjection z := by
  have hh := AsymptoticIsometryRange.cogram_comp
    (AsymptoticCongruenceQuotient.induction N hε ht z) (signedNewSpace N hN s).subtypeₗᵢ
  have hr : (signedNewSpace N hN s).subtypeₗᵢ.toLinearMap.range=signedNewSpace N hN s :=
    Submodule.range_subtype _
  rw [starProjection_congr _ _ hr] at hh
  exact hh

theorem signedNew_induction (N : ℕ) (hN : 0<N) (s : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    (signedNewStripSpace N hN s hε ht z).starProjection
      (AsymptoticCongruenceQuotient.induction N hε ht z f)=
      AsymptoticCongruenceQuotient.induction N hε ht z ((signedNewSpace N hN s).starProjection f) := by
  rw [signedNewStripSpace_projection]
  exact QuantitativeEulerOldProjectionBlock.compressed_apply_isometry _ _ f

/-- The new signed range is exactly the literal total-new weighted
space intersected with the kernel of the actual weighted Fricke row. -/
theorem signedNewStripSpace_mem (N : ℕ) (hN : 0<N) (s : ℝ)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    v∈signedNewStripSpace N hN s hε ht z ↔
      v∈AsymptoticTotalNewCorner.stripSpace N hN hε ht z ∧ weightedRow N hN s hε ht z v=0 := by
  constructor
  · rintro ⟨f,rfl⟩
    have hf := (inter_mem _ _ f.val).mp f.property
    constructor
    · exact ⟨⟨f.val,hf.1⟩,rfl⟩
    · change weightedRow N hN s hε ht z (AsymptoticCongruenceQuotient.induction N hε ht z f.val)=0
      rw [weightedRow_induction]
      have hz : countingRow N hN s f.val=0 := hf.2
      rw [hz,map_zero]
  · rintro ⟨⟨f,rfl⟩,hf⟩
    have hzero : countingRow N hN s f.val=0 := by
      change weightedRow N hN s hε ht z (AsymptoticCongruenceQuotient.induction N hε ht z f.val)=0 at hf
      rw [weightedRow_induction] at hf
      apply (AsymptoticCongruenceQuotient.induction N hε ht z).injective
      simpa only [map_zero] using hf
    exact ⟨⟨f.val,(inter_mem _ _ _).mpr ⟨f.property,hzero⟩⟩,rfl⟩

theorem signedNew_old_energy_gap (N : ℕ) (hN : 0<N) :
    ∃ γ : ℝ,0<γ ∧ ∀ (s : ℝ),s^2=1 → ∀ f : ℓ²(Classes (gamma N),ℂ),
      γ*‖f-(signedNewSpace N hN s).starProjection f‖^2≤
        (N.primeFactors.toList.map fun p => localOldEnergy N hN p f).sum+
        ‖countingRow N hN s f‖^2 := by
  obtain ⟨a,ha,hgap⟩ := totalNew_old_energy_gap N hN
  refine ⟨min a 4,lt_min ha (by norm_num),?_⟩
  intro s hs f
  have hd := inter_projection_distance _ _ (globalFricke_totalNew_sign_commute N hN s) f
  have hfirst := (mul_le_mul_of_nonneg_right (min_le_left a 4)
    (sq_nonneg ‖f-(AsymptoticTotalNewCorner.space N hN).starProjection f‖)).trans (hgap f)
  have hsecond : min a 4*‖f-(permutationSignSpace (globalFrickeEquiv N hN) s).starProjection f‖^2≤
      ‖countingRow N hN s f‖^2 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right a 4)
      (sq_nonneg ‖f-(permutationSignSpace (globalFrickeEquiv N hN) s).starProjection f‖)
    rw [permutationSignSpace_gap _ (globalFrickeEquiv_involutive N hN) s hs] at hh
    exact hh
  exact (mul_le_mul_of_nonneg_left hd (le_min ha.le (by norm_num))).trans
    (by rw [mul_add]; exact add_le_add hfirst hsecond)

/-- The actual total-new and global-sign weighted target has a positive
gap controlled by the canonical old-family energies and the same
weighted Fricke row used by the concrete residual recombiner. -/
theorem signedNew_indexed_weighted_gap (N : ℕ) (hN : 0<N) :
    ∃ γ : ℝ,0<γ ∧ ∀ (s : ℝ),s^2=1 → ∀ {ε : ℝ} (hε : 0<ε)
      {t : ℕ} (ht : 1≤t) (z : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),
      v∈AsymptoticCongruenceQuotient.quotientSpace N hε ht z →
      γ*‖v-(signedNewStripSpace N hN s hε ht z).starProjection v‖^2≤
        (∑ i : PrimeOldIndex N,
          ‖(AsymptoticCongruenceOldSpace.space N (oldGroup N hN i.1.val i.2)
            (primeOld_le N hN i) hε ht z).starProjection v‖^2)+
        ‖weightedRow N hN s hε ht z v‖^2 := by
  obtain ⟨γ,hγ,hgap⟩ := signedNew_old_energy_gap N hN
  refine ⟨γ,hγ,?_⟩
  intro s hs ε hε t ht z v hv
  rw [indexed_old_energy_eq]
  obtain ⟨f,rfl⟩ := hv
  simp only [LinearIsometry.coe_toLinearMap,signedNew_induction,weightedRow_induction,
    ← map_sub,LinearIsometry.norm_map,weightedLocalOldEnergy_induction]
  exact hgap s hs f

#print axioms signedNewStripSpace_projection
#print axioms signedNewStripSpace_mem
#print axioms signedNew_indexed_weighted_gap

end QuantitativeNewGap
