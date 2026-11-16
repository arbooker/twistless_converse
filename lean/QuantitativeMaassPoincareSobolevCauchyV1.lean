module

public import QuantitativeMaassSobolevCauchyV1
public import QuantitativeMaassLocalizationModuleV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Filter UpperHalfPlane UniformSpace
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Strong coordinate approximation with fixed support gives a Cauchy sequence
in the actual completed quotient energy space. -/
theorem smooth_energy_approximation_cauchy (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    {Lf Lu : NNReal} {f : Point → ℂ} (hf : LipschitzWith Lf f) (hc : HasCompactSupport f)
    (u : ℕ → SmoothUpperSeed)
    (hs : ∀ n,tsupport (upperFunction (u n).toFun)⊆K)
    (hu : ∀ n,ContDiff ℝ ∞ (u n).toFun ∧ HasCompactSupport (u n).toFun ∧
      tsupport (u n).toFun⊆{Z : Point | 0<Z.2} ∧ LipschitzWith Lu (u n).toFun)
    (hm : Tendsto (fun n => ∫ Z,‖(u n).toFun Z-f Z‖^2) atTop (𝓝 0))
    (hd : Tendsto (fun n => ∫ Z,‖fderiv ℝ (u n).toFun Z-fderiv ℝ f Z‖^2) atTop (𝓝 0)) :
    CauchySeq (fun n => smoothEnergyMap N (seedModule (u n))) := by
  obtain ⟨C,hC,hbound⟩ := compact_poincare_coordinate_energy_bound N K hK
  let e : ℕ → ℝ := fun n => 2*C*((∫ Z,‖(u n).toFun Z-f Z‖^2)+
    (∫ Z,‖fderiv ℝ (u n).toFun Z-fderiv ℝ f Z‖^2))
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (hm.add hd).const_mul (2*C)
  apply cauchySeq_of_norm_sub_square_le he
  intro m n
  let w := moduleSeed (seedModule (u m)-seedModule (u n))
  have hw : w.toFun=(fun Z => (u m).toFun Z-(u n).toFun Z) := rfl
  have hwc : ContDiff ℝ ∞ w.toFun := (hu m).1.sub (hu n).1
  have hwk : HasCompactSupport w.toFun := (hu m).2.1.sub (hu n).2.1
  have hwp : tsupport w.toFun⊆{Z : Point | 0<Z.2} :=
    (tsupport_sub (u m).toFun (u n).toFun).trans (union_subset (hu m).2.2.1 (hu n).2.2.1)
  have hws : tsupport (upperFunction w.toFun)⊆K :=
    (tsupport_sub (upperFunction (u m).toFun) (upperFunction (u n).toFun)).trans
      (union_subset (hs m) (hs n))
  have hwD : fderiv ℝ w.toFun=(fun Z =>
      fderiv ℝ (u m).toFun Z-fderiv ℝ (u n).toFun Z) := by
    funext Z
    exact fderiv_sub ((hu m).1.differentiable (by simp) Z)
      ((hu n).1.differentiable (by simp) Z)
  have hE : smoothEnergyMap N (seedModule (u m))-smoothEnergyMap N (seedModule (u n))=
      (poincareEnergySeed N w : QuotientEnergySpace N) := (map_sub (smoothEnergyMap N) _ _).symm
  rw [hE,Completion.norm_coe]
  have hM := integral_sub_square_le
    ((hu m).1.continuous.memLp_of_hasCompactSupport (hu m).2.1 : MemLp (u m).toFun 2 volume)
    ((hu n).1.continuous.memLp_of_hasCompactSupport (hu n).2.1)
    (hf.continuous.memLp_of_hasCompactSupport hc)
  have hD := integral_sub_square_le (lipschitz_fderiv_memLp (hu m).2.2.2 (hu m).2.1)
    (lipschitz_fderiv_memLp (hu n).2.2.2 (hu n).2.1) (lipschitz_fderiv_memLp hf hc)
  have hh := hbound w hwc hwk hwp hws
  rw [hwD,hw] at hh
  apply hh.trans
  calc
    _ ≤ C*((2*(∫ Z,‖(u m).toFun Z-f Z‖^2)+2*(∫ Z,‖(u n).toFun Z-f Z‖^2))+
      (2*(∫ Z,‖fderiv ℝ (u m).toFun Z-fderiv ℝ f Z‖^2)+
        2*(∫ Z,‖fderiv ℝ (u n).toFun Z-fderiv ℝ f Z‖^2))) :=
      mul_le_mul_of_nonneg_left (add_le_add hM hD) hC.le
    _ = e m+e n := by dsimp [e]; ring

/-- The literal weighted seed admits joint coordinate and quotient-energy
limits, constructed from the same smooth compact sequence. -/
theorem quotientWeight_seed_energy_limit (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (w : SmoothUpperSeed) :
    let f : Point → ℂ := fun Z => (quotientWeightPlane N ε v Z:ℂ)*
      upperSeedExtension (upperFunction w.toFun) Z
    ∃ (u : ℕ → SmoothUpperSeed) (U : QuotientEnergySpace N),
      Tendsto (fun n => smoothEnergyMap N (seedModule (u n))) atTop (𝓝 U) ∧
      Tendsto (fun n => ∫ Z,‖(u n).toFun Z-f Z‖^2) atTop (𝓝 0) ∧
      (∀ᵐ Z ∂(volume : Measure Point),
        Tendsto (fun n => fderiv ℝ (u n).toFun Z) atTop (𝓝 (fderiv ℝ f Z))) ∧
      ∃ K : Set ℍ,IsCompact K ∧ ∀ n,tsupport (upperFunction (u n).toFun)⊆K := by
  dsimp only
  let f : Point → ℂ := fun Z => (quotientWeightPlane N ε v Z:ℂ)*
    upperSeedExtension (upperFunction w.toFun) Z
  obtain ⟨L,K,u,hK,hs,hu,hm,hd,ha⟩ := quotientWeight_seed_sobolev_approx N hε hv w
  obtain ⟨Lf,hf⟩ := quotientWeight_seed_lipschitz N hε hv w
  have hc : HasCompactSupport f := (upperSeedExtension_compact _ w.compact).mono
    (Function.support_mul_subset_right _ _)
  have hC := smooth_energy_approximation_cauchy N K hK hf hc u hs hu hm hd
  obtain ⟨U,hU⟩ := cauchySeq_tendsto_of_complete hC
  exact ⟨u,U,hU,hm,ha,K,hK,hs⟩

#print axioms smooth_energy_approximation_cauchy
#print axioms quotientWeight_seed_energy_limit

end QuantitativeMaass
