module

public import QuantitativeMaassCylinderCoordinatesV1
public import QuantitativeMaassCylinderEulerZeroModeV1
public import AsymptoticCylinderTerminalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticMassTransport
open scoped Topology

namespace QuantitativeMaass

def terminalHeightMask (ε y : ℝ) : ℂ := if ε≤y then 1 else 0

theorem terminalHeightMask_measurable (ε : ℝ) : Measurable (terminalHeightMask ε) := by
  unfold terminalHeightMask
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem terminalHeightMask_bound (ε y : ℝ) : ‖terminalHeightMask ε y‖≤1 := by
  unfold terminalHeightMask
  split_ifs <;> norm_num

theorem terminalHeightMask_real (ε y : ℝ) : star (terminalHeightMask ε y)=terminalHeightMask ε y := by
  unfold terminalHeightMask
  split_ifs <;> simp

/-- The two actual cylinder coordinate systems intertwine terminal height
restriction, including the measurable boundary convention. -/
theorem productCylinder_terminal_intertwining (ε : ℝ) (f : AsymptoticCylinder.Space) :
    productCylinderToTranslation (AsymptoticCylinderTerminal.projection ε f)=
      cylinderHeightMultiplier (terminalHeightMask ε) (terminalHeightMask_measurable ε) 1
        (terminalHeightMask_bound ε) (productCylinderToTranslation f) := by
  apply cylinderZeroExtension.injective
  rw [productCylinderToTranslation_lift,AsymptoticCylinderTerminal.lift_projection,
    ←productCylinderToTranslation_lift]
  let g := productCylinderToTranslation f
  have hm := AsymptoticL2Multiplier.operator_coeFn
    (fun z : ℍ => terminalHeightMask ε z.im)
    ((terminalHeightMask_measurable ε).comp continuous_im.measurable).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℍ => terminalHeightMask_bound ε z.im)) g
  apply Lp.ext
  filter_upwards [AsymptoticRegionL2.projection_coeFn volume
    (AsymptoticCertificateOperators.highStrip ε) (AsymptoticCertificateOperators.highStrip_measurable ε)
    (cylinderZeroExtension g),cylinderZeroExtension_coeFn g,
    cylinderZeroExtension_coeFn_of_ae _ _ hm] with z h1 h2 h3
  change AsymptoticCylinderTerminal.hyperProjection ε (cylinderZeroExtension g) z=_ at h1 ⊢
  change _=(AsymptoticCertificateOperators.highStrip ε).indicator (cylinderZeroExtension g) z at h1
  change cylinderZeroExtension
    (cylinderHeightMultiplier (terminalHeightMask ε) (terminalHeightMask_measurable ε) 1
      (terminalHeightMask_bound ε) (productCylinderToTranslation f)) z=
    strip.indicator (fun x => terminalHeightMask ε x.im*g x) z at h3
  rw [h1,h3]
  classical
  by_cases hz : z∈strip
  · by_cases hy : ε≤z.im
    · have hh : z∈AsymptoticCertificateOperators.highStrip ε := ⟨hz,hy⟩
      simp only [Set.indicator_of_mem hh,Set.indicator_of_mem hz,h2,terminalHeightMask,
        ite_eq_left hy,one_mul]
    · have hh : z∉AsymptoticCertificateOperators.highStrip ε := fun h => hy h.2
      simp only [Set.indicator_of_notMem hh,Set.indicator_of_mem hz,terminalHeightMask,
        ite_eq_right hy,zero_mul]
  · have hh : z∉AsymptoticCertificateOperators.highStrip ε := fun h => hz h.1
    rw [Set.indicator_of_notMem hh,Set.indicator_of_notMem hz]

/-- Terminal data with no horizontal constant Fourier mode, before Gram
normalization of the reconstruction on this very subspace. -/
def terminalNonzeroModes (ε : ℝ) : Submodule ℂ AsymptoticCylinder.Space :=
  AsymptoticCylinderTerminal.Space ε ⊓
    cylinderNonzeroModes.comap productCylinderToTranslation.toLinearMap

theorem terminalNonzeroModes_closed (ε : ℝ) :
    IsClosed (terminalNonzeroModes ε : Set AsymptoticCylinder.Space) := by
  apply IsClosed.inter
  · exact (AsymptoticCylinderTerminal.projection ε-ContinuousLinearMap.id ℂ _).isClosed_ker
  · exact cylinderNonzeroModes_closed.preimage productCylinderToTranslation.continuous

instance (ε : ℝ) : CompleteSpace (terminalNonzeroModes ε) :=
  (terminalNonzeroModes_closed ε).completeSpace_coe

/-- Isometric inclusion into the full terminal space, retaining both the
height support and zero-mode conditions. -/
def terminalNonzeroInclusion (ε : ℝ) :
    terminalNonzeroModes ε →ₗᵢ[ℂ] AsymptoticCylinderTerminal.Space ε where
  toFun g := ⟨g.val,g.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

theorem terminalRestriction_nonzero (ε : ℝ) (f : AsymptoticCylinder.Space)
    (hf : productCylinderToTranslation f∈cylinderNonzeroModes) :
    AsymptoticCylinderTerminal.projection ε f∈terminalNonzeroModes ε := by
  refine ⟨(AsymptoticRegionL2.restrict AsymptoticCylinder.measure
    (AsymptoticCylinderTerminal.region ε) (AsymptoticCylinderTerminal.region_measurable ε) f).property,?_⟩
  change productCylinderToTranslation (AsymptoticCylinderTerminal.projection ε f)∈cylinderNonzeroModes
  rw [productCylinder_terminal_intertwining]
  exact cylinderNonzeroModes_multiplier _ (terminalHeightMask_measurable ε) 1
    (terminalHeightMask_bound ε) (terminalHeightMask_real ε) hf

/-- The raw terminal restriction of every original Euler solution lies in
the concrete nonzero-mode terminal Hilbert space. -/
theorem original_terminal_nonzero {N Q : ℕ} {hQ : 0<Q}
    (hN : 0<N) (A : FinitenessCertificate.Certificate N Q hQ)
    (P : FinitenessGlobalHeight.Parameters A) (r : ℝ) (σ : ℕ) {b : ℕ → ℂ}
    (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)
    (f : AsymptoticCylinder.Space)
    (hf : AsymptoticCylinderLift.lift f=principalEulerWeightedLp hN A P r σ hb) :
    AsymptoticCylinderTerminal.projection P.ε f∈terminalNonzeroModes P.ε := by
  apply terminalRestriction_nonzero
  have he : productCylinderToTranslation f=principalEulerCylinderLp hN A P r σ hb := by
    apply cylinderZeroExtension.injective
    rw [productCylinderToTranslation_lift,principalEulerCylinderLp_physical,hf]
  rw [he]
  exact principalEulerCylinder_nonzero_modes hN A P r σ hb

#print axioms productCylinder_terminal_intertwining
#print axioms terminalNonzeroModes_closed
#print axioms terminalRestriction_nonzero
#print axioms original_terminal_nonzero

end QuantitativeMaass
