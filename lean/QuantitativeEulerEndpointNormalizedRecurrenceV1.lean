module

public import QuantitativeEulerEndpointBlockRecurrenceV1
public import QuantitativeEulerEndpointNormalizedRowsV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNormalizedRecurrence
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointBlockGram
open QuantitativeEulerEndpointBlockUpdate QuantitativeEulerEndpointSoftUpdate MeasureTheory Polynomial
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (μ : Measure α) (hf : μ s<∞)
  (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hU : ∀ x, (U x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x)
  (q : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hq : IsStarProjection q)
  (V : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
  (hV : ∀ x, (V x).toSubmodule.starProjection = QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖≤C i)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "τ" => rootedTrace hact s hs p hp μ hf
local notation "hτ" => rootedTrace_mono hact s hs p hp μ hf
local notation "factor" => QuantitativeEulerEndpointBlockNormalization.factor C
local notation "NB" => QuantitativeEulerEndpointNormalizedRows.row hact s hs p B C
local notation "NC" => QuantitativeEulerEndpointNormalizedRows.bound C
local notation "hmNB" => QuantitativeEulerEndpointNormalizedRows.row_measurable hact s hs p B hmB C
local notation "hcNB" => QuantitativeEulerEndpointNormalizedRows.row_covariant hact s hs p B hcB C
local notation "hnNB" => QuantitativeEulerEndpointNormalizedRows.row_norm hact s hs p hp B C hC
local notation "hsNB" => QuantitativeEulerEndpointNormalizedRows.row_source hact s hs p hp B C
local notation "F" => fun n => gramSum hact s hs p hp (NB n) (hmNB n) (hcNB n) (NC n) (hnNB n) (hsNB n) n

local instance closedSubmodule_complete (W : ClosedSubmodule ℂ ℓ²(G,ℂ)) :
    CompleteSpace W.toSubmodule := W.isClosed.completeSpace_coe

include U hU V hV hq in
/-- One normalized polynomial update from arbitrary original rows. Its
hard-contraction input and exact solution equations use the original rows;
ambient right support and the sum-of-squares normalization are discharged. -/
theorem exists_normalized_block_update
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1)
    (hhalf : ∀ x, QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x=
      (highAt (ρ A x) (1/2)).starProjection)
    (n : ℕ)
    (c : ℝ) (hc : 0<c) {d K : ℝ}
    (hd : 0<d) (hK : 0<K) (hcut : 2*d^2<K)
    (hbound : (∑ i : Fin n, (NC n i)^2)+d^2≤K)
    (target rho : ℝ) (hrho0 : 0≤rho) (hrho1 : rho≤1)
    (htheta0 : 0≤Real.log (K/(factor n*c)^2)/Real.log (K/(2*d^2)))
    (htheta1 : Real.log (K/(factor n*c)^2)/Real.log (K/(2*d^2))≤1)
    (hchain : (trace μ (QuantitativeSpectralRegularPacket.projectionFamily V B c n)).toReal-target≤
      rho*(QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf q-target))
    (L : ℕ) {J : ℕ} (hJ : 0<J) :
    ∃ z : ℝ[X], z.natDegree≤16*J^5+1 ∧
      (∑ i∈z.support, |z.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
      0≤aeval (update A (A*F n*A) L) z ∧ aeval (update A (A*F n*A) L) z≤A ∧
      τ (aeval (update A (A*F n*A) L) z-(aeval (update A (A*F n*A) L) z)^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, A*E=E → (∀ i : Fin n, ∀ x, B i x*ρ E x=0) →
        aeval (update A (A*F n*A) L) z*E=E) ∧
      τ (aeval (update A (A*F n*A) L) z)-target≤
        (1-(1-Real.exp (-(L:ℝ)*(d^2/32)))*(1-rho)*
          (1-Real.log (K/(factor n*c)^2)/Real.log (K/(2*d^2))))*(τ A-target)+
        (4+2*(L:ℝ))*τ (A-A^2)+(μ s).toReal*(Real.log 2/Real.log (K/(2*d^2))) := by
  have hPU (x : α) : QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x*
      (V x).toSubmodule.starProjection=(V x).toSubmodule.starProjection := by
    have hAx : IsSelfAdjoint (ρ A x) :=
      (IsSelfAdjoint.of_nonneg hA0).map (QuantitativeEulerEndpointCornerCut.evaluation hact s hs p hp x)
    have hAP : (ρ A x).comp (U x).toSubmodule.starProjection=ρ A x := by
      rw [hU]
      exact congrArg (fun E : 𝔄 => ρ E x) (mul_one A)
    have hle := highAt_le_corner (ρ A x) hAx (U x).toSubmodule (by norm_num : (0:ℝ)≤1/2) hAP
    rw [hV,hhalf,← hU]
    exact ContinuousLinearMap.ext (fun v => (U x).toSubmodule.starProjection_eq_self_iff.mpr
      (hle ((highAt (ρ A x) (1/2)).starProjection_apply_mem v)))
  have hchain' : (trace μ (QuantitativeSpectralRegularPacket.projectionFamily V
      (rows hact s hs (NB n) q) (factor n*c) n)).toReal-target≤
      rho*(QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf q-target) := by
    rw [QuantitativeEulerEndpointBlockRestriction.restricted_projectionFamily hact s hs q V hV,
      QuantitativeEulerEndpointNormalizedRows.projectionFamily_eq hact s hs p B C V hPU]
    exact hchain
  obtain ⟨z,hdeg,hmass,hz0,hzA,hdef,hfixed,hrec⟩ :=
    QuantitativeEulerEndpointBlockRecurrence.exists_contracting_block_update
      hact s hs p hp μ hf U hU q hq V hV (NB n) (hmNB n) (hcNB n) (NC n) (hnNB n) (hsNB n)
      hmp A hA0 hA1 hhalf n (QuantitativeEulerEndpointNormalizedRows.bound_square_sum C n)
      (factor n*c) (mul_pos (QuantitativeEulerEndpointBlockNormalization.factor_pos C n) hc)
      hd hK hcut hbound target rho hrho0 hrho1 htheta0 htheta1 hchain' L hJ
  refine ⟨z,hdeg,hmass,hz0,hzA,hdef,?_,hrec⟩
  intro E hAE hBE
  apply hfixed E hAE
  intro i x
  apply QuantitativeEulerEndpointNormalizedRows.row_kills hact s hs p B C n i (ρ E)
  · intro y
    exact congrArg (fun D : 𝔄 => ρ D y) (one_mul E)
  · exact hBE i

#print axioms exists_normalized_block_update
end QuantitativeEulerEndpointNormalizedRecurrence
