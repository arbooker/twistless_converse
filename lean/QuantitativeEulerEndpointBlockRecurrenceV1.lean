module

public import QuantitativeEulerEndpointBlockUpdateV1
public import QuantitativeEulerEndpointBlockRecurrenceScalarV1
public import QuantitativeEulerEndpointSubcornerMassV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlockRecurrence
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
  (hsource : ∀ i x, B i x*QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x=B i x)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp
local notation "τ" => rootedTrace hact s hs p hp μ hf
local notation "hτ" => rootedTrace_mono hact s hs p hp μ hf
local notation "F" => gramSum hact s hs p hp B hmB hcB C hC hsource
local notation "R" => rows hact s hs B q
local notation "hmR" => rows_measurable hact s hs B hmB q
local notation "hcR" => rows_covariant hact s hs B hcB q
local notation "hCR" => rows_norm hact s hs B C hC q hq
local notation "hsrcR" => rows_source hact s hs B q hq
local notation "D" => gramSum hact s hs q hq R hmR hcR C hCR hsrcR
local notation "υ" => rootedTrace hact s hs q hq μ hf
local notation "hυ" => rootedTrace_mono hact s hs q hq μ hf

include U hU V hV hq in
/-- The actual one-block soft recurrence, conditional only on the hard
packet's contraction toward the desired target and numeric cutoff bounds.
All spectral mass, determinant, sharpening and solution-preservation
estimates are discharged for the same constructed polynomial. -/
theorem exists_contracting_block_update
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1)
    (hhalf : ∀ x, QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x=
      (highAt (ρ A x) (1/2)).starProjection)
    (n : ℕ) (hnorm : (∑ i : Fin n, (C i)^2)≤1)
    (c : ℝ) (hc : 0<c) {d K : ℝ}
    (hd : 0<d) (hK : 0<K) (hcut : 2*d^2<K)
    (hbound : (∑ i : Fin n, (C i)^2)+d^2≤K)
    (target rho : ℝ) (hrho0 : 0≤rho) (hrho1 : rho≤1)
    (htheta0 : 0≤Real.log (K/c^2)/Real.log (K/(2*d^2)))
    (htheta1 : Real.log (K/c^2)/Real.log (K/(2*d^2))≤1)
    (hchain : (trace μ (QuantitativeSpectralRegularPacket.projectionFamily V R c n)).toReal-target≤
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
          (1-Real.log (K/c^2)/Real.log (K/(2*d^2))))*(τ A-target)+
        (4+2*(L:ℝ))*τ (A-A^2)+(μ s).toReal*(Real.log 2/Real.log (K/(2*d^2))) := by
  obtain ⟨z,hdeg,hmass,hz0,hzA,hdef,hfixed,hloss⟩ :=
    exists_block_update hact s hs p hp μ hf U hU q hq V hV B hmB hcB C hC hsource
      hmp A hA0 hA1 hhalf n hnorm c hc hd hK hcut hbound L hJ
  refine ⟨z,hdeg,hmass,hz0,hzA,hdef,hfixed,?_⟩
  have hAA := CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one hA0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg A hA0).mpr hA1)
  have hdef0 : 0≤τ (A-A^2) := by
    have hh : 0≤A-A^2 := sub_nonneg.mpr (by simpa only [pow_two] using hAA)
    simpa only [map_zero] using hτ hh
  have hw0 : 0≤1-Real.exp (-(L:ℝ)*(d^2/32)) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg L))
      (div_nonneg (sq_nonneg d) (by norm_num))
  have hw1 : 1-Real.exp (-(L:ℝ)*(d^2/32))≤1 := by
    have he := Real.exp_pos (-(L:ℝ)*(d^2/32))
    linarith
  have hlog : 0<Real.log (K/(2*d^2)) :=
    Real.log_pos ((one_lt_div (mul_pos (by norm_num) (sq_pos_of_pos hd))).mpr hcut)
  have heta : 0≤Real.log 2/Real.log (K/(2*d^2)) :=
    div_nonneg (Real.log_nonneg (by norm_num)) hlog.le
  have hpError := QuantitativeEulerEndpointCornerCut.half_cut_trace_error
    hact s hs p hp U hU μ hf A hA0 hA1
  simp only [← hhalf] at hpError
  rw [← QuantitativeEulerEndpointSubcornerMass.initial_trace_eq hact s hs q hq μ hf] at hpError
  have hm : τ A-4*τ (A-A^2)≤
      QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf q := by
    have hh := (abs_le.mp hpError).1
    linarith
  have hrD := QuantitativeEulerEndpointSubcornerMass.survivor_mass_le_initial
    hact s hs q hq μ hf V hV R hmR hcR C hCR c hc n
  rw [← QuantitativeEulerEndpointSubcornerMass.initial_trace_eq hact s hs q hq μ hf] at hrD
  have hrArea := hrD.trans (QuantitativeEulerEndpointSubcornerMass.initial_trace_bounds
    hact s hs q hq μ hf).2
  apply soft_block_excess hdef0 hw0 hw1 hrho0 hrho1 htheta0 htheta1 heta
    ENNReal.toReal_nonneg hrArea hm hchain
  simpa only [mul_div_assoc] using hloss

#print axioms exists_contracting_block_update
end QuantitativeEulerEndpointBlockRecurrence
