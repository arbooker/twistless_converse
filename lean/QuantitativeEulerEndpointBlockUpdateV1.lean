module

public import QuantitativeEulerEndpointBlockMassV1
public import QuantitativeEulerEndpointCutDefectV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlockUpdate
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointBlockGram
open QuantitativeEulerEndpointBlockMass QuantitativeEulerEndpointSoftUpdate MeasureTheory Polynomial
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

theorem gramSum_kills (n : ℕ) (E : 𝔄)
    (hE : ∀ i : Fin n, ∀ x, B i x*ρ E x=0) : F n*E=0 := by
  apply representation_injective hact s hs p hp
  funext x
  change ρ (F n) x*ρ E x=0
  rw [representation_gramSum,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_assoc,hE i x,mul_zero]

include U hU V hV hq in
/-- A complete one-block polynomial update: the detected mass lower bound
comes from the actual restricted packet, exact original-row solutions are
preserved, and the output sharpening has explicit complexity and defect. -/
theorem exists_block_update
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    (A : 𝔄) (hA0 : 0≤A) (hA1 : A≤1)
    (hhalf : ∀ x, QuantitativeSpectralRegularAlgebra.representation G α hact s hs q x=
      (highAt (ρ A x) (1/2)).starProjection)
    (n : ℕ) (hnorm : (∑ i : Fin n, (C i)^2)≤1)
    (c : ℝ) (hc : 0<c) {d K : ℝ}
    (hd : 0<d) (hK : 0<K) (hcut : 2*d^2<K)
    (hbound : (∑ i : Fin n, (C i)^2)+d^2≤K)
    (L : ℕ) {J : ℕ} (hJ : 0<J) :
    let m := QuantitativeSpectralFiniteCornerTrace.rootedTrace μ hact s hs hf q
    let r := (trace μ (QuantitativeSpectralRegularPacket.projectionFamily V R c n)).toReal
    ∃ z : ℝ[X], z.natDegree≤16*J^5+1 ∧
      (∑ i∈z.support, |z.coeff i|)≤(((16*J^5:ℕ):ℝ)+2)*3^(16*J^5) ∧
      0≤aeval (update A (A*F n*A) L) z ∧ aeval (update A (A*F n*A) L) z≤A ∧
      τ (aeval (update A (A*F n*A) L) z-(aeval (update A (A*F n*A) L) z)^2)≤4*τ 1/(J:ℝ) ∧
      (∀ E : 𝔄, A*E=E → (∀ i : Fin n, ∀ x, B i x*ρ E x=0) →
        aeval (update A (A*F n*A) L) z*E=E) ∧
      (1-Real.exp (-(L:ℝ)*(d^2/32)))*
        (m-(r+(m-r)*Real.log (K/c^2)/Real.log (K/(2*d^2))+
          r*Real.log 2/Real.log (K/(2*d^2))))-2*(L:ℝ)*τ (A-A^2)≤
        τ A-τ (aeval (update A (A*F n*A) L) z) := by
  dsimp only
  have hF0 := gramSum_nonneg hact s hs p hp B hmB hcB C hC hsource n
  have hF1 := gramSum_le_one hact s hs p hp B hmB hcB C hC hsource n hnorm
  have hCA : A*F n*A≤A^2 := by
    simpa only [inv_one,one_smul] using compressed_energy_le_square A (F n) hA0
      (by norm_num : (0:ℝ)<1) (by simpa only [one_smul] using hF1)
  obtain ⟨z,hdeg,hmass,hz0,hzA,hdef,hfixed,hloss⟩ :=
    exists_sharpened_update_with_loss τ hτ (rootedTrace_cyclic hact s hs p hp μ hf hmp)
      A (A*F n*A) hA0 hA1 (conjugate_nonneg_of_nonneg hF0 hA0) hCA L (d^2/32) hJ
  refine ⟨z,hdeg,hmass,hz0,hzA,hdef,?_,?_⟩
  · intro E hAE hBE
    apply hfixed E hAE
    have hFE := gramSum_kills hact s hs p hp B hmB hcB C hC hsource n E hBE
    rw [mul_assoc,hAE,mul_assoc,hFE,mul_zero]
  · have hdet := block_detected_mass hact s hs p hp μ hf U hU q hq V hV
      B hmB hcB C hC hsource hmp A hA0 hhalf n c hc hd hK hcut hbound
    dsimp only at hdet
    have hw : 0≤1-Real.exp (-(L:ℝ)*(d^2/32)) := by
      apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg L))
        (div_nonneg (sq_nonneg d) (by norm_num))
    have hh := mul_le_mul_of_nonneg_left hdet hw
    linarith

#print axioms gramSum_kills
#print axioms exists_block_update
end QuantitativeEulerEndpointBlockUpdate
