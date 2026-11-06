module

public import QuantitativeEulerEndpointBaselineGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerDensityGenerators QuantitativeArithmetic
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

def baselineSize (N : ℕ) [NeZero N] : NewBaselineIndex N → ℕ
  | .inl none => 1
  | .inl (some a) => (primeLift N a).q
  | .inr p => p.val

def baselineAmplitude (N : ℕ) [NeZero N] (sector : Sector N) : NewBaselineIndex N → ℝ
  | .inl _ => ‖sign sector.1‖
  | .inr p => ‖AsymptoticCylinderRamified.eigenvalue sector p.val‖

theorem baseline_row_polynomial (N : ℕ) [NeZero N] (sector : Sector N)
    (R Y H U : ℝ) (t : ℕ) (hU : 1≤U) (hN : (N:ℝ)≤U)
    (hsize : ∀ i, (baselineSize N i:ℝ)≤U) (hamp : ∀ i, baselineAmplitude N sector i≤U)
    (hR0 : 0≤R) (hR : R≤U) (hH0 : 0≤H) (hH : H≤U)
    (hY : 0<Y) (hYinv : (min 1 Y)⁻¹≤U) (i : NewBaselineIndex N) :
    wideBaselineRowBound N sector R Y H t i≤36*9^t*U^(8+10*t) := by
  cases i with
  | inl i =>
    cases i with
    | none =>
      exact wideTwistBound_polynomial N 1 (sign sector.1) R Y H U t hU hN
        (hsize (.inl none)) (hamp (.inl none)) hR0 hR hH0 hH hY hYinv
    | some a =>
      exact wideTwistBound_polynomial N (primeLift N a).q (sign sector.1) R Y H U t hU hN
        (hsize (.inl (some a))) (hamp (.inl (some a))) hR0 hR hH0 hH hY hYinv
  | inr p =>
    exact wideRamifiedBound_polynomial p.val (AsymptoticCylinderRamified.eigenvalue sector p.val)
      R Y H U t hU (hsize (.inr p)) (hamp (.inr p)) hR0 hR hH0 hH hY hYinv

/-- One level-and-sector constant controls the entire ORIGINAL baseline
initializer in every growing observation rectangle. -/
theorem exists_baseline_detector_envelope (N : ℕ) [NeZero N] (sector : Sector N) :
    ∃ M : ℝ, 4≤M ∧ ∀ U : ℝ, M≤U → ∀ R Y H : ℝ,
      0≤R → R≤U → 0≤H → H≤U → 0<Y → (min 1 Y)⁻¹≤U → ∀ t : ℕ,
      wideDetectorBound N sector R Y H t≤36*9^t*U^(10+10*t) := by
  let K := ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewBaselineIndex N => Space)).symm.toContinuousLinearMap‖
  let f : Fin 4 ⊕ (NewBaselineIndex N × Fin 2) → ℝ
    | .inl i => ![4,(N:ℝ),(Fintype.card (NewBaselineIndex N):ℝ),K] i
    | .inr (i,j) => ![(baselineSize N i:ℝ),baselineAmplitude N sector i] j
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have hM4 : 4≤M := hf (.inl 0)
  refine ⟨M,hM4,?_⟩
  intro U hU R Y H hR0 hR hH0 hH hY hYinv t
  have hU1 : 1≤U := by linarith
  have hU0 : 0≤U := by linarith
  have hsum : (∑ i,wideBaselineRowBound N sector R Y H t i)≤U*(36*9^t*U^(8+10*t)) := by
    calc
      _ ≤ ∑ _i : NewBaselineIndex N, 36*9^t*U^(8+10*t) := Finset.sum_le_sum (fun i _ =>
        baseline_row_polynomial N sector R Y H U t hU1 ((hf (.inl 1)).trans hU)
          (fun j => (hf (.inr (j,0))).trans hU) (fun j => (hf (.inr (j,1))).trans hU)
          hR0 hR hH0 hH hY hYinv i)
      _ = (Fintype.card (NewBaselineIndex N):ℝ)*(36*9^t*U^(8+10*t)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right ((hf (.inl 2)).trans hU) (by positivity)
  unfold wideDetectorBound
  calc
    _ ≤ U*(U*(36*9^t*U^(8+10*t))) := mul_le_mul ((hf (.inl 3)).trans hU) hsum
      (Finset.sum_nonneg (fun i _ => wideBaselineRowBound_nonneg N sector R Y H t i)) hU0
    _ = _ := by rw [show 10+10*t=2+(8+10*t) by omega,pow_add]; ring

#print axioms baseline_row_polynomial
#print axioms exists_baseline_detector_envelope
end QuantitativeEulerEndpointPrepared
