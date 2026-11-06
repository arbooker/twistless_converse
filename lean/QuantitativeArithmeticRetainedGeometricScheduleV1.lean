module

public import QuantitativeArithmeticRetainedApproximationScheduleV1
public import QuantitativeHolomorphicGrowingScaledTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedGeometricSchedule
open QuantitativeArithmeticEnvelope
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization QuantitativeArithmeticRetainedFiniteTransport
open QuantitativeArithmeticRetainedGrowingEnvelope QuantitativeArithmeticRetainedGeometricTrace
open QuantitativeArithmeticRetainedApproximationSchedule
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticFiniteBranch AsymptoticSectorSigns

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (P : Parameters A) (hS : ∀p∈S,p.Prime) (hN : 0<N)

def upperHeight (s : ℝ) : ℝ := Real.exp (16*s)
def bottom (d : ℝ → ℕ) (s : ℝ) : ℝ := lowerHeight A P (tolerance s (d s))
def matrixHeight (R : ℝ → ℝ) (d : ℝ → ℕ) (s : ℝ) : ℝ :=
  let B := normalizerMatrixHeight A P hS hN (tolerance s (d s))
  4*B^2*(2*max 1 (8*(R s)^2*B^2))^(d s)*(upperHeight s+2)
def complexity (e : Sector N) (M L : ℝ → ℝ) (d : ℝ → ℕ) (s : ℝ) : ℝ :=
  let V := normalizedExpression A P hS hN (tolerance s (d s)) e
  expressionBound V^2*(1+M s*expressionBound V^2)^(d s)+
    (V.length:ℝ)^2*(1+L s*(V.length:ℝ)^2)^(d s)

theorem bottom_pos (d : ℝ → ℕ) (s : ℝ) : 0<bottom A P d s := lowerHeight_pos A P (tolerance_pos _ _)
theorem matrixHeight_nonneg (R : ℝ → ℝ) (d : ℝ → ℕ) (s : ℝ) : 0≤matrixHeight A P hS hN R d s := by
  unfold matrixHeight upperHeight
  positivity

theorem complexity_nonneg (e : Sector N) (M L : ℝ → ℝ) (d : ℝ → ℕ) (s : ℝ)
    (hm : 0≤M s) (hl : 0≤L s) : 0≤complexity A P hS hN e M L d s := by
  unfold complexity
  positivity

/-- All four geometric quantities come from the scheduled mixed expression.
Only growth of the actual row aggregates and observation degree is used. -/
theorem common_growth (e : Sector N) (R M L : ℝ → ℝ) (d : ℝ → ℕ)
    (hR : Exp 2 R) (hM : Exp 2 M) (hL : Exp 2 L)
    (hR0 : ∀s,1≤s → 0≤R s) (hM0 : ∀s,1≤s → 0≤M s) (hL0 : ∀s,1≤s → 0≤L s)
    (hd : Exp 2 (fun s => (d s:ℝ))) :
    ∃K : ℝ,0≤K ∧ ∀s : ℝ,1≤s →
      matrixHeight A P hS hN R d s≤Real.exp (Real.exp (K*s^2)) ∧
      upperHeight s≤Real.exp (Real.exp (K*s^2)) ∧
      (bottom A P d s)⁻¹≤Real.exp (Real.exp (K*s^2)) ∧
      complexity A P hS hN e M L d s≤Real.exp (Real.exp (K*s^2)) := by
  have hu := logAccuracy_growth d hd
  have hh : Exp 1 upperHeight := ⟨16,by norm_num,fun _ _ => by simp only [upperHeight,pow_one]; exact le_rfl⟩
  have hhp : DoubleExp (fun s => upperHeight s+2) := (hh.add (Exp.const 2 1)).toDoubleExp
  have hm0 := actual_matrix_growth A P hS hN (fun s => logAccuracy s (d s)) R d hu.1 hu.2 hR hR0 hd
  have hm : DoubleExp (matrixHeight A P hS hN R d) := by
    have hh := hm0.mul hhp (fun s _ => by unfold upperHeight; positivity)
    simpa only [DoubleExp,matrixHeight,←tolerance_eq] using hh
  have hf : DoubleExp (complexity A P hS hN e M L d) := by
    have hh := actual_complexity_growth A P hS hN e (fun s => logAccuracy s (d s)) M L d
      hu.1 hu.2 hM hL hM0 hL0 hd
    simpa only [DoubleExp,complexity,←tolerance_eq] using hh
  have hy : DoubleExp (fun s => (bottom A P d s)⁻¹) := by
    have hh := ((QuantitativeArithmeticRetainedScheduleGrowth.height_inverse_growth A P).compPoly hu.1 hu.2).toDoubleExp
    simpa only [bottom,QuantitativeArithmeticRetainedScheduleGrowth.height,←tolerance_eq] using hh
  obtain ⟨c₁,h₁,b₁⟩ := hm
  obtain ⟨c₂,h₂,b₂⟩ := hh.toDoubleExp
  obtain ⟨c₃,h₃,b₃⟩ := hy
  obtain ⟨c₄,h₄,b₄⟩ := hf
  refine ⟨c₁+c₂+c₃+c₄,by positivity,fun s hs => ?_⟩
  exact ⟨(b₁ s hs).trans (double_exp_mono (by linarith)),
    (b₂ s hs).trans (double_exp_mono (by linarith)),
    (b₃ s hs).trans (double_exp_mono (by linarith)),
    (b₄ s hs).trans (double_exp_mono (by linarith))⟩

/-- The actual mixed geometric trace error fits the manuscript's observation
scale. This specializes the checked general trace theorem; it does not assume
geometric separation or a trace-error estimate. -/
theorem geometric_rate (e : Sector N) (R M L : ℝ → ℝ) (d : ℝ → ℕ)
    (hR : Exp 2 R) (hM : Exp 2 M) (hL : Exp 2 L)
    (hR0 : ∀s,1≤s → 0≤R s) (hM0 : ∀s,1≤s → 0≤M s) (hL0 : ∀s,1≤s → 0≤L s)
    (hd : Exp 2 (fun s => (d s:ℝ))) :
    ∃K : ℝ,0≤K ∧ ∀a : ℝ,∀h : ℕ,0<h →
      1≤Real.log (observationScale a (h+1)) →
      32≤Real.log (Real.log (h+1:ℝ)) →
      (geometryGrowthCoefficient+29+K)*a^2≤1/2 →
      let s := Real.log (observationScale a (h+1))
      let D := matrixHeight A P hS hN R d s
      let Y := bottom A P d s
      let H := upperHeight s
      let F := complexity A P hS hN e M L d s
      (h+1:ℝ)^(-(1/3:ℝ))*D≤1 ∧
      F*QuantitativeHolomorphic.uniformRetainedTraceError D Y H h (periodizationSet Y H).card≤
        Real.exp (-Real.log (h+1:ℝ)/4) := by
  obtain ⟨K,hK,hk⟩ := common_growth A P hS hN e R M L d hR hM hL hR0 hM0 hL0 hd
  refine ⟨K,hK,fun a h hh hs hlog hscale => ?_⟩
  let s := Real.log (observationScale a (h+1))
  have hb := hk s hs
  exact growing_retained_trace_at_scale h hh (matrixHeight_nonneg A P hS hN R d s)
    (bottom_pos A P d s) (Real.exp_pos _) (complexity_nonneg A P hS hN e M L d s (hM0 s hs) (hL0 s hs))
    hK hs hlog hscale hb.1 hb.2.1 hb.2.2.1 hb.2.2.2

#print axioms common_growth
#print axioms geometric_rate
end QuantitativeArithmeticRetainedGeometricSchedule
