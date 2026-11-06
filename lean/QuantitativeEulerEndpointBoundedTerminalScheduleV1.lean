module

public import QuantitativeEulerEndpointBoundedTerminalSoftV1
public import QuantitativeEulerEndpointControlledParametersV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedTerminal
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open QuantitativeEulerEndpointControlledIteration

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable {s : Set UpperHalfPlane} (hs : IsCompact s) (l : List (EligiblePrime N))
variable (C : ℕ → ℝ)
  (hC : ∀ i x,‖normalizedCombinedRows A P e hs l i x‖≤C i)
local notation "r" => QuantitativeEulerEndpointBlockNormalization.factor C (l.length+1)
local notation "area" => (AsymptoticReconstructedCount.parameters A P).ε⁻¹

def logCost (c : ℝ) : ℝ := Real.log (2/(r*c)^2)
def effort (n j : ℕ) (c : ℝ) : ℝ :=
  QuantitativeEulerEndpointLocalEffort.effort n j (logCost l C c)

omit [NeZero N] in
theorem logCost_nonneg {c : ℝ} (hc : 0<c) (hu : r*c≤1) : 0≤logCost l C c := by
  have hr := QuantitativeEulerEndpointBlockNormalization.factor_pos C (l.length+1)
  have hrc : 0<r*c := mul_pos hr hc
  apply Real.log_nonneg
  apply (one_le_div (sq_pos_of_pos hrc)).mpr
  nlinarith

/-- The finite-horizon schedule pays the actual normalized threshold, the
attenuation and the propagated incoming defect on the full terminal strip.
No positivity assumption on signed trace excess is used. -/
theorem exists_scheduled_next (n j : ℕ) (hj : j≤n)
    (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1) (target c : ℝ)
    (hc : 0<c) (hu : r*c≤1)
    (hchain : cornerMass (fun x => QuantitativeSpectralDeflationChain.chain (half A P F x)
      (fun i => normalizedCombinedRows A P e hs l i x) c (l.length+1))-target≤
      (l.map primeFactor).prod*(cornerMass (half A P F)-target))
    (hdef : tr A P (F-F^2)≤4*area/(sharpness area (effort l C n j c):ℝ))
    {T : ℕ} (hT : 0<T) :
    let E := effort l C n j c
    ∃ z : ℝ[X], z.natDegree≤16*T^5+1 ∧
      (∑ i∈z.support,|z.coeff i|)≤(((16*T^5:ℕ):ℝ)+2)*3^(16*T^5) ∧
      QuantitativeEulerEndpointBernstein.ScalarSharpening z ∧
      0≤next A P e hs l C hC F (power E) z ∧ next A P e hs l C hC F (power E) z≤F ∧
      tr A P (next A P e hs l C hC F (power E) z-(next A P e hs l C hC F (power E) z)^2)≤4*area/(T:ℝ) ∧
      (∀ D : Algebra A P,F*D=D →
        (∀ i : Fin (l.length+1),∀ x,normalizedCombinedRows A P e hs l i x*rep A P D x=0) →
        next A P e hs l C hC F (power E) z*D=D) ∧
      max 0 (tr A P (next A P e hs l C hC F (power E) z)-target)≤
        ((l.map primeFactor).prod+2*blockRelativeLoss n j)*max 0 (tr A P F-target)+
          (1+area*Real.log 2)*blockAdditiveLoss n j := by
  intro E
  have harea : 0≤area := inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
  have hM := logCost_nonneg l C hc hu
  have hE : 0<E := QuantitativeEulerEndpointLocalEffort.effort_pos n j hM
  have hratio : logCost l C c/E≤blockRelativeLoss n j :=
    QuantitativeEulerEndpointLocalEffort.effort_ratio n j hj hM
  have hinverse : 1/E≤blockAdditiveLoss n j :=
    QuantitativeEulerEndpointLocalEffort.effort_inverse n j hj hM
  have htheta0 : 0≤logCost l C c/E := div_nonneg hM hE.le
  have htheta1 : logCost l C c/E≤1 :=
    hratio.trans (QuantitativeEulerEndpointControlledParameters.relative_le_one n j hj)
  have htheta : Real.log (2/(r*c)^2)/Real.log (2/(2*(cut E)^2))=logCost l C c/E := by
    rw [cut_log]
    rfl
  obtain ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,hrec⟩ :=
    exists_next A P e hs l C hC F hF0 hF1 c hc (cut_pos E) (by norm_num : (0:ℝ)<2)
      (cut_conditions hE).1 (cut_conditions hE).2 target
      (by rw [htheta]; exact htheta0) (by rw [htheta]; exact htheta1) hchain (power E) hT
  refine ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,?_⟩
  rw [htheta,cut_log] at hrec
  have he0 : 0≤Real.exp (-(power E:ℝ)*((cut E)^2/32)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(power E:ℝ)*((cut E)^2/32))≤1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity))
  have hcoef := coefficient_bounds (primeProduct_nonneg l)
    (QuantitativeEulerEndpointControlledPacket.primeProduct_le_one l) htheta0 htheta1 he0 he1
  have hrel : logCost l C c/E+Real.exp (-(power E:ℝ)*((cut E)^2/32))≤2*blockRelativeLoss n j := by
    have hh := (attenuation hE).trans (hinverse.trans (QuantitativeEulerEndpointControlledParameters.additive_le_relative n j))
    linarith
  have hamp : 0≤4+2*(power E:ℝ) := by positivity
  have hsharp := sharpness_error harea hE (le_refl area)
  have hpaid := (mul_le_mul_of_nonneg_left hdef hamp).trans hsharp
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hscale : 0≤1+area*Real.log 2 := by positivity
  have herror : (4+2*(power E:ℝ))*tr A P (F-F^2)+area*(Real.log 2/E)≤
      (1+area*Real.log 2)*blockAdditiveLoss n j := by
    have hh := mul_le_mul_of_nonneg_left hinverse hscale
    calc
      _ ≤ 1/E+area*(Real.log 2/E) := add_le_add hpaid le_rfl
      _ = (1+area*Real.log 2)*(1/E) := by ring
      _ ≤ _ := hh
  have herr0 : 0≤(1+area*Real.log 2)*blockAdditiveLoss n j :=
    mul_nonneg hscale (blockAdditiveLoss_nonneg n j)
  have hrec' : tr A P (next A P e hs l C hC F (power E) z)-target≤
      (1-(1-Real.exp (-(power E:ℝ)*((cut E)^2/32)))*(1-(l.map primeFactor).prod)*
        (1-logCost l C c/E))*(tr A P F-target)+
        (1+area*Real.log 2)*blockAdditiveLoss n j := by linarith [hrec,herror]
  have hpos := positive_part_step hcoef.1 herr0 hrec'
  have hcoef' : 1-(1-Real.exp (-(power E:ℝ)*((cut E)^2/32)))*(1-(l.map primeFactor).prod)*
      (1-logCost l C c/E)≤(l.map primeFactor).prod+2*blockRelativeLoss n j := by
    linarith [hcoef.2]
  exact hpos.trans (add_le_add (mul_le_mul_of_nonneg_right hcoef' (le_max_left _ _)) le_rfl)

#print axioms logCost_nonneg
#print axioms exists_scheduled_next
end QuantitativeEulerEndpointBoundedTerminal
