module

public import QuantitativeEulerEndpointBoundedIterationDataV1
public import QuantitativeEulerEndpointFiniteScheduleV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial Finset
open QuantitativeEulerEndpointBlocks

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)
variable (n : ℕ) (b : ℕ → Block A P e) (target : ℝ)
  (F : ℕ → Algebra A P) (z : ℕ → ℝ[X])
local notation "area" => (AsymptoticReconstructedCount.parameters A P).ε⁻¹

/-- The checked finite-horizon scalar bound applied to actual terminal
polynomial updates, with all sharpening and determinant errors already paid. -/
theorem finite_excess_bound
    (hsteps : ∀ j,j<n → Step A P e n b target j (F j) (z j) ∧
      F (j+1)=nextAt A P e n b j (F j) (z j))
    (bad : ℕ → ℝ) {C : ℝ} (hbad : ∀ j,0≤bad j)
    (hbudget : (∑ j∈range n,bad j)≤C)
    (hprime : ∀ j,j<n → ((b j).primes.map primeFactor).prod≤Real.exp (bad j)/4) :
    max 0 (tr A P (F n)-target)≤
      Real.exp (C+8)*(max 0 (tr A P (F 0)-target)+4*(1+area*Real.log 2))/(4:ℝ)^n := by
  have ha : 0≤area := inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
  have hB : 0≤1+area*Real.log 2 := by
    have hh : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hstep : ∀ j,j<n → max 0 (tr A P (F (j+1))-target)≤
      (Real.exp (bad j)/4+2*blockRelativeLoss n j)*max 0 (tr A P (F j)-target)+
        (1+area*Real.log 2)*blockAdditiveLoss n j := by
    intro j hj
    obtain ⟨hs,he⟩ := hsteps j hj
    have hrec := hs.excess
    rw [← he] at hrec
    exact hrec.trans (add_le_add
      (mul_le_mul_of_nonneg_right (add_le_add (hprime j hj) le_rfl) (le_max_left _ _)) le_rfl)
  simpa only [show (4:ℝ)*2=8 by norm_num] using
    finite_schedule_endpoint n (fun j => max 0 (tr A P (F j)-target)) bad
      (by norm_num : (0:ℝ)≤2) hB (fun _ _ => le_max_left _ _) hbad hbudget hstep

theorem finite_trace_bound (hzero : F 0=1) (htarget : 0≤target)
    (hsteps : ∀ j,j<n → Step A P e n b target j (F j) (z j) ∧
      F (j+1)=nextAt A P e n b j (F j) (z j))
    (bad : ℕ → ℝ) {C : ℝ} (hbad : ∀ j,0≤bad j)
    (hbudget : (∑ j∈range n,bad j)≤C)
    (hprime : ∀ j,j<n → ((b j).primes.map primeFactor).prod≤Real.exp (bad j)/4) :
    tr A P (F n)≤target+Real.exp (C+8)*(area+4*(1+area*Real.log 2))/(4:ℝ)^n := by
  have ha : 0≤area := inv_nonneg.mpr (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
  have hstart : max 0 (tr A P (F 0)-target)≤area := by
    rw [hzero,tr_one]
    exact max_le ha (sub_le_self _ htarget)
  have hh := (finite_excess_bound A P e n b target F z hsteps bad hbad hbudget hprime).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hstart le_rfl) (Real.exp_pos _).le) (by positivity))
  have hm := le_max_right 0 (tr A P (F n)-target)
  linarith

#print axioms finite_excess_bound
#print axioms finite_trace_bound
end QuantitativeEulerEndpointBoundedIteration
