module

public import QuantitativeEulerEndpointOriginalStepV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

abbrev EligiblePrime (N : ℕ) := {q : ℕ // q.Prime ∧ ¬q∣N}

instance eligible_prime_fact {N : ℕ} (p : EligiblePrime N) : Fact p.val.Prime := ⟨p.property.1⟩
instance closed_corner_complete (U : ClosedSubmodule ℂ Space) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

def primeCut (c : ℝ) (q : ℕ) : ℝ :=
  Real.sqrt (c^2*(q : ℝ)⁻¹/(2*((q-1 : ℕ) : ℝ)))

theorem primeCut_pos (c : ℝ) (hc : 0<c) (q : ℕ) [Fact q.Prime] : 0<primeCut c q := by
  have hq : 0<(q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqm : 0<((q-1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt (Fact.out : q.Prime).one_lt
  apply Real.sqrt_pos.mpr
  positivity

theorem primeCut_sq (c : ℝ) (q : ℕ) [Fact q.Prime] :
    (primeCut c q)^2=c^2*(q : ℝ)⁻¹/(2*((q-1 : ℕ) : ℝ)) := by
  apply Real.sq_sqrt
  positivity

def closedPrimeStep (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (c : ℝ) (U : ℍ → ClosedSubmodule ℂ Space)
    (p : EligiblePrime N) (x : ℍ) : ClosedSubmodule ℂ Space where
  toSubmodule := freshStepSource N p.val hN p.property.2 w hs hε t
    (fun y => (U y).toSubmodule) (primeCut c p.val) x
  isClosed' := (completeSpace_coe_iff_isComplete.mp
    (inferInstance : CompleteSpace (freshStepSource N p.val hN p.property.2 w hs hε t
      (fun y => (U y).toSubmodule) (primeCut c p.val) x))).isClosed

/-- Successive actual original-twist cuts, with threshold primeCut(c,q). -/
def primeChain (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (c : ℝ) (U : ℍ → ClosedSubmodule ℂ Space) :
    List (EligiblePrime N) → ℍ → ClosedSubmodule ℂ Space
  | [] => U
  | p::l => primeChain N hN w hs hε t c (closedPrimeStep N hN w hs hε t c U p) l

def cornerMass (U : ℍ → ClosedSubmodule ℂ Space) : ℝ :=
  (trace volume (fun x => (U x).toSubmodule.starProjection)).toReal

def primeFactor {N : ℕ} (p : EligiblePrime N) : ℝ := 1-(p.val : ℝ)⁻¹

theorem primeFactor_nonneg {N : ℕ} (p : EligiblePrime N) : 0≤primeFactor p := by
  have hp : 1≤(p.val : ℝ) := by exact_mod_cast p.property.1.one_lt.le
  exact sub_nonneg.mpr ((inv_le_one₀ (by linarith)).mpr hp)

theorem primeProduct_nonneg {N : ℕ} (l : List (EligiblePrime N)) :
    0≤(l.map primeFactor).prod := by
  induction l with
  | nil => simp
  | cons p l ih => exact mul_nonneg (primeFactor_nonneg p) ih

theorem eligible_not_dvd_of_ne {N : ℕ} (p r : EligiblePrime N) (hne : r≠p) : ¬r.val∣p.val := by
  intro hd
  rcases (Nat.dvd_prime p.property.1).mp hd with h | h
  · exact r.property.1.ne_one h
  · exact hne (Subtype.ext h)

variable (N : ℕ) (hN : 0<N) (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
variable {ε : ℝ} (hε : 0<ε) (t : ℕ) (c : ℝ)

theorem primeChain_le (U : ℍ → ClosedSubmodule ℂ Space) (l : List (EligiblePrime N)) (x : ℍ) :
    (primeChain N hN w hs hε t c U l x).toSubmodule≤(U x).toSubmodule := by
  induction l generalizing U with
  | nil => exact le_rfl
  | cons p l ih =>
    exact (ih _).trans (fresh_step_source_le N p.val hN p.property.2 w hs hε t _ _ x)

theorem primeChain_regular (hc : 0<c) (U : ℍ → ClosedSubmodule ℂ Space)
    (hmU : ∀ g h, Measurable (fun x => matrix (U x).toSubmodule.starProjection g h))
    (hcU : Covariant (fun x => (U x).toSubmodule.starProjection)) (l : List (EligiblePrime N)) :
    (∀ g h, Measurable (fun x => matrix (primeChain N hN w hs hε t c U l x).toSubmodule.starProjection g h)) ∧
      Covariant (fun x => (primeChain N hN w hs hε t c U l x).toSubmodule.starProjection) := by
  induction l generalizing U with
  | nil => exact ⟨hmU,hcU⟩
  | cons p l ih =>
    have hr := fresh_step_source_regular N p.val hN p.property.2 w hs hε t
      (fun x => (U x).toSubmodule) hmU hcU (primeCut c p.val) (primeCut_pos c hc p.val)
    exact ih _ hr.1 hr.2

theorem primeChain_supported (hc : 0<c) (U : ℍ → ClosedSubmodule ℂ Space)
    (r : ℕ) [Fact r.Prime] (hrN : ¬r∣N)
    (hU : ∀ x, Supported (integralGroup r) (U x).toSubmodule.starProjection)
    (l : List (EligiblePrime N)) (hl : ∀ p∈l, ¬r∣p.val) (x : ℍ) :
    Supported (integralGroup r) (primeChain N hN w hs hε t c U l x).toSubmodule.starProjection := by
  induction l generalizing U with
  | nil => exact hU x
  | cons p l ih =>
    apply ih _ _ (fun p hp => hl p (List.mem_cons_of_mem _ hp))
    intro y
    exact fresh_step_source_supported N p.val hN p.property.2 w hs hε t _ r hrN
      (hl p (List.mem_cons_self)) hU (primeCut c p.val) (primeCut_pos c hc p.val) y

theorem primeChain_trace_finite (U : ℍ → ClosedSubmodule ℂ Space)
    (hf : trace volume (fun x => (U x).toSubmodule.starProjection)<∞) (l : List (EligiblePrime N)) :
    trace volume (fun x => (primeChain N hN w hs hε t c U l x).toSubmodule.starProjection)<∞ :=
  projection_trace_finite_of_le volume _ _ (primeChain_le N hN w hs hε t c U l) hf

#print axioms primeChain_regular
#print axioms primeChain_supported
#print axioms primeChain_trace_finite
end QuantitativeEulerEndpointPrepared
