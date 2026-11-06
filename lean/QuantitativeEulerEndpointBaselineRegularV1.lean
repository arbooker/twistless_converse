module

public import QuantitativeEulerEndpointBaselineCutV1
public import AsymptoticRegularStackPolarV1
public import AsymptoticIntegralObservationsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticRegularTrace AsymptoticRegularObservationRows AsymptoticRegularBranchFamily
open AsymptoticObservationStack AsymptoticPolarIsometry
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

def baselineRowBound (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : Option (UnitResidue N) → ℝ
  | none => familyBound (twistBranches N 1 (NeZero.pos N) Nat.zero_lt_one)
      (Sum.elim (fun _ => 1) (fun _ => -w)) hs hε t
  | some a => familyBound (twistBranches N (primeLift N a).q (NeZero.pos N) (primeLift N a).prime.pos)
      (Sum.elim (fun _ => 1) (fun _ => -w)) hs hε t

theorem baseline_row_bound_nonneg (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (i : Option (UnitResidue N)) :
    0≤baselineRowBound N w hs hε t i := by
  cases i <;> exact familyBound_nonneg _ _ hs hε t

theorem baseline_row_norm (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (i : Option (UnitResidue N)) :
    ‖baselineRows N w hs hε t x i‖≤baselineRowBound N w hs hε t i := by
  cases i <;> exact family_norm_le _ _ hs hε t x

theorem baseline_rows_regular (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (i : Option (UnitResidue N)) :
    (∀ g h,Measurable (fun x => matrix (baselineRows N w hs hε t x i) g h)) ∧
      Covariant (fun x => baselineRows N w hs hε t x i) := by
  cases i <;> exact ⟨family_matrix_measurable _ _ hs hε t,family_covariant _ _ hs hε t⟩

def baselineStackBound (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Option (UnitResidue N) => Space)).symm.toContinuousLinearMap‖*
    ∑ i,baselineRowBound N w hs hε t i

theorem baseline_stack_norm (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    ‖baselineStack N w hs hε t x‖≤baselineStackBound N w hs hε t :=
  stack_norm_le _ _ (baseline_row_bound_nonneg N w hs hε t) (baseline_row_norm N w hs hε t x)

theorem baseline_absolute_regular (N : ℕ) [NeZero N] (w : ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    (∀ g h,Measurable (fun x => matrix (absolute (baselineStack N w hs hε t x)) g h)) ∧
      Covariant (fun x => absolute (baselineStack N w hs hε t x)) :=
  stack_absolute_regular _ (fun i => (baseline_rows_regular N w hs hε t i).1)
    (fun i => (baseline_rows_regular N w hs hε t i).2) _ (baseline_stack_norm N w hs hε t)

/-- Freshness includes every fixed original twist modulus. -/
theorem baseline_rows_supported (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqfixed : ∀ a : UnitResidue N, ¬q∣(primeLift N a).q)
    (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)
    (x : ℍ) (i : Option (UnitResidue N)) :
    Supported (integralGroup q) (baselineRows N w hs hε t x i) := by
  cases i with
  | none =>
    exact compact_family_supported q _ _
      (twistBranches_integral q N 1 (NeZero.pos N) Nat.zero_lt_one hqN
        (Fact.out : q.Prime).not_dvd_one) hs hε t x
  | some a =>
    exact compact_family_supported q _ _
      (twistBranches_integral q N (primeLift N a).q (NeZero.pos N)
        (primeLift N a).prime.pos hqN (hqfixed a)) hs hε t x

theorem baseline_absolute_supported (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime]
    (hqN : ¬q∣N) (hqfixed : ∀ a : UnitResidue N, ¬q∣(primeLift N a).q)
    (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    Supported (integralGroup q) (absolute (baselineStack N w hs hε t x)) :=
  supported_stackAbsolute _ _ (baseline_rows_supported N q hqN hqfixed w hs hε t x)

#print axioms baseline_absolute_regular
#print axioms baseline_absolute_supported
end QuantitativeEulerEndpointPrepared
