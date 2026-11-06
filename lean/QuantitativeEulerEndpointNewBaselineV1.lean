module

public import QuantitativeEulerEndpointNewOriginalRowsV1
public import QuantitativeEulerEndpointGoodInjectionV1
public import QuantitativeEulerEndpointSurvivorRegularV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticRegularObservationRows AsymptoticRegularBranchFamily AsymptoticSectorSigns
open AsymptoticObservationStack AsymptoticPolarIsometry AsymptoticRegularTrace
open AsymptoticIntegralSubgroup AsymptoticSubgroupSupport AsymptoticHyperbolicArea AsymptoticOrbitDiagonal
open QuantitativeSpectralCornerCutRow QuantitativeSpectralRegularCornerStep
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

abbrev NewBaselineIndex (N : ℕ) := Option (UnitResidue N) ⊕ ↥N.primeFactors

def newBaselineRows (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    NewBaselineIndex N → Space →L[ℂ] Space
  | .inl i => baselineRows N (sign sector.1) hs hε t x i
  | .inr p => bad p.val (Nat.mem_primeFactors.mp p.property).1.pos
      (AsymptoticCylinderRamified.eigenvalue sector p.val) hs hε t x

def newBaselineRowBound (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) : NewBaselineIndex N → ℝ
  | .inl i => baselineRowBound N (sign sector.1) hs hε t i
  | .inr p => familyBound (ramifiedBranches p.val (Nat.mem_primeFactors.mp p.property).1.pos)
      (Sum.elim (fun _ => 1) (fun _ => -AsymptoticCylinderRamified.eigenvalue sector p.val)) hs hε t

theorem newBaselineRowBound_nonneg (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (i : NewBaselineIndex N) :
    0≤newBaselineRowBound N sector hs hε t i := by
  cases i with
  | inl i => exact baseline_row_bound_nonneg N _ hs hε t i
  | inr p => exact familyBound_nonneg _ _ hs hε t

theorem newBaselineRows_norm (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (i : NewBaselineIndex N) :
    ‖newBaselineRows N sector hs hε t x i‖≤newBaselineRowBound N sector hs hε t i := by
  cases i with
  | inl i => exact baseline_row_norm N _ hs hε t x i
  | inr p => exact family_norm_le _ _ hs hε t x

theorem newBaselineRows_regular (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (i : NewBaselineIndex N) :
    (∀ g h, Measurable (fun x => matrix (newBaselineRows N sector hs hε t x i) g h)) ∧
      Covariant (fun x => newBaselineRows N sector hs hε t x i) := by
  cases i with
  | inl i => exact baseline_rows_regular N _ hs hε t i
  | inr p => exact ⟨family_matrix_measurable _ _ hs hε t,family_covariant _ _ hs hε t⟩

def newBaselineDetector (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  absolute (stack (newBaselineRows N sector hs hε t x))

theorem newBaselineDetector_regular (N : ℕ) [NeZero N] (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    ∃ M : ℝ, 0≤M ∧ (∀ x, ‖newBaselineDetector N sector hs hε t x‖≤M) ∧
      (∀ g h, Measurable (fun x => matrix (newBaselineDetector N sector hs hε t x) g h)) ∧
      Covariant (newBaselineDetector N sector hs hε t) := by
  let M := ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewBaselineIndex N => Space)).symm.toContinuousLinearMap‖*
    ∑ i,newBaselineRowBound N sector hs hε t i
  have hM : 0≤M := mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ =>
    newBaselineRowBound_nonneg N sector hs hε t i))
  have hb (x : ℍ) : ‖stack (newBaselineRows N sector hs hε t x)‖≤M :=
    stack_norm_le _ _ (newBaselineRowBound_nonneg N sector hs hε t)
      (newBaselineRows_norm N sector hs hε t x)
  have hr := stack_absolute_regular (newBaselineRows N sector hs hε t)
    (fun i => (newBaselineRows_regular N sector hs hε t i).1)
    (fun i => (newBaselineRows_regular N sector hs hε t i).2) M hb
  exact ⟨M,hM,fun x => by simpa only [newBaselineDetector,absolute_opNorm] using hb x,hr⟩

theorem newBaselineDetector_supported (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) (hqfixed : ∀ a : UnitResidue N, ¬q∣(primeLift N a).q)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    Supported (integralGroup q) (newBaselineDetector N sector hs hε t x) := by
  apply supported_stackAbsolute
  intro i
  cases i with
  | inl i => exact baseline_rows_supported N q hqN hqfixed _ hs hε t x i
  | inr p =>
    exact compact_family_supported q _ _
      (ramifiedBranches_integral q N p.val (Nat.mem_primeFactors.mp p.property).1.pos
        (Nat.mem_primeFactors.mp p.property).2.1 hqN) hs hε t x

/-- Exact decomposition of the original observation energy into fixed
original rows (including ramified rows) and the fresh shifted stack. -/
theorem primeOldOriginalEnergy_split (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    primeOldOriginalEnergy sector q hqN hs hε t x v=
      ‖newBaselineDetector N sector hs hε t x v‖^2+
      ‖stack (fun i => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN
        (sign sector.1) hs hε t i x) v‖^2 := by
  unfold newBaselineDetector
  rw [←absolute_norm]
  simp [newBaselineRows,primeOldOriginalEnergy,baselineRows,fixedPrimeStack,
    PiLp.norm_sq_eq_of_L2,Fintype.sum_sum_type,Fintype.sum_option,stack_apply]
  ring

/-- Actual compressed cutoff for every fixed original row, now including
all original ramified observations with the actual sector eigenvalues. -/
def newBaselineSurvivor (N : ℕ) [NeZero N] (H : ℝ) (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (x : ℍ) :
    Submodule ℂ Space :=
  nextSpace (AsymptoticOrbitRegion.Space (terminal ε\terminal H) x)
    (newBaselineDetector N sector hs hε t x) (Real.sqrt a)

instance newBaselineSurvivor_complete (N : ℕ) [NeZero N] (H : ℝ) (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (x : ℍ) :
    CompleteSpace (newBaselineSurvivor N H sector hs hε t a x) := by
  unfold newBaselineSurvivor
  infer_instance

theorem newBaselineSurvivor_energy (N : ℕ) [NeZero N] (H : ℝ) (sector : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (a : ℝ) (ha : 0≤a)
    (x : ℍ) (v : Space) (hv : v∈newBaselineSurvivor N H sector hs hε t a x) :
    ‖newBaselineDetector N sector hs hε t x v‖^2≤a*‖v‖^2 := by
  simpa only [Real.sq_sqrt ha] using nextSpace_energy _ _ (Real.sqrt a) v hv

#print axioms newBaselineDetector_regular
#print axioms newBaselineDetector_supported
#print axioms primeOldOriginalEnergy_split
#print axioms newBaselineSurvivor_energy
end QuantitativeEulerEndpointPrepared
