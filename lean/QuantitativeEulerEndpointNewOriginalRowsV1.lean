module

public import QuantitativeEulerEndpointFullNewSourceV1
public import QuantitativeEulerEndpointBaselineRegularV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory QuantitativeArithmetic QuantitativeEulerDensityGenerators
open AsymptoticRegularObservationRows AsymptoticRegularBranchFamily AsymptoticSectorSigns
open AsymptoticObservationStack AsymptoticPolarIsometry AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

abbrev NewOriginalIndex (N q : ℕ) := (Option (UnitResidue N) ⊕ Fin (q-1)) ⊕ ↥N.primeFactors

def newOriginalRows (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : NewOriginalIndex N q → Space →L[ℂ] Space
  | .inl (.inl i) => baselineRows N (sign sector.1) hs hε t x i
  | .inl (.inr j) => AsymptoticFreshCompactDefects.row N q (NeZero.pos N) hqN (sign sector.1) hs hε t j x
  | .inr p => bad p.val (Nat.mem_primeFactors.mp p.property).1.pos
      (AsymptoticCylinderRamified.eigenvalue sector p.val) hs hε t x

def newOriginalRowBound (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : NewOriginalIndex N q → ℝ
  | .inl (.inl i) => baselineRowBound N (sign sector.1) hs hε t i
  | .inl (.inr j) => AsymptoticFreshCompactDefects.rowBound N q (NeZero.pos N) hqN (sign sector.1) hs hε t j
  | .inr p => familyBound (ramifiedBranches p.val (Nat.mem_primeFactors.mp p.property).1.pos)
      (Sum.elim (fun _ => 1) (fun _ => -AsymptoticCylinderRamified.eigenvalue sector p.val)) hs hε t

theorem newOriginalRowBound_nonneg (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (i : NewOriginalIndex N q) :
    0≤newOriginalRowBound N sector q hqN hs hε t i := by
  rcases i with (i | j) | p
  · exact baseline_row_bound_nonneg N (sign sector.1) hs hε t i
  · exact AsymptoticFreshCompactDefects.rowBound_nonneg N q (NeZero.pos N) hqN _ hs hε t j
  · exact familyBound_nonneg _ _ hs hε t

theorem newOriginalRows_norm (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (i : NewOriginalIndex N q) :
    ‖newOriginalRows N sector q hqN hs hε t x i‖≤newOriginalRowBound N sector q hqN hs hε t i := by
  rcases i with (i | j) | p
  · exact baseline_row_norm N (sign sector.1) hs hε t x i
  · exact AsymptoticFreshCompactDefects.row_norm_le N q (NeZero.pos N) hqN _ hs hε t j x
  · exact family_norm_le _ _ hs hε t x

theorem newOriginalRows_regular (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (i : NewOriginalIndex N q) :
    (∀ g h, Measurable (fun x => matrix (newOriginalRows N sector q hqN hs hε t x i) g h)) ∧
      Covariant (fun x => newOriginalRows N sector q hqN hs hε t x i) := by
  rcases i with (i | j) | p
  · exact baseline_rows_regular N (sign sector.1) hs hε t i
  · exact AsymptoticFreshCompactDefects.row_regular N q (NeZero.pos N) hqN _ hs hε t j
  · exact ⟨family_matrix_measurable _ _ hs hε t,family_covariant _ _ hs hε t⟩

/-- The absolute detector of the actual fixed original rows, original
ramified rows and shifted individual fresh-prime rows. -/
def newOriginalDetector (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) : Space →L[ℂ] Space :=
  absolute (stack (newOriginalRows N sector q hqN hs hε t x))

theorem newOriginalDetector_energy (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (v : Space) :
    ‖newOriginalDetector N sector q hqN hs hε t x v‖^2=
      primeOldOriginalEnergy sector q hqN hs hε t x v := by
  unfold newOriginalDetector
  rw [←absolute_norm,PiLp.norm_sq_eq_of_L2]
  simp [newOriginalRows,primeOldOriginalEnergy,baselineRows,fixedPrimeStack,
    PiLp.norm_sq_eq_of_L2,Fintype.sum_sum_type,Fintype.sum_option,stack_apply]

theorem newOriginalDetector_regular (N : ℕ) [NeZero N] (sector : Sector N)
    (q : ℕ) [Fact q.Prime] (hqN : ¬q∣N) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    ∃ M : ℝ, 0≤M ∧ (∀ x, ‖newOriginalDetector N sector q hqN hs hε t x‖≤M) ∧
      (∀ g h, Measurable (fun x => matrix (newOriginalDetector N sector q hqN hs hε t x) g h)) ∧
      Covariant (newOriginalDetector N sector q hqN hs hε t) := by
  let M := ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : NewOriginalIndex N q => Space)).symm.toContinuousLinearMap‖*
    ∑ i,newOriginalRowBound N sector q hqN hs hε t i
  have hM : 0≤M := mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ =>
    newOriginalRowBound_nonneg N sector q hqN hs hε t i))
  have hb (x : ℍ) : ‖stack (newOriginalRows N sector q hqN hs hε t x)‖≤M :=
    stack_norm_le _ _ (newOriginalRowBound_nonneg N sector q hqN hs hε t)
      (newOriginalRows_norm N sector q hqN hs hε t x)
  have hr := stack_absolute_regular (newOriginalRows N sector q hqN hs hε t)
    (fun i => (newOriginalRows_regular N sector q hqN hs hε t i).1)
    (fun i => (newOriginalRows_regular N sector q hqN hs hε t i).2) M hb
  exact ⟨M,hM,fun x => by simpa only [newOriginalDetector,absolute_opNorm] using hb x,hr⟩

#print axioms newOriginalRows_regular
#print axioms newOriginalDetector_energy
#print axioms newOriginalDetector_regular
end QuantitativeEulerEndpointPrepared
