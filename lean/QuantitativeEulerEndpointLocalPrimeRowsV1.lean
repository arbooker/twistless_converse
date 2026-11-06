module

public import QuantitativeEulerEndpointLocalOldTracesV1
public import QuantitativeEulerEndpointLocalControlAlgebraV1
public import QuantitativeSpectralObservabilityPrimeOldDataV1
public import AsymptoticSimpleOldAnnihilationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticCongruenceStrip AsymptoticSectorSigns AsymptoticRegularBranchFamily
open QuantitativeSpectralObservability QuantitativeNewGap QuantitativeArithmeticCrossPrime
open AsymptoticRegularCompactBranch (Space)
open scoped Classical

private theorem cosetTraceRow_group_transport (N : ℕ) (V : Subspace ℂ Ring)
    {J K : Subgroup G} (hJK : J=K) {ι : Type*} [Fintype ι]
    (hK : ∀ (r : ι → K) (e : ι ≃ K ⧸ (gamma N).subgroupOf K),
      (∀ i,e i=QuotientGroup.mk (r i)) → cosetTraceRow r∈V)
    (r : ι → J) (e : ι ≃ J ⧸ (gamma N).subgroupOf J)
    (he : ∀ i,e i=QuotientGroup.mk (r i)) : cosetTraceRow r∈V := by
  subst K
  exact hK r e he

theorem oldGroup_cosetTrace_mem (N : ℕ) (hN : 0<N) (p : ℕ) (hp : p.Prime) (hpN : p∣N)
    (sector : Sector N) (b : Bool) {ι : Type*} [Fintype ι] (r : ι → oldGroup N hN p b)
    (e : ι ≃ oldGroup N hN p b ⧸ (gamma N).subgroupOf (oldGroup N hN p b))
    (he : ∀ i,e i=QuotientGroup.mk (r i)) :
    cosetTraceRow r∈localRowSpan N p hN hp.pos (sign sector.1)
      (AsymptoticCylinderRamified.eigenvalue sector p) := by
  rcases hpN with ⟨M,rfl⟩
  have hM : 0<M := Nat.pos_of_mul_pos_left hN
  let : Fact p.Prime := ⟨hp⟩
  have hw : sign sector.1*sign sector.1=1 := by simpa only [pow_two] using sign_sq sector.1
  have hsq : p^2∣p*M ↔ p∣M := by rw [pow_two,Nat.mul_dvd_mul_iff_left hp.pos]
  have hfirst : oldGroup (p*M) hN p false=gamma M := by
    simp only [oldGroup,Bool.false_eq_true,ite_false,Nat.mul_div_cancel_left M hp.pos]
  have hsecond : oldGroup (p*M) hN p true=frickeOldGroup (p*M) M hN := by
    simp only [oldGroup,ite_true,Nat.mul_div_cancel_left M hp.pos]
  by_cases hpM : p∣M
  · rw [AsymptoticCylinderRamified.eigenvalue,ite_eq_left (hsq.mpr hpM)]
    cases b
    · apply cosetTraceRow_group_transport (p*M) _ hfirst ?_ r e he
      intro r' e' he'
      exact repeated_lower_cosetTrace_mem M p hM hp.pos hpM (sign sector.1) hw r' e' he'
    · apply cosetTraceRow_group_transport (p*M) _ hsecond ?_ r e he
      intro r' e' he'
      exact repeated_fricke_cosetTrace_mem M p hM hp.pos hpM (sign sector.1) r' e' he'
  · rw [AsymptoticCylinderRamified.eigenvalue,ite_eq_right (fun h => hpM (hsq.mp h))]
    cases b
    · apply cosetTraceRow_group_transport (p*M) _ hfirst ?_ r e he
      intro r' e' he'
      exact simple_lower_cosetTrace_mem M p hM hpM (sign sector.1) (delta sector p)
        (delta_sq sector p) r' e' he'
    · apply cosetTraceRow_group_transport (p*M) _ hsecond ?_ r e he
      intro r' e' he'
      exact simple_fricke_cosetTrace_mem M p hM hpM (sign sector.1) (delta sector p)
        hw (delta_sq sector p) r' e' he'

def primeOldRingRow (N : ℕ) (hN : 0<N) (i : PrimeOldIndex N) : Ring :=
  (((gamma N).subgroupOf (primeOldGroup N hN i)).index:ℂ)⁻¹ •
    cosetTraceRow (primeOldRepresentatives N hN i)

theorem primeOldRingRow_mem (N : ℕ) (hN : 0<N) (sector : Sector N) (i : PrimeOldIndex N) :
    primeOldRingRow N hN i∈localRowSpan N i.1.val hN
      (Nat.mem_primeFactors.mp i.1.property).1.pos (sign sector.1)
      (AsymptoticCylinderRamified.eigenvalue sector i.1.val) := by
  apply Submodule.smul_mem
  exact oldGroup_cosetTrace_mem N hN i.1.val (Nat.mem_primeFactors.mp i.1.property).1
    (Nat.mem_primeFactors.mp i.1.property).2.1 sector i.2
    (primeOldRepresentatives N hN i) (Equiv.refl _) (fun q => (Quotient.out_eq q).symm)

/-- Exact identification with the normalized old row used by the existing
newspace detector, including its actual Quotient.out representatives. -/
theorem compactAction_primeOldRingRow (N : ℕ) (hN : 0<N) (i : PrimeOldIndex N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (primeOldRingRow N hN i)=
      AsymptoticRegularBranchFamily.family (oldBranches (primeOldRepresentatives N hN i))
        (oldCoefficients N (primeOldGroup N hN i)) hs hε t x := by
  rw [primeOldRingRow,map_smul,cosetTraceRow,map_sum,Finset.smul_sum]
  unfold AsymptoticRegularBranchFamily.family oldCoefficients oldBranches
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := compactAction_branch hs hε t x
    (projectiveBranch (primeOldRepresentatives N hN i j).val⁻¹)
  rw [show AsymptoticRationalBranches.ofMatrix
      (projectiveBranch (primeOldRepresentatives N hN i j).val⁻¹).matrix
      (projectiveBranch (primeOldRepresentatives N hN i j).val⁻¹).positive=
      (primeOldRepresentatives N hN i j).val⁻¹ from projectiveBranch_label _] at h
  exact h

theorem primeOldRingRow_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (sector : Sector N) (i : PrimeOldIndex N) :
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      WideLocalControl P i.1.val (Nat.mem_primeFactors.mp i.1.property).1.pos (sign sector.1)
        (AsymptoticCylinderRamified.eigenvalue sector i.1.val) (primeOldRingRow N (NeZero.pos N) i) B K := by
  exact wide_local_span_control P _ _ _ _ (by simpa only [pow_two] using sign_sq sector.1) _
    (primeOldRingRow_mem N (NeZero.pos N) sector i)

#print axioms oldGroup_cosetTrace_mem
#print axioms primeOldRingRow_mem
#print axioms compactAction_primeOldRingRow
#print axioms primeOldRingRow_original_control
end QuantitativeEulerEndpointPrepared
