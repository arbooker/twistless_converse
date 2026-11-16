module

public import QuantitativeMaassCountingOrbitLawsV1
public import AsymptoticTwistObservationFormulaV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticOrbitDecode AsymptoticRegularObservationRows AsymptoticRationalBranches
open AsymptoticRationalFreeness AsymptoticSectorSigns QuantitativeNewGap
open scoped lp
namespace QuantitativeMaass.CountingMetric

/-- The positive cap can be removed pointwise from an actual strip lift. -/
theorem decode_cap_lift (N : ℕ) {δ : ℝ} (hδ : 0<δ) (ν : ℕ) (z : ℍ)
    (f : Classes (gamma N)→ℂ) (v : AsymptoticRegularCompactBranch.Space)
    (hv : ∀ a,v a=AsymptoticMassTransport.strip.indicator
      (fun w => (AsymptoticCompactBranch.cap δ ν w:ℂ)*f (classOf (gamma N) a)) (a • z))
    (a : AsymptoticRationalGroup.Group) :
    decode δ ν z v a=f (classOf (gamma N) a) := by
  rw [decode,hv,Set.indicator_of_mem (AsymptoticCongruenceQuotient.foldLabel_mem z a),
    AsymptoticCongruenceQuotient.cap_fold]
  have hc : classOf (gamma N) (foldLabel z a)=classOf (gamma N) a :=
    AsymptoticCongruenceQuotient.foldLabel_class N z a
  rw [hc]
  exact mul_div_cancel_left₀ _ (cap_ne_zero hδ ν (a • z))

theorem translation_coe (r : ℚ) (w : ℍ) :
    ((ofMatrix (translation r).matrix (translation r).positive • w : ℍ):ℂ)=
      (w:ℂ)+(r:ℂ) := by
  rw [ofMatrix_action]
  change ((realMatrix (AsymptoticMobiusFold.translation r) • w : ℍ):ℂ)=_
  rw [realMatrix_translation,AsymptoticMobiusFold.translation_action]
  simp

theorem reflected_coe (N q : ℕ) (hN : 0<N) (hq : 0<q) (j : ℕ) (w : ℍ) :
    ((ofMatrix (reflected N q hN hq j).matrix
      (reflected N q hN hq j).positive • w : ℍ):ℂ)=
      -1/((Nat.lcm N (q^2):ℂ)*(w:ℂ))+(j:ℂ)/q := by
  rw [ofMatrix_action]
  change ((realMatrix (AsymptoticReconstructionBranch.branch (Nat.lcm N (q^2):ℚ) 0
    ((j:ℚ)/q) (by exact_mod_cast (Nat.lcm_pos hN (pow_pos hq 2)).ne')) • w : ℍ):ℂ)=_
  rw [realMatrix_branch]
  simpa using AsymptoticReconstructionBranch.branch_action
    (show (0:ℝ)<Nat.lcm N (q^2) by exact_mod_cast Nat.lcm_pos hN (pow_pos hq 2))
    0 ((j:ℝ)/q) w

/-- The analytic twist equation annihilates the literal rational branch row. -/
theorem twist_row_zero_of_decode (N q : ℕ) (hN : 0<N) (hq : 0<q) (χ : ℂ)
    {δ : ℝ} (hδ : 0<δ) (ν : ℕ) (z : ℍ) (F : ℂ→ℂ)
    (v : AsymptoticRegularCompactBranch.Space)
    (hv : ∀ a,decode δ ν z v a=F ((a • z : ℍ):ℂ))
    (hF : ∀ w : ℍ,FinitenessAnalyticReconstruction.twist F q w=
      χ*FinitenessAnalyticReconstruction.twist F q (-1/((Nat.lcm N (q^2):ℂ)*(w:ℂ))))
    (s : Set ℍ) (hs : IsCompact s) : twist N q hN hq χ hs hδ ν z v=0 := by
  apply (all_compact_family_zero_iff (twistBranches N q hN hq)
    (Sum.elim (fun _ => 1) (fun _ => -χ)) hδ ν z v).mpr _ s hs
  intro a
  rw [Fintype.sum_sum_type]
  simp only [twistBranches,Sum.elim_inl,Sum.elim_inr,one_mul,hv,mul_smul]
  simp_rw [translation_coe,reflected_coe]
  push_cast
  rw [←Finset.mul_sum]
  have hh := hF (a • z)
  simp only [AsymptoticTwistObservation.twist_eq_residues] at hh
  linear_combination hh

/-- All compact original rows vanish on the unnormalized cap lift of a
canonical counting-sector vector, at every free rational orbit. -/
theorem countingSector_cap_rows (N : ℕ) (hN : 0<N) (e : Sector N)
    {δ : ℝ} (hδ : 0<δ) (ν : ℕ) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e)
    (v : AsymptoticRegularCompactBranch.Space)
    (hv : ∀ a,decode δ ν z v a=f (classOf (gamma N) a))
    (r : AsymptoticCompactObservationCount.Row N) (s : Set ℍ) (hs : IsCompact s) :
    row hN r e hs hδ ν z v=0 := by
  cases r with
  | twist q hq =>
    apply twist_row_zero_of_decode N q hN hq (multiplier e q) hδ ν z
      (upperZeroExtension (orbitRepresentative N z hz f).val) v
    · intro a
      rw [hv,upperZeroExtension_apply,orbitRepresentative_apply]
    · intro w
      exact countingSector_orbit_all_laws N hN e f hf z hz q hq w
  | ramified p hp hpN =>
    apply (all_compact_ramified_zero_iff p hp.pos (AsymptoticCylinderRamified.eigenvalue e p)
      hδ ν z v).mpr _ s hs
    intro a
    simp only [hv]
    exact countingSector_ramified N hN e f hf p hp hpN a

#print axioms decode_cap_lift
#print axioms translation_coe
#print axioms reflected_coe
#print axioms twist_row_zero_of_decode
#print axioms countingSector_cap_rows
end QuantitativeMaass.CountingMetric
