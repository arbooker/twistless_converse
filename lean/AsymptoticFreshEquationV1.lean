module

public import AsymptoticFreshCompactDefectsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshResidues

open AsymptoticCertificateBranches

variable (q : ℕ) [Fact q.Prime]

theorem residue_pos (a : residues q) : 0<a.val := by
  have ha := (Finset.mem_filter.mp a.property).2
  by_contra hn
  have hz : a.val=0 := by omega
  have he : q=1 := by simpa only [hz,Nat.coprime_zero_left] using ha
  exact (Fact.out : q.Prime).ne_one he

/-- The q-1 row labels are exactly the residue indices used by the
existing twist observation, not a replacement set of equations. -/
def residueEquiv : Fin (q-1) ≃ residues q where
  toFun i := ⟨i.val+1,by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega),index_coprime q i⟩⟩
  invFun a := ⟨a.val-1,by
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp a.property).1
    have hp := residue_pos q a
    omega⟩
  left_inv i := by apply Fin.ext; simp
  right_inv a := by
    apply Subtype.ext
    change a.val-1+1=a.val
    exact Nat.sub_add_cancel (residue_pos q a)

theorem residueEquiv_val (i : Fin (q-1)) : (residueEquiv q i).val=i.val+1 := rfl

#print axioms residue_pos
#print axioms residueEquiv_val

end AsymptoticFreshResidues

namespace AsymptoticFreshEquation

open AsymptoticFreshCompactDefects AsymptoticFreshResidues AsymptoticRegularBranchFamily
open AsymptoticRegularObservationRows AsymptoticRationalBranches AsymptoticIntegralSubgroup
open AsymptoticCompactFamilyTranslation AsymptoticMixing
open AsymptoticRegularCompactBranch (Space)
open UpperHalfPlane ContinuousLinearMap

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

include hq in
theorem level_eq : Nat.lcm N (q^2)=N*q^2 :=
  (((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hq).symm.pow_right 2).lcm_eq_mul

include hq in
theorem reflected_label_eq (i : Fin (q-1)) :
    ofMatrix (reflected N q hN (Fact.out : q.Prime).pos (i.val+1)).matrix
      (reflected N q hN (Fact.out : q.Prime).pos (i.val+1)).positive=
    ofMatrix (reflectedBranch N q hN i).matrix (reflectedBranch N q hN i).positive := by
  apply Subtype.ext
  apply Subtype.ext
  change AsymptoticRationalGroup.rationalMap (AsymptoticReconstructionBranch.branch
    (Nat.lcm N (q^2):ℚ) 0 (((i.val+1:ℕ):ℚ)/q)
      (by exact_mod_cast (Nat.lcm_pos hN (pow_pos (Fact.out : q.Prime).pos 2)).ne'))=_
  simp only [level_eq N q hq,Nat.cast_mul,Nat.cast_pow]
  rfl

variable (w : ℂ) {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ)

include hq in
theorem twist_eq_sums (x : ℍ) :
    twist N q hN (Fact.out : q.Prime).pos w hs hε t x=
      (∑ i,compact (translationBranch q i) hs hε t x)-
        w • ∑ i,compact (reflectedBranch N q hN i) hs hε t x := by
  have ht := Equiv.sum_comp (residueEquiv q) (fun a =>
    compact (AsymptoticRegularObservationRows.translation ((a.val:ℚ)/q)) hs hε t x)
  have hr := Equiv.sum_comp (residueEquiv q) (fun a =>
    compact (reflected N q hN (Fact.out : q.Prime).pos a.val) hs hε t x)
  have ht' : (∑ a : AsymptoticCertificateBranches.residues q,
      compact (AsymptoticRegularObservationRows.translation ((a.val:ℚ)/q)) hs hε t x)=
      ∑ i,compact (translationBranch q i) hs hε t x := by
    simpa only [residueEquiv_val,translationBranch,parameter] using ht.symm
  have hr' : (∑ a : AsymptoticCertificateBranches.residues q,
      compact (reflected N q hN (Fact.out : q.Prime).pos a.val) hs hε t x)=
      ∑ i,compact (reflectedBranch N q hN i) hs hε t x := by
    rw [← hr]
    apply Finset.sum_congr rfl
    intro i hi
    exact compact_eq_of_label _ _ (reflected_label_eq N q hN hq i) hs hε t x
  have hsm : (∑ a : AsymptoticCertificateBranches.residues q,
      (-w) • compact (reflected N q hN (Fact.out : q.Prime).pos a.val) hs hε t x)=
      (-w) • (∑ a : AsymptoticCertificateBranches.residues q,
        compact (reflected N q hN (Fact.out : q.Prime).pos a.val) hs hε t x) := by
    exact Finset.smul_sum.symm
  unfold twist family
  rw [Fintype.sum_sum_type]
  simp only [twistBranches,Sum.elim_inl,Sum.elim_inr,one_smul]
  rw [hsm,ht',hr']
  exact (congrArg (fun y => (∑ i,compact (translationBranch q i) hs hε t x)+y)
    (_root_.neg_smul w (∑ i,compact (reflectedBranch N q hN i) hs hε t x))).trans
      (sub_eq_add_neg _ _).symm

/-- The actual existing prime twist residual is the negative of the
mixed compact individual defects, with exactly the same input and output
spaces, cutoffs, weights and finite fold certificates. -/
theorem averaged_eq_negative_twist (x : ℍ) :
    mixed (primeLabels q) (fun i => AsymptoticFreshCompactDefects.row N q hN hq w hs hε t i x)=
      -twist N q hN (Fact.out : q.Prime).pos w hs hε t x := by
  rw [averaged_rows,twist_eq_sums N q hN hq]
  abel

#print axioms level_eq
#print axioms reflected_label_eq
#print axioms twist_eq_sums
#print axioms averaged_eq_negative_twist

end AsymptoticFreshEquation
