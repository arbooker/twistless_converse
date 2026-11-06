module

public import QuantitativeEulerDiamondRecoveryV1
public import QuantitativeEulerDiamondRegionV1
public import AsymptoticDecodedObservationsV1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerDiamondDecode

open UpperHalfPlane AsymptoticCongruenceLabels AsymptoticRegularBranchFamily
open AsymptoticFreshMatrices AsymptoticFreshAveraging AsymptoticFreshCompactDefects
open AsymptoticRegularObservationRows AsymptoticOrbitDecode
open QuantitativeArithmeticDiamondLabels
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCertificateBranches (residues)
open scoped Classical

/-- The original q=1 observation is exactly the Fricke residual in the
same group algebra used by diamond recovery. -/
theorem compactAction_untwisted (N : ℕ) (hN : 0<N) (w : ℂ)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (1-w • symbol (frickeLabel N hN))=
      twist N 1 hN Nat.zero_lt_one w hs hε t x := by
  let z : residues 1 := ⟨0,by simp [residues]⟩
  have hz (i : residues 1) : i=z := by
    apply Subtype.ext
    have hi := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
    change i.val=0
    omega
  let : Unique (residues 1) := ⟨⟨z⟩,hz⟩
  unfold twist family
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,twistBranches,Sum.elim_inl,Sum.elim_inr,one_smul]
  rw [hz (default : residues 1)]
  simp only [z,Nat.cast_zero,zero_div]
  have hi : translation 0=identityBranch := rfl
  rw [hi]
  have he := compactAction_branch hs hε t x (reflected N 1 hN Nat.zero_lt_one 0)
  rw [reflected_one_label] at he
  have hid := compactAction_branch hs hε t x identityBranch
  rw [identityBranch_label,map_one] at hid
  rw [map_sub,map_smul,hid,he]
  rw [sub_eq_add_neg]
  congr 1
  exact (neg_smul w (compact (reflected N 1 hN Nat.zero_lt_one 0) hs hε t x)).symm

variable (N q : ℕ) [Fact q.Prime] (hN : 0<N) (hq : ¬q∣N)

theorem canonical_residual_identity (w : ℂ) (hw : w*w=1) (j : Fin (q-1)) :
    symbol (integralLabel (swappedCanonical N q hq j))-1=
      (-w) • ((1-w • symbol (frickeLabel N hN))+
        (w • symbol (defectLabel N q hN hq j)-1))*symbol ((defectLabel N q hN hq j)⁻¹) := by
  have hsum : (1-w • symbol (frickeLabel N hN))+
      (w • symbol (defectLabel N q hN hq j)-1)=
      w • (symbol (defectLabel N q hN hq j)-symbol (frickeLabel N hN)) := by
    rw [smul_sub]
    abel
  have hgi : symbol (defectLabel N q hN hq j)*symbol ((defectLabel N q hN hq j)⁻¹)=1 := by
    rw [←map_mul,mul_inv_cancel,map_one]
  rw [←fricke_defectLabel_inv N q hN hq j,map_mul,hsum,smul_smul,neg_mul,hw,
    neg_one_smul,neg_mul,sub_mul,hgi]
  abel

/-- Removing the actual untwisted observation produces the canonical
Gamma0 defect, with the exact swapped-residue convention. No Fricke
invariance of the vector is assumed. -/
theorem compact_canonical_recovery (w : ℂ) (hw : w*w=1) (j : Fin (q-1))
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    let b := symbolBranch ((defectLabel N q hN hq j)⁻¹)
    let hu := branchImage_compact b hs
    AsymptoticCongruenceDefect.operator (swappedCanonical N q hq j) hs hε t x=
      (-w) • (branchTransport b hs hε t x).comp
        (twist N 1 hN Nat.zero_lt_one w hu hε t x+
          (w • compact (matrixBranch N q hN hq j) hu hε t x-compact identityBranch hu hε t x)) := by
  let b := symbolBranch ((defectLabel N q hN hq j)⁻¹)
  let hu := branchImage_compact b hs
  have hm := compactAction_branch hu hε t x (matrixBranch N q hN hq j)
  rw [matrixBranch_label] at hm
  have hi := compactAction_branch hu hε t x identityBranch
  rw [identityBranch_label,map_one] at hi
  have hsum : compactAction hu hε t x
      ((1-w • symbol (frickeLabel N hN))+
        (w • symbol (defectLabel N q hN hq j)-1))=
      twist N 1 hN Nat.zero_lt_one w hu hε t x+
        (w • compact (matrixBranch N q hN hq j) hu hε t x-compact identityBranch hu hε t x) := by
    rw [map_add,compactAction_untwisted N hN w hu hε t x,map_sub,map_smul,hm,hi]
  have ht := compactAction_mul_symbol b hs hε t x
    ((1-w • symbol (frickeLabel N hN))+(w • symbol (defectLabel N q hN hq j)-1))
  have hb : AsymptoticRationalBranches.ofMatrix b.matrix b.positive=(defectLabel N q hN hq j)⁻¹ := symbolBranch_label _
  rw [hb,hsum] at ht
  have he := congrArg (compactAction hs hε t x) (canonical_residual_identity N q hN hq w hw j)
  rw [compactAction_congruence,smul_mul_assoc,map_smul] at he
  exact he.trans (congrArg (fun T : Space →L[ℂ] Space => (-w) • T) ht)

#print axioms compactAction_untwisted
#print axioms canonical_residual_identity
#print axioms compact_canonical_recovery
end QuantitativeEulerDiamondDecode
