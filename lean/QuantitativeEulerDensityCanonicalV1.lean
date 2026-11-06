module

public import QuantitativeEulerDensityDecodeV1
public import QuantitativeArithmeticDiamondLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix QuantitativeArithmetic QuantitativeHolomorphic AsymptoticFreshMatrices
open AsymptoticFreshResidues QuantitativeArithmeticDiamondLabels
open scoped MatrixGroups Classical

/-- The determinant congruence uniquely identifies the actual residue
permutation when both entries lie in the original nonzero residue range. -/
theorem canonical_eq_observed (N q : ℕ) [Fact q.Prime] (hq : ¬q∣N)
    (a b c : ℤ) (ha : 1≤a ∧ a<q) (hb : 1≤b ∧ b<q)
    (hdet : (q : ℤ)*c=(N : ℤ)*a*b+1) :
    ∃ j : Fin (q-1), canonical N q a b c hdet=swappedCanonical N q hq j := by
  let j : Fin (q-1) := ⟨(a-1).toNat,by omega⟩
  have hja : a=(j.val : ℤ)+1 := by dsimp [j]; omega
  have hr : (N : ZMod q)*(a : ZMod q)*(b : ZMod q)= -1 := by
    have hd := congrArg (fun z : ℤ => (z : ZMod q)) hdet
    push_cast at hd
    simp only [ZMod.natCast_self,zero_mul] at hd
    linear_combination -hd
  have hn : (N : ZMod q)≠0 := (levelUnit q N hq).ne_zero
  have haj : (a : ZMod q)≠0 := by
    have hi := (indexUnit q j).ne_zero
    simpa only [indexUnit_val,hja,Int.cast_add,Int.cast_natCast,Int.cast_one,
      Nat.cast_add,Nat.cast_one] using hi
  have hp := permutation_relation q N hq j
  have hp' : (N : ZMod q)*(a : ZMod q)*
      (((permutation q N hq j).val : ℤ)+1 : ℤ)= -1 := by
    simpa only [hja,Int.cast_add,Int.cast_natCast,Int.cast_one,mul_right_comm] using hp
  have hbc := mul_left_cancel₀ (mul_ne_zero hn haj) (hr.trans hp'.symm)
  have hbj : b=((permutation q N hq j).val : ℤ)+1 := by
    have he := (ZMod.intCast_eq_intCast_iff' b ((permutation q N hq j).val+1) q).mp hbc
    rw [Int.emod_eq_of_lt (by omega) hb.2,
      Int.emod_eq_of_lt (by omega) (by have hi := (permutation q N hq j).isLt; omega)] at he
    exact he
  have hcj : c=quotient q N hq j := by
    have he := quotient_relation q N hq j
    have hq0 : (q : ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    apply mul_left_cancel₀ hq0
    rw [hdet,he,hja,hbj]
    ring
  refine ⟨j,?_⟩
  apply Subtype.ext
  change canonicalEntries N q a b c=
    canonicalEntries N q (j.val+1) ((permutation q N hq j).val+1) (quotient q N hq j)
  rw [hja,hbj,hcj]

/-- Every prepared fresh-prime certificate is literally one of the
swapped canonical matrices in the original observation family. The finite
index is derived from the certificate ranges and determinant identity. -/
theorem PolynomialPrimeCertificate.canonical_eq_observed
    {Q B c D d : ℤ} {N q : ℕ} [Fact q.Prime] {K : ℝ}
    (cert : PolynomialPrimeCertificate Q B N c D d q K) (hq : ¬q∣N) :
    ∃ j : Fin (q-1),
      (⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
        upperUnipotent cert.l,cert.canonical_det⟩ : SL(2,ℤ))=
        swappedCanonical N q hq j := by
  have hd : (q : ℤ)*(cert.D'+(N : ℤ)*d*cert.l+(N : ℤ)*cert.β)=
      (N : ℤ)*(q-d)*cert.β+1 := by
    simpa only [add_comm] using cert.canonical_bottom_eq
  obtain ⟨j,hj⟩ := QuantitativeEulerDensityGenerators.canonical_eq_observed N q hq (q-d) cert.β
    (cert.D'+(N : ℤ)*d*cert.l+(N : ℤ)*cert.β) cert.alpha_range cert.beta_range hd
  refine ⟨j,?_⟩
  have he : (⟨lowerUnipotent N (-1)*certificateMatrix q cert.B' N d cert.D'*
        upperUnipotent cert.l,cert.canonical_det⟩ : SL(2,ℤ))=
      canonical N q (q-d) cert.β (cert.D'+(N : ℤ)*d*cert.l+(N : ℤ)*cert.β) hd :=
    Subtype.ext cert.canonical_eq
  exact he.trans hj

#print axioms canonical_eq_observed
#print axioms PolynomialPrimeCertificate.canonical_eq_observed
end QuantitativeEulerDensityGenerators
