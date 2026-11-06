module

public import SpanningCRTExponentsV1
public import SpanningAdditionCoordinatesV1

@[expose] public section

namespace SpanningAdditionFailure

open scoped BigOperators
open SpanningAdditionCoordinates SpanningSlicedAddition SpanningTraceAlgebra

def NegativeInverse (B c:ℕ) (t:ℤ) : Prop := (B:ℤ)∣(c:ℤ)*t+1

theorem negative_inverse_exists {B c:ℕ} (hB:0<B) (hc:Nat.Coprime c B) :
    ∃u:ℕ,NegativeInverse B c u := by
  obtain ⟨s,z,hs⟩ := inverse_exists hc
  let u := (SpanningCyclicCoordinates.residue hB (-s)).val
  have hu : (u:ℤ)=(-s)%(B:ℤ) := residue_cast hB (-s)
  have he := Int.mul_ediv_add_emod (-s) (B:ℤ)
  refine ⟨u,z-(c:ℤ)*((-s)/(B:ℤ)),?_⟩
  rw [hu]
  nlinarith [congrArg (fun x:ℤ => (c:ℤ)*x) he,hs]

theorem negative_inverse_coprime {B c u:ℕ} (hu:NegativeInverse B c u) :
    Nat.Coprime u B := by
  have hgu : ((Nat.gcd u B:ℕ):ℤ)∣(u:ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left u B)
  have hgB : ((Nat.gcd u B:ℕ):ℤ)∣(B:ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right u B)
  have hg : ((Nat.gcd u B:ℕ):ℤ)∣(1:ℤ) := by
    have he := dvd_sub (dvd_trans hgB hu) (dvd_mul_of_dvd_right hgu (c:ℤ))
    simpa using he
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hg)

theorem negative_inverse_unique {B c:ℕ} {t u:ℤ} (hc:Nat.Coprime c B)
    (ht:NegativeInverse B c t) (hu:NegativeInverse B c u) : (B:ℤ)∣u-t := by
  have hd : (B:ℤ)∣(c:ℤ)*(u-t) := by
    convert dvd_sub hu ht using 1
    ring
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hd (by
    simpa only [Int.gcd_natCast_natCast] using hc.symm)

theorem common_step {I:Type*} [Fintype I] [DecidableEq I]
    (c:I→ℕ) {B u:ℕ} (hu:NegativeInverse B (∏i,c i) u)
    (i:I) {t:ℤ} (hc:Nat.Coprime (c i) B) (ht:NegativeInverse B (c i) t) :
    (B:ℤ)∣(u*SpanningCRTExponents.weight c i:ℕ)-t := by
  apply negative_inverse_unique hc ht
  unfold NegativeInverse at hu ⊢
  convert hu using 1
  push_cast
  rw [mul_left_comm,←Nat.cast_mul,SpanningCRTExponents.mul_weight]
  push_cast
  ring

def ShiftFailure {K:Type*} [Field K] (B c:ℕ) (V:Submodule K (ℤ→K)) : Prop :=
  ∃t:ℤ,NegativeInverse B c t ∧ ∃v:Fin c→V,
    (∃r,v r≠0) ∧ ∀n:ℤ,(∑r,(v r:ℤ→K) (n+t*r.val))=0

theorem failure_of_not_injective {K:Type*} [Field K] {B c:ℕ}
    (hcpos:0<c) (hc:Nat.Coprime c B) (V:Submodule K (ℤ→K))
    (hcyc:∀v∈V,Cyclic B v) (hbad:¬AdditionInjective c B (V:Set (ℤ→K))) :
    ShiftFailure B c V := by
  classical
  unfold AdditionInjective at hbad
  push Not at hbad
  obtain ⟨w,hw,hzero,r,hr,hnz⟩ := hbad
  obtain ⟨s,z,hs⟩ := inverse_exists hc
  have hinv : inverseAddition c s w=0 := by
    rw [←addition_eq_inverse hcpos hc hs w (fun r hr => hcyc _ (hw r hr))]
    exact hzero
  refine ⟨-s,?_,(fun r => ⟨w r.val,hw r.val r.isLt⟩),?_,?_⟩
  · refine ⟨z,?_⟩
    nlinarith [hs]
  · refine ⟨⟨r,hr⟩,?_⟩
    intro he
    exact hnz (congrArg Subtype.val he)
  · intro n
    have he := congrFun hinv ((c:ℤ)*n)
    change (∑r∈Finset.range c,w r (s*((c:ℤ)*n-r)))=0 at he
    rw [←Fin.sum_univ_eq_sum_range] at he
    change (∑r:Fin c,w r.val (n+(-s)*r.val))=0
    convert he using 1
    apply Finset.sum_congr rfl
    intro r _
    apply cyclic_eq_of_dvd (hcyc _ (hw r.val r.isLt))
    refine ⟨-z*n,?_⟩
    nlinarith [congrArg (fun x:ℤ => x*n) hs]

#print axioms failure_of_not_injective
#print axioms common_step

end SpanningAdditionFailure
