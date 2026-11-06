module

public import AsymptoticOrbitDecodeV1
public import AsymptoticFreshCongruenceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticOrbitDecode

open AsymptoticRationalBranches AsymptoticRegularBranchFamily
open AsymptoticRegularObservationRows AsymptoticFreshCompactDefects AsymptoticFreshMatrices
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactBranch (cap)
open AsymptoticCertificateBranches (residues)
open UpperHalfPlane ContinuousLinearMap
open scoped Classical

variable {ι : Type*} [Fintype ι]

theorem family_decode (b : ι → Branch) (c : ι → ℂ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space) (a : AsymptoticRationalGroup.Group) :
    family b c hs hε t x f a=
      if a • x∈s then (cap ε t (a • x):ℂ)*
        ∑ i,c i*decode ε t x f (ofMatrix (b i).matrix (b i).positive*a) else 0 := by
  unfold family
  change (lp.evalCLM ℂ (fun _ : AsymptoticRationalGroup.Group => ℂ) 2 a)
    ((∑ i,c i • compact (b i) hs hε t x) f)=_
  rw [_root_.sum_apply,map_sum]
  change (∑ i,c i*(compact (b i) hs hε t x f a))=_
  simp_rw [compact_decode]
  by_cases ha : a • x∈s
  · simp only [ite_eq_left ha]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp only [ite_eq_right ha,mul_zero,Finset.sum_const_zero]

/-- All compact members of any finite rational branch family are
equivalent to their pointwise decoded relation on every group coordinate. -/
theorem all_compact_family_zero_iff (b : ι → Branch) (c : ι → ℂ)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space) :
    (∀ s : Set ℍ,∀ hs : IsCompact s,family b c hs hε t x f=0) ↔
    ∀ a : AsymptoticRationalGroup.Group,
      ∑ i,c i*decode ε t x f (ofMatrix (b i).matrix (b i).positive*a)=0 := by
  constructor
  · intro h a
    have he := congrArg (fun v : Space => v a) (h {a • x} isCompact_singleton)
    rw [family_decode,ite_eq_left (Set.mem_singleton (a • x))] at he
    exact (mul_eq_zero.mp he).resolve_left (cap_ne_zero hε t (a • x))
  · intro h s hs
    apply lp.ext
    funext a
    rw [family_decode,h a,mul_zero]
    simp

omit [Fintype ι] in
theorem reflected_one_label (N : ℕ) (hN : 0<N) :
    ofMatrix (reflected N 1 hN Nat.zero_lt_one 0).matrix
      (reflected N 1 hN Nat.zero_lt_one 0).positive=frickeLabel N hN := by
  unfold reflected frickeLabel
  simp only [Nat.one_pow,Nat.lcm_one_right,Nat.cast_zero,zero_div]

omit [Fintype ι] in
/-- The untwisted equation already present among the original rows
is exactly the Fricke law on decoded coordinates. -/
theorem all_compact_untwisted_zero_iff (N : ℕ) (hN : 0<N) (w : ℂ)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) (f : Space) :
    (∀ s : Set ℍ,∀ hs : IsCompact s,twist N 1 hN Nat.zero_lt_one w hs hε t x f=0) ↔
    ∀ a : AsymptoticRationalGroup.Group,
      w*decode ε t x f (frickeLabel N hN*a)=decode ε t x f a := by
  let z : residues 1 := ⟨0,by simp [residues]⟩
  have hz (i : residues 1) : i=z := by
    apply Subtype.ext
    have hi := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
    change i.val=0
    omega
  let : Unique (residues 1) := ⟨⟨z⟩,hz⟩
  change (∀ s : Set ℍ,∀ hs : IsCompact s,
    family (twistBranches N 1 hN Nat.zero_lt_one) (Sum.elim (fun _ => 1) (fun _ => -w)) hs hε t x f=0) ↔ _
  rw [all_compact_family_zero_iff]
  apply forall_congr'
  intro a
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,twistBranches,Sum.elim_inl,Sum.elim_inr,one_mul]
  rw [hz (default : residues 1)]
  simp only [z,Nat.cast_zero,zero_div]
  change decode ε t x f (ofMatrix identityBranch.matrix identityBranch.positive*a)+
    (-w)*decode ε t x f
      (ofMatrix (reflected N 1 hN Nat.zero_lt_one 0).matrix
        (reflected N 1 hN Nat.zero_lt_one 0).positive*a)=0 ↔ _
  rw [identityBranch_label,one_mul,reflected_one_label]
  constructor <;> intro h <;> linear_combination -h

#print axioms family_decode
#print axioms all_compact_family_zero_iff
#print axioms reflected_one_label
#print axioms all_compact_untwisted_zero_iff

end AsymptoticOrbitDecode
