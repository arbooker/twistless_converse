module

public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic

set_option autoImplicit false

@[expose] public section

namespace SpanningExceptionalSet

abbrev Circle := AddCircle (1:ℝ)

/-- Points whose two-base semigroup orbit never enters the periodic arc. -/
def exceptional (Q q₁ q₂ : ℕ) (arc : Set Circle) : Set Circle :=
  {x | ∀ a b : ℕ, (Q*q₁^a*q₂^b) • x ∉ arc}

theorem closed (Q q₁ q₂ : ℕ) {arc : Set Circle} (h : IsOpen arc) :
    IsClosed (exceptional Q q₁ q₂ arc) := by
  have he : exceptional Q q₁ q₂ arc =
      ⋂ a : ℕ, ⋂ b : ℕ, (fun x : Circle => (Q*q₁^a*q₂^b) • x) ⁻¹' arcᶜ := by
    ext x
    simp [exceptional]
  rw [he]
  exact isClosed_iInter (fun a => isClosed_iInter (fun b =>
    h.isClosed_compl.preimage (continuous_id.nsmul (Q*q₁^a*q₂^b))))

theorem invariant_first (Q q₁ q₂ : ℕ) (arc : Set Circle) {x : Circle}
    (hx : x ∈ exceptional Q q₁ q₂ arc) : q₁ • x ∈ exceptional Q q₁ q₂ arc := by
  intro a b
  simpa only [smul_smul, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hx (a+1) b

theorem invariant_second (Q q₁ q₂ : ℕ) (arc : Set Circle) {x : Circle}
    (hx : x ∈ exceptional Q q₁ q₂ arc) : q₂ • x ∈ exceptional Q q₁ q₂ arc := by
  intro a b
  simpa only [smul_smul, pow_succ, mul_assoc] using hx a (b+1)

theorem zero_mem (Q q₁ q₂ : ℕ) {arc : Set Circle} (hzero : 0 ∉ arc) :
    0 ∈ exceptional Q q₁ q₂ arc := by
  intro a b
  simpa using hzero

theorem proper (Q q₁ q₂ : ℕ) {arc : Set Circle} {x : Circle}
    (hx : Q • x ∈ arc) : exceptional Q q₁ q₂ arc ≠ Set.univ := by
  intro he
  have hmem : x ∈ exceptional Q q₁ q₂ arc := he.symm ▸ Set.mem_univ x
  have h := hmem 0 0
  simp only [pow_zero, mul_one] at h
  exact h hx

/-- A finite set invariant under multiplication by q≥2 consists of torsion
points. On R/Z these are precisely the rational points. This lemma does not
assume or assert Furstenberg's finite-or-full dichotomy. -/
theorem torsion_of_finite_invariant {G : Type*} [AddCommGroup G]
    {E : Set G} (hE : E.Finite) {q : ℕ} (hq : 2≤q)
    (hmap : ∀ x∈E, q • x ∈ E) {x : G} (hx : x∈E) :
    ∃ n : ℕ, 0<n ∧ n • x=0 := by
  classical
  let : Fintype E := hE.fintype
  have horbit : ∀ j : ℕ, q^j • x ∈ E := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih => simpa only [pow_succ', mul_smul] using hmap _ ih
  obtain ⟨i,j,hij,he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨q^n • x, horbit n⟩ : E))
  have he' : q^i • x=q^j • x := congrArg Subtype.val he
  have hordered : ∀ i j : ℕ, i<j → q^i • x=q^j • x → ∃ n : ℕ, 0<n ∧ n • x=0 := by
    intro i j hij he
    have hp : q^i<q^j := pow_lt_pow_right₀ (by omega) hij
    refine ⟨q^j-q^i, Nat.sub_pos_of_lt hp, ?_⟩
    apply add_right_cancel (b:=q^i • x)
    rw [zero_add, ← add_nsmul, Nat.sub_add_cancel hp.le, he]
  rcases lt_or_gt_of_ne hij with hij|hji
  · exact hordered i j hij he'
  · exact hordered j i hji he'.symm

#print axioms closed
#print axioms torsion_of_finite_invariant

end SpanningExceptionalSet
