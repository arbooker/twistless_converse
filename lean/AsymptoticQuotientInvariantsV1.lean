module

public import AsymptoticOvergroupIsometryV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticNestedQuotients

open ContinuousLinearMap
open scoped lp

variable {G : Type*} [Group G]

def stabilizer (F : G → ℂ) : Subgroup G where
  carrier := {a | ∀ g,F (a*g)=F g}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb g
    rw [mul_assoc,ha,hb]
  inv_mem' := by
    intro a ha g
    simpa only [mul_inv_cancel_left] using (ha (a⁻¹*g)).symm

theorem invariant_sup_iff (F : G → ℂ) (J K : Subgroup G) :
    (∀ a : ↥(J⊔K),∀ g,F (a.val*g)=F g) ↔
      (∀ a : J,∀ g,F (a.val*g)=F g) ∧ (∀ a : K,∀ g,F (a.val*g)=F g) := by
  have he (L : Subgroup G) : (∀ a : L,∀ g,F (a.val*g)=F g) ↔ L≤stabilizer F := by
    exact ⟨fun h a ha => h ⟨a,ha⟩,fun h a => h a.property⟩
  rw [he,he,he,sup_le_iff]

theorem factors_iff_invariant {H J : Subgroup G} (h : H≤J) (v : Classes H → ℂ) :
    (∃ f : Classes J → ℂ,∀ q,v q=f (forget h q)) ↔
      ∀ a : J,∀ g,v (classOf H (a.val*g))=v (classOf H g) := by
  constructor
  · rintro ⟨f,hf⟩ a g
    rw [hf,hf,forget_classOf,forget_classOf,classOf_mul]
  · intro hv
    have he : ∀ a b,QuotientGroup.rightRel J a b → v (classOf H a)=v (classOf H b) := by
      intro a b hab
      let j : J := ⟨b*a⁻¹,QuotientGroup.rightRel_apply.mp hab⟩
      simpa only [j,inv_mul_cancel_right] using (hv j a).symm
    refine ⟨Quotient.lift (fun g => v (classOf H g)) he,?_⟩
    intro q
    induction q using Quotient.inductionOn with
    | h g => rfl

/-- An invariant counting-space vector must vanish if each larger coset
contains infinitely many small cosets. No closed-range premise is used. -/
theorem invariant_zero_of_infinite {H J : Subgroup G} (h : H≤J)
    [Infinite (J ⧸ H.subgroupOf J)] (v : ℓ²(Classes H,ℂ))
    (hv : ∀ a : J,∀ g,v (classOf H (a.val*g))=v (classOf H g)) : v=0 := by
  obtain ⟨f,hf⟩ := (factors_iff_invariant h v).mpr hv
  apply lp.ext
  funext q
  change v q=0
  by_contra hq
  have hs : Summable (fun r : Classes H => ‖v r‖^2) := by
    simpa using (lp.hasSum_norm (p:=2) (by norm_num) v).summable
  have hsub := hs.subtype (fun r => forget h r=forget h q)
  have hc : Summable (fun _ : {r : Classes H // forget h r=forget h q} => ‖v q‖^2) := by
    apply hsub.congr
    intro r
    change ‖v r.val‖^2=‖v q‖^2
    rw [hf r.val,hf q,r.property]
  let : Finite {r : Classes H // forget h r=forget h q} :=
    Finite.of_summable_const (sq_pos_of_pos (norm_pos_iff.mpr hq)) hc
  exact Finite.false (Finite.of_equiv {r : Classes H // forget h r=forget h q}
    (fibreEquiv h (forget h q)))

/-- The closed invariant space is defined for every overgroup, including
the infinite-index case needed for the meet of the two old directions. -/
noncomputable def invariantSpace (H J : Subgroup G) : Submodule ℂ ℓ²(Classes H,ℂ) :=
  ⨅ a : J,⨅ g : G,((lp.evalCLM ℂ (fun _ : Classes H => ℂ) 2 (classOf H (a.val*g)))-
    (lp.evalCLM ℂ (fun _ : Classes H => ℂ) 2 (classOf H g))).ker

theorem invariantSpace_mem (H J : Subgroup G) (v : ℓ²(Classes H,ℂ)) :
    v∈invariantSpace H J ↔ ∀ a : J,∀ g,v (classOf H (a.val*g))=v (classOf H g) := by
  simp only [invariantSpace,Submodule.mem_iInf,LinearMap.mem_ker]
  change (∀ a : J,∀ g,v (classOf H (a.val*g))-v (classOf H g)=0) ↔ _
  simp only [sub_eq_zero]

theorem invariantSpace_sup (H J K : Subgroup G) :
    invariantSpace H (J⊔K)=invariantSpace H J⊓invariantSpace H K := by
  ext v
  simp only [invariantSpace_mem,Submodule.mem_inf]
  exact invariant_sup_iff (fun g => v (classOf H g)) J K

theorem invariantSpace_eq_space {H J : Subgroup G} (h : H≤J)
    [Finite (J ⧸ H.subgroupOf J)] : invariantSpace H J=space h := by
  ext v
  exact (invariantSpace_mem H J v).trans (isometry_range_iff h v).symm

theorem invariantSpace_eq_bot {H J : Subgroup G} (h : H≤J)
    [Infinite (J ⧸ H.subgroupOf J)] : invariantSpace H J=⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  exact invariant_zero_of_infinite h v ((invariantSpace_mem H J v).mp hv)

#print axioms invariant_sup_iff
#print axioms factors_iff_invariant
#print axioms invariant_zero_of_infinite
#print axioms invariantSpace_mem
#print axioms invariantSpace_sup
#print axioms invariantSpace_eq_space
#print axioms invariantSpace_eq_bot

end AsymptoticNestedQuotients
