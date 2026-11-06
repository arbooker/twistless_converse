module

public import FurstenbergMinimalFiniteV1
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Baire.LocallyCompactRegular

set_option autoImplicit false

@[expose] public section

namespace FurstenbergDichotomy

open Set SpanningExceptionalSet SpanningProjectedWords FurstenbergZero FurstenbergMinimal
open IndependentBases Filter
open scoped Topology

/-- A continuous map with finite fibres preserves accumulation points. -/
theorem accPt_image_of_finite_fiber {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] {A : Set X} {x : X} {f : X → Y}
    (hf : Continuous f) (hfin : {y | f y = f x}.Finite)
    (hx : AccPt x (𝓟 A)) : AccPt (f x) (𝓟 (f '' A)) := by
  rw [accPt_iff_nhds] at hx ⊢
  intro U hU
  let F : Set X := {y | f y = f x} \ {x}
  have hF : IsClosed F := hfin.sdiff.isClosed
  have hxF : x ∈ Fᶜ := by simp [F]
  have hV : f ⁻¹' U ∩ Fᶜ ∈ 𝓝 x :=
    inter_mem (hf.continuousAt.preimage_mem_nhds hU) (hF.isOpen_compl.mem_nhds hxF)
  obtain ⟨y,⟨⟨hyU,hyF⟩,hyA⟩,hyx⟩ := hx _ hV
  refine ⟨f y,⟨hyU,mem_image_of_mem f hyA⟩,?_⟩
  intro he
  exact hyF ⟨he,by simpa using hyx⟩

/-- Multiplication by a positive integer has finite fibres on R/Z. -/
theorem finite_nsmul_fiber {n : ℕ} (hn : 0 < n) (x : Circle) :
    {y : Circle | n • y = n • x}.Finite := by
  have hfin := (AddCircle.finite_torsion 1 hn).preimage
    (f:=fun y : Circle => y-x) (fun _ _ _ _ h => (sub_left_inj).mp h)
  convert hfin using 1
  ext y
  simp only [mem_ofPred_eq, mem_preimage, nsmul_sub, sub_eq_zero]

/-- The derived set is again invariant. -/
theorem derived_invariant {q₁ q₂ : ℕ} (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {A : Set Circle} (hA : Invariant q₁ q₂ A) : Invariant q₁ q₂ (derivedSet A) := by
  intro n hn x hx
  have hh := accPt_image_of_finite_fiber (continuous_id.nsmul n)
    (finite_nsmul_fiber (tower_pos h₁ h₂ hn) x) hx
  apply (derivedSet_mono _ A ?_) hh
  rintro y ⟨z,hz,rfl⟩
  exact hA n hn z hz

/-- A finite covering by translates of a closed set gives nonempty interior. -/
theorem interior_nonempty_of_nsmul_full {A : Set Circle} (hA : IsClosed A)
    {d : ℕ} (hd : 0 < d) (hfull : (fun x : Circle => d • x) '' A = univ) :
    (interior A).Nonempty := by
  let K : Set Circle := {θ | d • θ = 0}
  have hK : K.Finite := AddCircle.finite_torsion 1 hd
  let : Finite K := hK.to_subtype
  let F : K → Set Circle := fun θ => {x | x+θ.val ∈ A}
  have hF : ∀ θ, IsClosed (F θ) := fun θ =>
    hA.preimage (continuous_id.add continuous_const)
  have hcover : ⋃ θ, F θ = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : d • x ∈ (fun z : Circle => d • z) '' A := hfull.symm ▸ mem_univ _
    obtain ⟨a,ha,he⟩ := hx
    have hk : a-x ∈ K := by change d • (a-x)=0; rw [nsmul_sub]; exact sub_eq_zero.mpr he
    exact mem_iUnion.mpr ⟨⟨a-x,hk⟩,by simpa [F] using ha⟩
  obtain ⟨θ,hθ⟩ := nonempty_interior_of_iUnion_of_closed hF hcover
  have hopen : IsOpen ((fun x : Circle => x+θ.val) '' interior (F θ)) :=
    (Homeomorph.addRight θ.val).isOpenMap _ isOpen_interior
  have hsub : (fun x : Circle => x+θ.val) '' interior (F θ) ⊆ A := by
    rintro y ⟨x,hx,rfl⟩
    exact (interior_subset (s:=F θ) hx : x+θ.val ∈ A)
  exact (hθ.image _).mono (interior_maximal hsub hopen)

/-- An expanding multiplier sends any open interval onto the circle after
sufficiently many iterations. -/
theorem full_of_interior {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁)
    {A : Set Circle} (hInv : Invariant q₁ q₂ A) (hA : (interior A).Nonempty) :
    A = univ := by
  let U : Set ℝ := ((↑) : ℝ → Circle) ⁻¹' interior A
  have hU : IsOpen U := isOpen_interior.preimage (AddCircle.continuous_mk' 1)
  have hUn : U.Nonempty := by
    obtain ⟨x,hx⟩ := hA
    obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective x
    exact ⟨u,hx⟩
  obtain ⟨a,b,hab,hI⟩ := hU.exists_Ioo_subset hUn
  let c := (a+b)/2
  have hac : a<c := by dsimp [c]; linarith
  have hcb : c<b := by dsimp [c]; linarith
  obtain ⟨j,hj⟩ := pow_unbounded_of_one_lt (1/(b-c))
    (show (1:ℝ)<q₁ by exact_mod_cast (show 1<q₁ by omega))
  let Q := q₁^j
  have hQ : 0 < (Q:ℝ) := by dsimp [Q]; positivity
  have hlen : 1 < (Q:ℝ)*(b-c) := by
    rw [← Nat.cast_pow] at hj
    exact (div_lt_iff₀ (sub_pos.mpr hcb)).mp hj
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ ((↑) : ℝ → Circle) '' Icc ((Q:ℝ)*c) ((Q:ℝ)*c+1) := by
    rw [AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨y,hy,rfl⟩ := hx
  have hyI : y/(Q:ℝ) ∈ Ioo a b := by
    constructor
    · apply (lt_div_iff₀ hQ).mpr
      have hc := mul_lt_mul_of_pos_left hac hQ
      nlinarith [hy.1]
    · apply (div_lt_iff₀ hQ).mpr
      nlinarith [hy.2]
  have hyA := interior_subset (hI hyI)
  have hh := hInv Q ⟨j,0,by simp [Q]⟩ _ hyA
  rw [← AddCircle.coe_nsmul,nsmul_eq_mul,mul_div_cancel₀ _ (ne_of_gt hQ)] at hh
  exact hh

/-- Furstenberg's classical finite-or-full theorem for two multiplicatively
independent integer multipliers on the circle. -/
theorem finite_or_full {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {A : Set Circle} (hA : IsClosed A)
    (hInv : Invariant q₁ q₂ A) : A.Finite ∨ A = univ := by
  classical
  by_cases hfin : A.Finite
  · exact Or.inl hfin
  right
  have hDA : Admissible q₁ q₂ (derivedSet A) := by
    refine ⟨isClosed_derivedSet A, ?_, derived_invariant (by omega) (by omega) hInv⟩
    obtain ⟨x,hx⟩ := (show A.Infinite from hfin).exists_accPt_principal
    exact ⟨x,hx⟩
  obtain ⟨M,hMD,hM⟩ := exists_minimal hDA
  have hMfin := minimal_finite h₁ h₂ hi hM
  obtain ⟨x,hx⟩ := hM.prop.2.1
  obtain ⟨d,hd,hxd⟩ := torsion_of_finite_invariant hMfin h₁
    (fun y hy => hM.prop.2.2 _ ⟨1,0,by simp⟩ y hy) hx
  let B : Set Circle := (fun y : Circle => d • y) '' A
  have hB : IsClosed B := (hA.isCompact.image (continuous_id.nsmul d)).isClosed
  have hBI : Invariant q₁ q₂ B := by
    rintro n hn y ⟨z,hz,rfl⟩
    exact ⟨n • z,hInv n hn z hz,by rw [smul_comm]⟩
  have hacc : AccPt (0:Circle) (𝓟 B) := by
    have hh := accPt_image_of_finite_fiber (continuous_id.nsmul d)
      (finite_nsmul_fiber hd x) (hMD hx)
    change AccPt (d • x) (𝓟 B) at hh
    rwa [hxd] at hh
  have hz : (0:Circle) ∈ closure (B \ {0}) :=
    mem_closure_iff_clusterPt.mpr (accPt_principal_iff_clusterPt.mp hacc)
  have hfull := full_of_zero_accumulation h₁ h₂ hi hB hBI hz
  exact full_of_interior h₁ hInv (interior_nonempty_of_nsmul_full hA hd hfull)

#print axioms accPt_image_of_finite_fiber
#print axioms full_of_interior
#print axioms finite_or_full

end FurstenbergDichotomy
