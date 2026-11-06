module

public import QuantitativeSpectralExceptionalFundamentalReductionV1
public import QuantitativeSpectralExceptionalGeometryCoverV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalGeometry

open Matrix UpperHalfPlane Set AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRegularBranchFamily QuantitativeSpectralExceptionalReducedRows
open QuantitativeSpectralObservability QuantitativeSpectralFiniteReduction
open scoped MatrixGroups Modular Pointwise

/-- A single finite congruence family converts the wide sampled cover
into the literal fundamental compact cover, at the same height cutoff. -/
theorem finite_wide_fundamental_reduction (N : ℕ) (hN : 0 < N) :
    ∃ F : Finset SL(2,ℤ), (∀ g ∈ F, g ∈ CongruenceSubgroup.Gamma0 N) ∧
      ∀ H : ℝ, 4 ≤ H → ∀ z ∈ wideCompactCover N H,
        ∃ g ∈ F, integralLabel g • z ∈ fundamentalCompact N H := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let Q := SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N
  let := Fintype.ofFinite Q
  obtain ⟨F,hF⟩ := finite_wide_box_fd_reduction
  let r (p : Q × ↥F) : Q := QuotientGroup.mk (p.2.val*p.1.out)
  let g (p : Q × ↥F) : SL(2,ℤ) := (r p).out⁻¹*(p.2.val*p.1.out)
  have hg (p) : g p ∈ CongruenceSubgroup.Gamma0 N :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (r p))
  refine ⟨Finset.univ.image g,?_,?_⟩
  · intro a ha
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ha
    exact hg p
  · intro H hH z hz
    obtain ⟨q,v,hv,rfl⟩ := mem_iUnion.mp hz
    obtain ⟨a,ha,hav,hai⟩ := hF H hH v hv
    let p : Q × ↥F := (q,⟨a,ha⟩)
    refine ⟨g p,Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩,?_⟩
    apply mem_iUnion.mpr
    refine ⟨r p,a • v,⟨hav,hai⟩,?_⟩
    simp only [← map_inv,integralLabel_action,g,p,mul_smul,smul_inv_smul]

theorem finite_wide_fundamental_words (N : ℕ) (hN : 0 < N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N) :
    ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ H : ℝ, 4 ≤ H → ∀ z ∈ wideCompactCover N H,
        ∃ l ∈ W, integralLabel l.prod • z ∈ fundamentalCompact N H := by
  classical
  obtain ⟨F,hF,hr⟩ := finite_wide_fundamental_reduction N hN
  choose w hw using fun a : ↥F => congruence_word N S hS a.val (hF a.val a.property)
  refine ⟨Finset.univ.image w,?_,?_⟩
  · intro l hl
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hl
    exact (hw a).2
  · intro H hH z hz
    obtain ⟨a,ha,haz⟩ := hr H hH z hz
    refine ⟨w ⟨a,ha⟩,Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,rfl⟩,?_⟩
    simpa only [(hw ⟨a,ha⟩).1] using haz

/-- Every retained rational row has fixed word reducers directly into the
literal fundamental-domain sampler. The final wide-to-fundamental step
introduces no additional height loss. -/
theorem finite_retained_fundamental_words {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 0 < N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ)) = CongruenceSubgroup.Gamma0 N)
    (b : ι → Branch) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ W : Finset (List SL(2,ℤ)),
      (∀ l ∈ W, ∀ a ∈ l, a ∈ S ∨ a⁻¹ ∈ S) ∧
      ∀ H : ℝ, B ≤ H → ∀ z ∈ openCover N \ wideTailCover N (H/C), ∀ i,
        ∃ l ∈ W, (integralLabel l.prod * label (b i)) • z ∈ fundamentalCompact N H := by
  classical
  obtain ⟨C,B,hC,hB,W,hW,hr⟩ := finite_retained_family_words N hN S hS b
  obtain ⟨V,hV,hv⟩ := finite_wide_fundamental_words N hN S hS
  let f : List SL(2,ℤ) × List SL(2,ℤ) → List SL(2,ℤ) := fun p => p.2 ++ p.1
  refine ⟨C,max B 4,hC,hB.trans_le (le_max_left _ _),(W.product V).image f,?_,?_⟩
  · intro l hl a ha
    obtain ⟨⟨u,v⟩,hpair,rfl⟩ := Finset.mem_image.mp hl
    rcases List.mem_append.mp ha with ha | ha
    · exact hV v (Finset.mem_product.mp hpair).2 a ha
    · exact hW u (Finset.mem_product.mp hpair).1 a ha
  · intro H hH z hz i
    obtain ⟨l,hl,hlz⟩ := hr H ((le_max_left _ _).trans hH) z hz i
    obtain ⟨m,hm,hmz⟩ := hv H ((le_max_right _ _).trans hH)
      ((integralLabel l.prod*label (b i)) • z) hlz
    refine ⟨m++l,Finset.mem_image.mpr ⟨(l,m),Finset.mem_product.mpr ⟨hl,hm⟩,rfl⟩,?_⟩
    simpa only [List.prod_append,map_mul,mul_smul] using hmz

#print axioms finite_wide_fundamental_words
#print axioms finite_retained_fundamental_words

end QuantitativeSpectralExceptionalGeometry
