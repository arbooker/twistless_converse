module

public import FurstenbergZeroV1
public import Mathlib.Order.Zorn

set_option autoImplicit false

@[expose] public section

namespace FurstenbergMinimal

open Set SpanningExceptionalSet SpanningProjectedWords FurstenbergZero
open IndependentBases

/-- The closed nonempty invariant sets, ordered by inclusion. -/
def Admissible (q₁ q₂ : ℕ) (A : Set Circle) : Prop :=
  IsClosed A ∧ A.Nonempty ∧ Invariant q₁ q₂ A

/-- Compactness supplies a minimal invariant subset of any closed nonempty one. -/
theorem exists_minimal {q₁ q₂ : ℕ} {A : Set Circle} (hA : Admissible q₁ q₂ A) :
    ∃ M, M ⊆ A ∧ Minimal (Admissible q₁ q₂) M := by
  apply zorn_superset_nonempty {M | Admissible q₁ q₂ M} _ A hA
  intro c hcs hc hcn
  let : Std.Refl (flip (fun x y : Set Circle => x ⊆ y)) := ⟨fun _ => Subset.rfl⟩
  refine ⟨⋂₀ c, ⟨isClosed_sInter (fun t ht => (hcs ht).1), ?_, ?_⟩,
    fun s hs => sInter_subset_of_mem hs⟩
  · convert @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      _ _ _ hcn.coe_sort ((↑) : c → Set Circle) ?_ ?_ ?_ ?_ using 1
    · exact sInter_eq_iInter
    · exact DirectedOn.directed_val hc.symm.directedOn
    · exact fun i => (hcs i.prop).2.1
    · exact fun i => (hcs i.prop).1.isCompact
    · exact fun i => (hcs i.prop).1
  · intro n hn x hx
    exact mem_sInter.mpr (fun t ht => (hcs ht).2.2 n hn x (mem_sInter.mp hx t ht))

/-- Every orbit in a minimal invariant set is dense in that set. -/
theorem orbit_dense {q₁ q₂ : ℕ} {M : Set Circle}
    (hM : Minimal (Admissible q₁ q₂) M) {x : Circle} (hx : x ∈ M) :
    closure {y | ∃ n, Tower q₁ q₂ n ∧ n • x = y} = M := by
  let O : Set Circle := {y | ∃ n, Tower q₁ q₂ n ∧ n • x = y}
  have hO : O ⊆ M := by
    rintro y ⟨n, hn, rfl⟩
    exact hM.prop.2.2 n hn x hx
  apply hM.eq_of_subset _ (hM.prop.1.closure_subset_iff.mpr hO)
  refine ⟨isClosed_closure, ?_, ?_⟩
  · exact ⟨x, subset_closure ⟨1, ⟨0, 0, by simp⟩, one_nsmul x⟩⟩
  · intro n hn y hy
    have hcont : Continuous (fun z : Circle => n • z) := continuous_id.nsmul n
    apply closure_mono (show (fun z : Circle => n • z) '' O ⊆ O from ?_)
      (mem_closure_image hcont.continuousAt hy)
    rintro z ⟨w, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨n*m, tower_mul hn hm, by rw [mul_smul]⟩

/-- A minimal invariant set containing a torsion point is finite. -/
theorem finite_of_torsion {q₁ q₂ : ℕ} {M : Set Circle}
    (hM : Minimal (Admissible q₁ q₂) M) {x : Circle} (hx : x ∈ M)
    {d : ℕ} (hd : 0 < d) (hxd : d • x = 0) : M.Finite := by
  let T : Set Circle := {y | d • y = 0}
  have hT : T.Finite := AddCircle.finite_torsion 1 hd
  have he : M ∩ T = M := by
    apply hM.eq_of_subset _ inter_subset_left
    refine ⟨hM.prop.1.inter hT.isClosed, ⟨x,hx,hxd⟩, ?_⟩
    intro n hn y hy
    refine ⟨hM.prop.2.2 n hn y hy.1, ?_⟩
    change d • (n • y) = 0
    rw [smul_comm, hy.2, smul_zero]
  rw [← he]
  exact hT.subset inter_subset_right

/-- Difference sets of infinite closed invariant sets fill the circle. -/
theorem difference_full {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {A : Set Circle} (hA : IsClosed A)
    (hInv : Invariant q₁ q₂ A) (hInf : A.Infinite) :
    {z | ∃ x ∈ A, ∃ y ∈ A, x-y=z} = univ := by
  let D : Set Circle := {z | ∃ x ∈ A, ∃ y ∈ A, x-y=z}
  have hD : IsClosed D := by
    have he : D = (fun p : Circle × Circle => p.1-p.2) '' (A ×ˢ A) := by
      ext z
      simp only [D, mem_ofPred_eq, mem_image, mem_prod]
      constructor
      · rintro ⟨x,hx,y,hy,he⟩
        exact ⟨(x,y),⟨hx,hy⟩,he⟩
      · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,he⟩
        exact ⟨x,hx,y,hy,he⟩
    rw [he]
    exact ((hA.isCompact.prod hA.isCompact).image
      (continuous_fst.sub continuous_snd)).isClosed
  have hDI : Invariant q₁ q₂ D := by
    rintro n hn z ⟨x,hx,y,hy,rfl⟩
    exact ⟨n • x,hInv n hn x hx,n • y,hInv n hn y hy,(nsmul_sub _ _ _).symm⟩
  obtain ⟨x,hx,hacc⟩ := hInf.exists_accPt_of_subset_isCompact hA.isCompact Subset.rfl
  have hcl : x ∈ closure (A \ {x}) :=
    mem_closure_iff_clusterPt.mpr (accPt_principal_iff_clusterPt.mp hacc)
  have h0 : (0:Circle) ∈ closure (D \ {0}) := by
    have hc : Continuous (fun y : Circle => y-x) := continuous_id.sub continuous_const
    have hh := mem_closure_image hc.continuousAt hcl
    simp only [sub_self] at hh
    apply closure_mono _ hh
    rintro z ⟨y,hy,rfl⟩
    refine ⟨⟨y,hy.1,x,hx,rfl⟩, ?_⟩
    simpa only [mem_singleton_iff, sub_eq_zero] using hy.2
  exact full_of_zero_accumulation h₁ h₂ hi hD hDI h0

/-- A common fixed point of the generators is fixed by their semigroup. -/
theorem tower_fixed {q₁ q₂ n : ℕ} {θ : Circle}
    (h₁ : q₁ • θ = θ) (h₂ : q₂ • θ = θ) (hn : Tower q₁ q₂ n) : n • θ = θ := by
  have hp : ∀ q : ℕ, q • θ = θ → ∀ a : ℕ, q^a • θ = θ := by
    intro q hq a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ, mul_smul, hq, ih]
  obtain ⟨a,b,rfl⟩ := hn
  rw [mul_smul, hp q₂ h₂ b, hp q₁ h₁ a]

/-- Overlapping translates of a minimal invariant set coincide. This orbit
form is enough to propagate the rational grids in Furstenberg's argument. -/
theorem translate_mem {q₁ q₂ : ℕ} {M : Set Circle}
    (hM : Minimal (Admissible q₁ q₂) M) {θ μ β x : Circle}
    (h₁ : q₁ • θ = θ) (h₂ : q₂ • θ = θ)
    (hμ : μ ∈ M) (hβ : β ∈ M) (hθ : μ-β=θ) (hx : x ∈ M) : x-θ ∈ M := by
  have hcl : x ∈ closure {y | ∃ n, Tower q₁ q₂ n ∧ n • μ = y} := by
    rwa [orbit_dense hM hμ]
  have hc : Continuous (fun y : Circle => y-θ) := continuous_id.sub continuous_const
  apply hM.prop.1.closure_subset (closure_mono ?_ (mem_closure_image hc.continuousAt hcl))
  rintro z ⟨y,⟨n,hn,rfl⟩,rfl⟩
  have he : n • μ - θ = n • β := by
    rw [← tower_fixed h₁ h₂ hn, ← nsmul_sub, ← hθ]
    simp
  change n • μ - θ ∈ M
  rw [he]
  exact hM.prop.2.2 n hn β hβ

/-- For a minimal infinite set, every common fixed translation is a period. -/
theorem translate_mem_of_infinite {q₁ q₂ : ℕ} (h₁ : 2 ≤ q₁) (h₂ : 2 ≤ q₂)
    (hi : Independent q₁ q₂) {M : Set Circle}
    (hM : Minimal (Admissible q₁ q₂) M) (hInf : M.Infinite)
    {θ x : Circle} (hθ₁ : q₁ • θ = θ) (hθ₂ : q₂ • θ = θ) (hx : x ∈ M) : x-θ ∈ M := by
  have hD := difference_full h₁ h₂ hi hM.prop.1 hM.prop.2.2 hInf
  have ht : θ ∈ {z | ∃ μ ∈ M, ∃ β ∈ M, μ-β=z} := hD.symm ▸ mem_univ θ
  obtain ⟨μ,hμ,β,hβ,he⟩ := ht
  exact translate_mem hM hθ₁ hθ₂ hμ hβ he hx

#print axioms exists_minimal
#print axioms orbit_dense
#print axioms finite_of_torsion
#print axioms difference_full
#print axioms translate_mem_of_infinite

end FurstenbergMinimal
