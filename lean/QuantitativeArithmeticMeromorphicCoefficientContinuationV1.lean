module

public import SmallLevelContinuationTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticMeromorphicCoefficientContinuation
open SmallLevelContinuation

open Complex Filter Set Matrix
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source-closed continuation with meromorphic shifted-row coefficients.
This permits staged rational reconstruction without expanding or globally
clearing every elimination denominator. The leading matrix remains analytic. -/
theorem closed_system_meromorphic_coefficients (B : ℝ) (F : ℂ → ι → ℂ)
    (A : ℂ → Matrix ι ι ℂ) (C : ℕ → ℂ → Matrix ι ι ℂ)
    (H : ℕ → ℂ → ι → ℂ)
    (hF : ∀ i z, B<z.re → AnalyticAt ℂ (fun w => F w i) z)
    (hA : ∀ x i j, AnalyticAt ℂ (fun z => A z i j) x)
    (hd : ∃ y, (A y).det≠0)
    (hC : ∀ m x i j, MeromorphicAt (fun z => C m z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → MeromorphicAt (fun w => H n w i) z)
    (hrow : ∀ n z, B<z.re → ∀ i,
      ∑ j, A z i j*F z j=H n z i+
        ∑ m ∈ Finset.range n, ∑ j, C m z i j*F (z+((m:ℂ)+1)) j) :
    ∃ G : ℂ → ι → ℂ, (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=F z := by
  have stages : ∀ n : ℕ, ∃ V : ℂ → ι → ℂ,
      (∀ i, MeromorphicNFOn (fun z => V z i) {z : ℂ | B-(n:ℝ)<z.re}) ∧
      ∀ z, B<z.re → V z=F z := by
    intro n
    induction n with
    | zero =>
      refine ⟨F,?_,fun _ _ => rfl⟩
      intro i z hz
      exact (hF i z (by simpa using hz)).meromorphicNFAt
    | succ n ih =>
      obtain ⟨V,hV,heV⟩ := ih
      let R : ℂ → ι → ℂ := fun z i => H n z i+
        ∑ m ∈ Finset.range n, ∑ j, C m z i j*V (z+((m:ℂ)+1)) j
      have hR (i : ι) : MeromorphicOn (fun z => R z i)
          {z : ℂ | B-((n:ℝ)+1)<z.re} := by
        intro x hx
        apply (hH n i x hx).add
        apply MeromorphicAt.fun_sum
        intro m _
        apply MeromorphicAt.fun_sum
        intro j _
        apply (hC m x i j).mul
        have hshift : B-(n:ℝ)<(x+((m:ℂ)+1)).re := by
          simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
          change B-((n:ℝ)+1)<x.re at hx
          linarith [Nat.cast_nonneg (α:=ℝ) m]
        exact ((hV j hshift).meromorphicAt).comp_analyticAt
          (g := fun z : ℂ => z+((m:ℂ)+1)) (by fun_prop)
      have he : ∀ z, B<z.re → A z *ᵥ V z=R z := by
        intro z hz
        funext i
        change (∑ j, A z i j*V z j)=_
        rw [heV z hz,hrow n z hz i]
        change H n z i+_=H n z i+_
        congr 1
        apply Finset.sum_congr rfl
        intro m _
        have hs : B<(z+((m:ℂ)+1)).re := by
          simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
          linarith [Nat.cast_nonneg (α:=ℝ) m]
        rw [heV _ hs]
      obtain ⟨W,hW,heW,_⟩ := matrix_halfplane_extension
        (B-((n:ℝ)+1)) (B-(n:ℝ)) B (by linarith) A R V hA hd hR hV he
      refine ⟨W,?_,?_⟩
      · simpa only [Nat.cast_succ] using hW
      · intro z hz
        exact (heW z (by linarith [Nat.cast_nonneg (α:=ℝ) n])).trans (heV z hz)
  have hcoord (i : ι) : ∃ G : ℂ → ℂ, (∀ x, MeromorphicNFAt G x) ∧
      EqOn G (fun z => F z i) {z : ℂ | B<z.re} := by
    apply halfplane_glue B (fun z => F z i)
    intro n
    obtain ⟨V,hV,heV⟩ := stages n
    exact ⟨fun z => V z i,hV i,fun z hz => congrFun (heV z hz) i⟩
  choose G hG heG using hcoord
  refine ⟨fun z i => G i z,hG,?_⟩
  intro z hz
  funext i
  exact heG i hz

#print axioms closed_system_meromorphic_coefficients

end QuantitativeArithmeticMeromorphicCoefficientContinuation
