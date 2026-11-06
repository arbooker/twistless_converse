module

public import SmallLevelUniversalRegularTailFirstShiftV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelFiniteShift
open Complex Matrix Filter
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- Restrict a continued rectangular system to a finite row family and
apply an analytic scalar left syzygy. Removable tail germs suffice. -/
theorem selected_regular_first_shift {ι κ ρ : Type*} [Fintype ι] [Fintype ρ]
    (rows : ρ→κ) (B : ℝ) (G : ℂ→ι→ℂ)
    (A : ℂ→Matrix κ ι ℂ) (C : ℕ→ℂ→Matrix κ ι ℂ) (H : ℕ→ℂ→κ→ℂ)
    (hC : ∀ n x i j, AnalyticAt ℂ (fun z => C n z i j) x)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,A z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ a∈Finset.range n,∑ j,C a z i j*G (z+((a:ℂ)+1)) j))
    (x : ℂ) (v : ι→ℂ) (hv : IsLeadingVector G x v)
    (htail : ∀ a : ℕ, 1≤a → ∀ i j, ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-1) ∧
      (fun z => C a z i j*G (z+((a:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-1)] R)
    (K : ℂ→ρ→ℂ) (hK : ∀ z i,AnalyticAt ℂ (fun w => K w i) z)
    (hKA : ∀ z (w : ι→ℂ),∑ i,K z i*(∑ j,A z (rows i) j*w j)=0) :
    ∑ i,K (x-1) i*(∑ j,C 0 (x-1) (rows i) j*v j)=0 := by
  classical
  let A' : ℂ→Matrix ρ ι ℂ:=fun z i => A z (rows i)
  let C' : ℕ→ℂ→Matrix ρ ι ℂ:=fun n z i => C n z (rows i)
  let L : ℂ→Matrix Unit ρ ℂ:=fun z _ i => K z i
  have hLA (z : ℂ) : L z*A' z=0 := by
    ext r j
    have hh:=hKA z (Pi.single j 1)
    simpa [Matrix.mul_apply,L,A',Pi.single_apply] using hh
  have h:=IsLeadingVector.regular_tail_first_shift B G A' C'
    (fun n z i => H n z (rows i)) L
    (fun n z i j => hC n z (rows i) j)
    (fun n i z hz => hH n (rows i) z hz)
    (fun z _ i => hK z i) hLA
    (fun n i z hz => hrow n (rows i) z hz) x v hv
    (fun a ha i j => htail a ha (rows i) j)
  have hh : (L (x-1) *ᵥ (C' 0 (x-1) *ᵥ v)) ()=0 := by
    rw [Matrix.mulVec_mulVec]
    exact congrFun h ()
  exact hh

#print axioms selected_regular_first_shift
end SmallLevelFiniteShift
