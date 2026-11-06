module

public import SmallLevelPoleGridTheoryV4
public import SmallLevelContinuationTheoryV4

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticUniversalPoleVector
open Complex Filter Set
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- The universal principal-part condition at one pole. It ensures that
adding more certified analytic rows never changes the chosen pole vector. -/
def IsLeadingVector (G : ℂ → ι → ℂ) (x : ℂ) (v : ι → ℂ) : Prop :=
  v≠0 ∧ ∀ (A : ℂ → ι → ℂ) (H : ℂ → ℂ),
    (∀ j, AnalyticAt ℂ (fun z => A z j) x) → AnalyticAt ℂ H x →
    ((fun z => ∑ j, A z j*G z j)=ᶠ[𝓝[≠] x] H) → ∑ j, A x j*v j=0

/-- One nonzero Laurent vector simultaneously satisfies every analytic row
with analytic right hand side, not just a preselected finite subsystem. -/
theorem exists_leading_vector (G : ℂ → ι → ℂ) (x : ℂ)
    (hG : ∀ j, MeromorphicAt (fun z => G z j) x)
    (hpole : ∃ j, meromorphicOrderAt (fun z => G z j) x<0) :
    ∃ v, IsLeadingVector G x v := by
  classical
  let R := {r : (ℂ → ι → ℂ)×(ℂ → ℂ) //
    (∀ j, AnalyticAt ℂ (fun z => r.1 z j) x) ∧ AnalyticAt ℂ r.2 x ∧
      (fun z => ∑ j, r.1 z j*G z j)=ᶠ[𝓝[≠] x] r.2}
  obtain ⟨v,hv,hrows⟩ := SmallLevelPoleGrid.leading_kernel (ρ:=R) hG hpole
    (fun z r j => r.val.1 z j) (fun r => r.val.2)
    (fun r => r.property.1) (fun r => r.property.2.1) (fun r => r.property.2.2)
  refine ⟨v,hv,?_⟩
  intro A H hA hH he
  exact hrows ⟨(A,H),hA,hH,he⟩

/-- Apply the SAME universal vector to any continued Taylor row at a
rightmost pole. The remainder bound may depend on the row. -/
theorem IsLeadingVector.taylor {G : ℂ → ι → ℂ} {x : ℂ} {v : ι → ℂ}
    (hv : IsLeadingVector G x v)
    (hG : ∀ j z, MeromorphicNFAt (fun s => G s j) z)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (B : ℝ) (A : ℂ → ι → ℂ) (C : ℕ → ℂ → ι → ℂ) (H : ℕ → ℂ → ℂ)
    (hA : ∀ j, AnalyticAt ℂ (fun z => A z j) x)
    (hC : ∀ n j, AnalyticAt ℂ (fun z => C n z j) x)
    (hH : ∀ (n : ℕ) z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (H n) z)
    (hrow : ∀ n : ℕ, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j, A z j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z+∑ a∈Finset.range n, ∑ j, C a z j*G (z+((a:ℂ)+1)) j)) :
    ∑ j, A x j*v j=0 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (B-x.re)
  have hx : B-((n:ℝ)+1)<x.re := by linarith
  apply hv.2 A _ hA _ (hrow n hx)
  apply (hH n x hx).add
  apply Finset.analyticAt_fun_sum
  intro a _
  apply Finset.analyticAt_fun_sum
  intro j _
  have hs : AnalyticAt ℂ (fun z => G z j) (x+((a:ℂ)+1)) := by
    apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    simpa only [Nat.cast_add,Nat.cast_one] using hshift (a+1) (by omega) j
  exact (hC a j).mul (hs.comp (f:=fun z : ℂ => z+((a:ℂ)+1))
    (analyticAt_id.add analyticAt_const))

#print axioms exists_leading_vector
#print axioms IsLeadingVector.taylor
end QuantitativeArithmeticUniversalPoleVector
