module
public import QuantitativeArithmeticUniversalPoleVectorV1
public import QuantitativeArithmeticAnalyticGermTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLeadingCoordinateDetection
open QuantitativeArithmeticUniversalPoleVector QuantitativeArithmeticAnalyticGerm

theorem coordinate_zero_of_germ {ι : Type*} [Fintype ι]
    {G : ℂ→ι→ℂ} {x : ℂ} {v : ι→ℂ} (hv : IsLeadingVector G x v)
    (j : ι) (hg : HasAnalyticGerm (fun z => G z j) x) : v j=0 := by
  classical
  obtain ⟨H,hH,he⟩ := hg
  have h := hv.2 (fun _ i => if i=j then 1 else 0) H
    (fun _ => analyticAt_const) hH (by simpa using he)
  simpa using h

/-- If specified coordinates detect the kernel of analytic leading rows,
some specified coordinate must carry every genuine pole of the system. -/
theorem pole_in_detecting_coordinates {ι ρ κ : Type*} [Fintype ι]
    (G : ℂ→ι→ℂ) (x : ℂ) (σ : κ→ι) (A : ℂ→ρ→ι→ℂ)
    (hG : ∀ i,MeromorphicNFAt (fun z => G z i) x)
    (hpole : ∃ i,meromorphicOrderAt (fun z => G z i) x<0)
    (hA : ∀ r i,AnalyticAt ℂ (fun z => A z r i) x)
    (hrows : ∀ r,HasAnalyticGerm (fun z => ∑ i,A z r i*G z i) x)
    (hker : ∀ v : ι→ℂ,(∀ r,∑ i,A x r i*v i=0) → (∀ j,v (σ j)=0) → v=0) :
    ∃ j,meromorphicOrderAt (fun z => G z (σ j)) x<0 := by
  classical
  obtain ⟨v,hv⟩ := exists_leading_vector G x (fun i => (hG i).meromorphicAt) hpole
  have hvr : ∀ r,∑ i,A x r i*v i=0 := by
    intro r
    obtain ⟨H,hH,he⟩ := hrows r
    exact hv.2 (fun z i => A z r i) H (hA r) hH he
  by_contra! hregular
  apply hv.1
  apply hker v hvr
  intro j
  apply coordinate_zero_of_germ hv (σ j)
  exact HasAnalyticGerm.of_analytic ((hG (σ j)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hregular j))

#print axioms coordinate_zero_of_germ
#print axioms pole_in_detecting_coordinates
end SmallLevelLeadingCoordinateDetection
