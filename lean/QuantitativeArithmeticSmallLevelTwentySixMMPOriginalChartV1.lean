module
public import QuantitativeArithmeticSmallLevelTwentySixMMPOriginalKernelV1
public import QuantitativeArithmeticSmallLevelTwentySixMMPPrimitiveTheoryV4
public import SmallLevelTwentySixMMPPariTheoryV4
public import SmallLevelLaurentProjectiveChartV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPOriginalChart
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open SmallLevelTwentySixGermDAG (replayVector)
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive

def augmentedRows {ρ : Type*} (rows : ρ → Poly) : Fin 5 ⊕ ρ → Poly :=
  Sum.elim (fun i => primitiveRows ⟨i.val,lt_trans i.isLt (by decide)⟩) rows

theorem first_five_support (i : Fin 5) :
    ∀ t∈primitiveRows ⟨i.val,lt_trans i.isLt (by decide)⟩, t.2.1=0 ∨ t.2.1=1 := by
  fin_cases i <;> decide +kernel

/-- Add the five checked small equations before taking the common leading
vector. Thus every additional supported analytic syzygy shares one legitimate
first-chart parameter, rather than separately chosen leading vectors. -/
theorem original_first_chart {ρ : Type*} {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0)
    (rows : ρ → Poly)
    (hsupport : ∀ i t,t∈rows i → t.2.1=0 ∨ t.2.1=1)
    (hgerms : ∀ i,HasAnalyticGerm (fun z => eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) (rows i)) s) :
    ∃ θ : ℂ,∀ i,eval
      (u*parameter 2 m s) ((parameter 3 m s)^2)
      (v*parameter 13 m s) ((parameter 5 m s)^2)
      (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s)
      1 (fun j => if j=0 then 1 else θ) (augmentedRows rows i)=0 := by
  have hsupport' : ∀ i t,t∈augmentedRows rows i → t.2.1=0 ∨ t.2.1=1 := by
    intro i
    cases i with
    | inl j => exact first_five_support j
    | inr j => exact hsupport j
  have hgerms' : ∀ i,HasAnalyticGerm (fun z => eval
      (u*parameter 2 m z) ((parameter 3 m z)^2)
      (v*parameter 13 m z) ((parameter 5 m z)^2)
      (badParameter f 3*parameter 3 m z) (badParameter f 5*parameter 5 m z)
      1 (replayVector m S.G z) (augmentedRows rows i)) s := by
    intro i
    cases i with
    | inl j =>
      simpa only [augmentedRows, Sum.elim_inl] using
        signed_original_primitive_germs S s u v hu hv hshift hs hs1 hη hs2 hs13
          ⟨j.val, lt_trans j.isLt (by decide)⟩
    | inr j => exact hgerms j
  obtain ⟨w,hw,hrows⟩ := QuantitativeArithmeticSmallLevelTwentySixMMPOriginalKernel.original_leading_kernel
    S T s u v hu hv hshift hη hs2 hs13 hpole (augmentedRows rows) hsupport' hgerms'
  have hw01 : w 0≠0 ∨ w 1≠0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  have hw0 := SmallLevelTwentySixMMPPari.first_coordinate_ne_zero
    (u*parameter 2 m s) ((parameter 3 m s)^2)
    (v*parameter 13 m s) ((parameter 5 m s)^2)
    (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s)
    (fun j => if j=0 then w 0 else w 1) (by simpa using hw01)
    (fun i => hrows (Sum.inl i))
  apply SmallLevelLaurentProjectiveChart.normalize_first _ _ _ _ _ _ _ (augmentedRows rows) w
    (by simpa using hw0) hrows

#print axioms first_five_support
#print axioms original_first_chart
end QuantitativeArithmeticSmallLevelTwentySixMMPOriginalChart
