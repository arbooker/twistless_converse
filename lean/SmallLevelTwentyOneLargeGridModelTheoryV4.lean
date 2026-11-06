module

public import SmallLevelContinuedMeromorphicSourcesV1
public import SmallLevelPoleGridTheoryV4
public import SmallLevelTwentyOneLargeGridLinksTheoryV4

/-! Consolidated chapter: SmallLevelTwentyOneLargeGridModel. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneLargeGridContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridModel
open Complex Set Filter Matrix SmallLevelAdditive
open SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneLargeGridLinks
open scoped Topology

/-- A continued210-grid together with its actual finite Taylor system. -/
structure ContinuedGrid (f : ℕ → ℂ) (ε : ℂ) where
  bound : ℝ
  values : ℂ → Fin 210 → ℂ
  errors : ℕ → ℂ → Fin 210 → ℂ
  normal : ∀ i s, MeromorphicNFAt (fun z => values z i) s
  agree : ∀ s, bound<s.re → values s=gridVector 210 2 f s
  right_analytic : ∀ i s, bound<s.re → AnalyticAt ℂ (fun z => values z i) s
  source_meromorphic : ∀ (n : ℕ) i s, bound-((n:ℝ)+1)<s.re → MeromorphicAt (fun z => errors n z i) s
  source_analytic : ∀ (n : ℕ) i s, bound-((n:ℝ)+1)<s.re → s≠2 → AnalyticAt ℂ (fun z => errors n z i) s
  relation : ∀ (n : ℕ) i s, bound-((n:ℝ)+1)<s.re →
    (fun z => ∑ j, leadingMatrix selectedData 1 f ε z i j*values z j)=ᶠ[𝓝[≠] s]
      (fun z => errors n z i+∑ a∈Finset.range n,
        ∑ j, shiftedMatrix selectedData 1 f ε a z i j*values (z+((a:ℂ)+1)) j)

/-- Actual continuation of the enlarged grid in the exceptional weight2
case. There is no assumption on the Hecke5 eigenvalue. -/
theorem original_continued_grid {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 2 f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 2 f ε)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i s, MeromorphicNFAt (fun z => G z i) s)
    (hGF : ∀ s, BG<s.re → G s=SmallLevelTwentyOne.gridVector 2 f s)
    (hGreg : ∀ i s, s≠2 → AnalyticAt ℂ (fun z => G z i) s) :
    Nonempty (ContinuedGrid f ε) := by
  obtain ⟨B,H,hF,hH,hHA,hrow⟩ := original_finite_matrix_sources selectedData
    (by decide : 0<1) hf ε hε hlaw BG G hG hGF hGreg
  have hd := actual_leading_exists_nonsingular f ε hE hu hv ha
  obtain ⟨V,hV,hVF⟩ := SmallLevelContinuation.closed_system_meromorphic_source
    B (gridVector 210 2 f) (leadingMatrix selectedData 1 f ε)
    (shiftedMatrix selectedData 1 f ε) H hF
    (leadingMatrix_analytic selectedData 1 f ε) hd
    (shiftedMatrix_analytic selectedData 1 f ε) hH (by
      intro n s hs i
      simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using
        congrFun (hrow n s hs) i)
  refine ⟨{
    bound := B
    values := V
    errors := H
    normal := hV
    agree := hVF
    right_analytic := ?_
    source_meromorphic := hH
    source_analytic := hHA
    relation := ?_ }⟩
  · intro i s hs
    apply (hF i s hs).congr
    have hn : ∀ᶠ z in 𝓝 s, B<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hn] with z hz
    exact (congrFun (hVF z hz) i).symm
  · exact SmallLevelContinuation.continued_meromorphic_rows B
      (gridVector 210 2 f) V (leadingMatrix selectedData 1 f ε)
      (shiftedMatrix selectedData 1 f ε) H (fun i s => (hV i s).meromorphicAt) hVF
      (leadingMatrix_analytic selectedData 1 f ε)
      (shiftedMatrix_analytic selectedData 1 f ε) hH hrow

#print axioms original_continued_grid
end SmallLevelTwentyOneLargeGridModel
end
end

/-! ## SmallLevelTwentyOneLargeGridPoleExclusionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridModel
open Complex Matrix SmallLevelTwentyOneLargeGridLinks
open QuantitativeArithmeticUniversalPoleVector

/-- At every possible quadratic-twist denominator zero, all coordinates of
an actual continued210-grid are analytic. The rightmost pole argument allows
arbitrary orders and all positive integer shifts. -/
theorem ContinuedGrid.analytic_at_denominator_root {f : ℕ → ℂ} {ε : ℂ}
    (S : ContinuedGrid f ε)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) {s : ℂ}
    (hs : SmallLevelTwentyOneChiFive.denominator 2 f s=0) (i : Fin 210) :
    AnalyticAt ℂ (fun z => S.values z i) s := by
  apply (S.normal i s).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  obtain ⟨n,hn,hshift⟩ := SmallLevelPoleGrid.rightmost_pole
    (fun j z => S.values z j) ⟨i,hp⟩ S.bound S.right_analytic
  obtain ⟨v,hvlead⟩ := exists_leading_vector S.values (s+n)
    (fun j => (S.normal j _).meromorphicAt) hn
  have him := (SmallLevelTwentyOneChiFive.exceptional_root_line ha hs).2
  have hx : s+(n:ℂ)≠2 := by
    intro he
    exact him (by simpa using congrArg Complex.im he)
  have hker : leadingMatrix selectedData 1 f ε (s+n) *ᵥ v=0 := by
    funext j
    exact hvlead.taylor_at S.normal hshift S.bound
      (fun z => leadingMatrix selectedData 1 f ε z j)
      (fun a z => shiftedMatrix selectedData 1 f ε a z j)
      (fun a z => S.errors a z j)
      (fun l => leadingMatrix_analytic selectedData 1 f ε (s+n) j l)
      (fun a l => shiftedMatrix_analytic selectedData 1 f ε a (s+n) j l)
      (fun a h => S.source_analytic a j (s+n) h hx)
      (fun a h => S.relation a j (s+n) h)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (actual_leading_shift_nonsingular f ε hE hu hv ha hs n)))
  exact hvlead.1 (hinj (hker.trans (Matrix.mulVec_zero _).symm))

#print axioms ContinuedGrid.analytic_at_denominator_root
end SmallLevelTwentyOneLargeGridModel
end
end
