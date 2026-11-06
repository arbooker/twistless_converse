module
public import SmallLevelTwentySixGridContinuationV1
public import SmallLevelTwentySixGridFullMatricesV1
public import SmallLevelContinuationTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix Filter SmallLevelTwentySixUnitMMM
open scoped Topology

/-- The original grid and all original Taylor equations on one half-plane.
This records meromorphic continuation only, with no pole-removability claim. -/
structure PoleSystem (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) where
  B : ℝ
  G : ℂ→Fin 320→ℂ
  E : ℕ→ℂ→GridSource→ℂ
  meromorphic : ∀ i x,MeromorphicNFAt (fun z => G z i) x
  agreement : ∀ z,B<z.re → G z=actualGrid m f z
  error : ∀ (n : ℕ) (i : GridSource) (z : ℂ),B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z
  rows : ∀ n z,B<z.re →
    fullLeadingMatrix m f ε z *ᵥ actualGrid m f z=E n z+
      ∑ j∈Finset.range n,fullShiftMatrix m f ε j z *ᵥ actualGrid m f (z+((j:ℂ)+1))

/-- No continuation or Taylor-row hypotheses are assumed: both follow
from the original solution at level26. -/
theorem original_pole_system (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧ Nonempty (PoleSystem m f ε) := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  obtain ⟨B,E,_hF,hE,hrow⟩:=initial_system_of_laws m hm hf hε hlaw
  obtain ⟨BG,G,hG,hGF⟩:=original_grid_continuation m hm hf
  refine ⟨ε,hε,⟨{
    B := max B BG
    G := G
    E := fun n s i => E i n s
    meromorphic := hG
    agreement := ?_
    error := ?_
    rows := ?_
  }⟩⟩
  · intro z hz
    exact hGF z (lt_of_le_of_lt (le_max_right B BG) hz)
  · intro n i z hz
    apply hE n i z
    linarith [le_max_left B BG]
  · intro n s hs
    have hb : B<s.re:=lt_of_le_of_lt (le_max_left B BG) hs
    change fullLeadingMatrix m f ε s *ᵥ (fun j => gridVector (2*m) f s (support j))=
      (fun i => E i n s)+∑ j∈Finset.range n,
        fullShiftMatrix m f ε j s *ᵥ
          (fun i => gridVector (2*m) f (s+((j:ℂ)+1)) (support i))
    rw [fullLeadingMatrix_mulVec]
    simp_rw [fullShiftMatrix_mulVec]
    funext i
    simpa only [Pi.add_apply,Finset.sum_apply] using hrow n s hb i

/-- Every original row persists as a punctured identity wherever its
analytic remainder is defined; this includes arbitrary Taylor orders. -/
theorem PoleSystem.continued_rows {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (n : ℕ) (i : GridSource) (x : ℂ)
    (hx : S.B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j,fullLeadingMatrix m f ε z i j*S.G z j)=ᶠ[𝓝[≠] x]
      (fun z => S.E n z i+∑ a∈Finset.range n,
        ∑ j,fullShiftMatrix m f ε a z i j*S.G (z+((a:ℂ)+1)) j) :=
  SmallLevelContinuation.rectangular_continued_rows S.B (actualGrid m f) S.G
    (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε) S.E
    (fun i z => (S.meromorphic i z).meromorphicAt) S.agreement
    (fun z i j => fullLeadingMatrix_analytic m f ε i j z)
    (fun n z i j => fullShiftMatrix_analytic m f ε n i j z)
    S.error S.rows n i x hx

#print axioms original_pole_system
#print axioms PoleSystem.continued_rows
end SmallLevelTwentySixGrid
