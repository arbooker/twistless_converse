module

public import SmallLevelTwentyOneLargeGridRowSourcesV1
public import SmallLevelContinuationTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridModel
open Complex Set Matrix SmallLevelAdditive
open SmallLevelTwentyOneFiniteGrid

variable {κ : Type*}

def leadingLinear (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) :
    (Fin 210 → ℂ) →ₗ[ℂ] (κ → ℂ) where
  toFun v i := leading (rows i) m f ε s v
  map_add' v w := funext (fun i => leading_add (rows i) m f ε s v w)
  map_smul' c v := funext (fun i => leading_smul (rows i) m f ε s c v)

def shiftedLinear (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    (Fin 210 → ℂ) →ₗ[ℂ] (κ → ℂ) where
  toFun v i := shifted (rows i) m f ε n s v
  map_add' v w := funext (fun i => shifted_add (rows i) m f ε n s v w)
  map_smul' c v := funext (fun i => shifted_smul (rows i) m f ε n s c v)

def leadingMatrix (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) :
    Matrix κ (Fin 210) ℂ := (leadingLinear rows m f ε s).toMatrix'

def shiftedMatrix (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    Matrix κ (Fin 210) ℂ := (shiftedLinear rows m f ε n s).toMatrix'

theorem leadingMatrix_apply (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (i : κ) (j : Fin 210) :
    leadingMatrix rows m f ε s i j=leading (rows i) m f ε s (Pi.single j 1) :=
  LinearMap.toMatrix'_apply _ _ _

theorem shiftedMatrix_apply (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (i : κ) (j : Fin 210) :
    shiftedMatrix rows m f ε n s i j=shifted (rows i) m f ε n s (Pi.single j 1) :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_mulVec (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ)
    (v : Fin 210 → ℂ) :
    leadingMatrix rows m f ε s *ᵥ v=(fun i => leading (rows i) m f ε s v) :=
  LinearMap.toMatrix'_mulVec _ _

theorem shiftedMatrix_mulVec (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (v : Fin 210 → ℂ) :
    shiftedMatrix rows m f ε n s *ᵥ v=(fun i => shifted (rows i) m f ε n s v) :=
  LinearMap.toMatrix'_mulVec _ _

theorem leadingMatrix_analytic (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (s : ℂ) (i : κ) (j : Fin 210) :
    AnalyticAt ℂ (fun z => leadingMatrix rows m f ε z i j) s := by
  simp only [leadingMatrix_apply]
  exact leading_analytic (rows i) m f ε _ s

theorem shiftedMatrix_analytic (rows : κ → Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (i : κ) (j : Fin 210) :
    AnalyticAt ℂ (fun z => shiftedMatrix rows m f ε n z i j) s := by
  simp only [shiftedMatrix_apply]
  exact shifted_analytic (rows i) m f ε n _ s

/-- Finite actual row families have one common half-plane schedule,
including the old-grid meromorphic source terms. -/
theorem original_finite_matrix_sources [Fintype κ] (rows : κ → Row)
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i s, MeromorphicNFAt (fun z => G z i) s)
    (hGF : ∀ s, BG<s.re → G s=SmallLevelTwentyOne.gridVector (2*m) f s)
    (hGreg : ∀ i s, s≠((2*m:ℕ):ℂ) → AnalyticAt ℂ (fun z => G z i) s) :
    ∃ (B : ℝ) (H : ℕ → ℂ → κ → ℂ),
      (∀ i s, B<s.re → AnalyticAt ℂ (fun z => gridVector 210 (2*m) f z i) s) ∧
      (∀ (M : ℕ) i s, B-((M:ℝ)+1)<s.re → MeromorphicAt (fun z => H M z i) s) ∧
      (∀ (M : ℕ) i s, B-((M:ℝ)+1)<s.re → s≠((2*m:ℕ):ℂ) →
        AnalyticAt ℂ (fun z => H M z i) s) ∧
      ∀ (M : ℕ) s, B<s.re →
        leadingMatrix rows m f ε s *ᵥ gridVector 210 (2*m) f s=
          H M s+∑ n∈Finset.range M,
            shiftedMatrix rows m f ε n s *ᵥ gridVector 210 (2*m) f (s+((n:ℂ)+1)) := by
  classical
  have hr (i : κ) := original_row_sources hm hf ε hε hlaw BG G hG hGF hGreg (rows i)
  choose bounds errors he ha hrow using hr
  obtain ⟨B,hB⟩ := (Set.finite_range bounds).bddAbove
  obtain ⟨C,hC⟩ := original_common_halfplane hf
  have hb (i : κ) : bounds i≤max B C := (hB (Set.mem_range_self i)).trans (le_max_left _ _)
  refine ⟨max B C,fun M s i => errors i M s,?_,?_,?_,?_⟩
  · intro i s hs
    exact (hC ((i:ℕ)/210) s (lt_of_le_of_lt (le_max_right _ _) hs)).1
  · intro M i s hs
    exact he i M s (by linarith [hb i])
  · intro M i s hs hk
    exact ha i M s (by linarith [hb i]) hk
  · intro M s hs
    rw [leadingMatrix_mulVec]
    simp only [shiftedMatrix_mulVec]
    funext i
    simpa only [Pi.add_apply,Finset.sum_apply] using hrow i M s (lt_of_le_of_lt (hb i) hs)

#print axioms original_finite_matrix_sources
end SmallLevelTwentyOneLargeGridModel
