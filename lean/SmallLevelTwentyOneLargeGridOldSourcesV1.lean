module

public import SmallLevelTwentyOneLargeGridRowModelV1
public import SmallLevelTwentyOneKnownWordsTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridModel
open Complex Set Filter SmallLevelTaylor SmallLevelAdditive
open SmallLevelTwentyOneFiniteGrid

/-- Embedding the old42-grid as every fifth210-grid coordinate. -/
theorem embedded_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (j : ℤ) :
    gridVector 210 k f s (gridIndex 210 (by decide) (5*j))=
      SmallLevelTwentyOne.gridVector k f s (SmallLevelTwentyOne.gridIndex j) := by
  rw [gridVector_index,SmallLevelTwentyOne.gridVector_index]
  unfold grid
  congr 1
  push_cast
  ring

def oldFiveSource (m : ℕ) (f : ℕ → ℂ) (G : ℂ → Fin 42 → ℂ) (j : ℤ) (s : ℂ) : ℂ :=
  ((Real.sqrt 5:ℂ)*f 5)*(5:ℂ)^((m:ℂ)-s)*G s (SmallLevelTwentyOne.gridIndex j)-
    ((5:ℂ)^((m:ℂ)-s))^2*G s (SmallLevelTwentyOne.gridIndex (5*j))

theorem oldFiveSource_meromorphic (m : ℕ) (f : ℕ → ℂ)
    (G : ℂ → Fin 42 → ℂ) (hG : ∀ i s, MeromorphicNFAt (fun z => G z i) s)
    (j : ℤ) (s : ℂ) : MeromorphicAt (oldFiveSource m f G j) s := by
  have hp := hecke_parameter_analytic (by decide : 0<5) m s
  exact (((analyticAt_const.mul hp).meromorphicAt).mul (hG _ s).meromorphicAt).sub
    ((hp.fun_pow 2).meromorphicAt.mul (hG _ s).meromorphicAt)

theorem oldFiveSource_analytic (m : ℕ) (f : ℕ → ℂ)
    (G : ℂ → Fin 42 → ℂ) (j : ℤ) (s : ℂ)
    (hG : ∀ i, AnalyticAt ℂ (fun z => G z i) s) :
    AnalyticAt ℂ (oldFiveSource m f G j) s := by
  have hp := hecke_parameter_analytic (by decide : 0<5) m s
  exact (((analyticAt_const.mul hp).mul (hG _))).sub ((hp.fun_pow 2).mul (hG _))

/-- Hecke5 sums use only previously continued42-grid coordinates as
source terms. The Hecke5 eigenvalue is arbitrary, including zero. -/
theorem original_five_source {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hGF : ∀ s, BG<s.re → G s=SmallLevelTwentyOne.gridVector (2*m) f s) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re →
      completeSum 210 (by decide) 5 j (gridVector 210 (2*m) f s)=oldFiveSource m f G j s := by
  obtain ⟨B,hB⟩ := original_hecke_grid 210 (by decide) hm hf
    (by decide : Nat.Prime 5) (by decide : 5∣210)
  refine ⟨max B BG,?_⟩
  intro j s hs
  have h := hB j s (lt_of_le_of_lt (le_max_left _ _) hs)
  have hsG := lt_of_le_of_lt (le_max_right B BG) hs
  have he (t : ℤ) : grid (2*m) f 210 (5*t) s=grid (2*m) f 42 t s := by
    unfold grid
    congr 1
    push_cast
    ring
  unfold heckeLeading at h
  norm_num only [show ¬5∣21 by decide,ite_false,Nat.cast_ofNat] at h
  rw [he j,show (25:ℤ)*j=5*(5*j) by ring,he (5*j)] at h
  unfold oldFiveSource
  rw [hGF s hsG,SmallLevelTwentyOne.gridVector_index,SmallLevelTwentyOne.gridVector_index]
  simp only [completeSum,gridVector_index]
  linear_combination h

#print axioms embedded_grid
#print axioms oldFiveSource_meromorphic
#print axioms original_five_source
end SmallLevelTwentyOneLargeGridModel
