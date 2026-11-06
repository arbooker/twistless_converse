module

public import SmallLevelTwentyOneAugmentedGermsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

theorem augmentedLeading_analytic (m : ℕ) (f : ℕ → ℂ) (ε x : ℂ)
    (r : AugmentedRow) (j : Fin 42) :
    AnalyticAt ℂ (fun z => augmentedLeading m f ε z r j) x := by
  rcases r with i | i | i | i | i
  · exact wordLeadingRow_analytic m (ε*I^(2*m)) (augmentedWordRows i).row x j
  · exact analyticAt_const
  · exact analyticAt_const.sub
      ((fullTaylorCoefficient_analytic (2*m) f ε (augmentedTaylorSpecs_valid i).1
        (augmentedTaylorSpecs_valid i).2.2.1 0 x).mul analyticAt_const)
  · exact analyticAt_const
  · exact heckeCoefficientRow_analytic m f (augmentedHeckeSpecs_valid i).1.pos
      (augmentedHeckeSpecs i).2 x j

theorem augmentedShift_analytic (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (x : ℂ)
    (r : AugmentedRow) (j : Fin 42) :
    AnalyticAt ℂ (fun z => augmentedShift m f ε n z r j) x := by
  rcases r with i | i | i | i | i
  · exact wordShiftRow_analytic m (ε*I^(2*m)) (augmentedWordRows i).row n x j
  · exact analyticAt_const
  · exact (fullTaylorCoefficient_analytic (2*m) f ε (augmentedTaylorSpecs_valid i).1
      (augmentedTaylorSpecs_valid i).2.2.1 (n+1) x).mul analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_const

/-- Algebraic syzygies of the literal474-row matrix give the first-jet
constraints on the same universal vector. The syzygy must still be proved;
it is not assumed as a replacement for the pole-exclusion theorem. -/
theorem augmented_first_shift_constraint {ρ : Type*}
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (L : ℂ → Matrix ρ AugmentedRow ℂ)
    (hL : ∀ z r i, AnalyticAt ℂ (fun w => L w r i) z)
    (hLA : ∀ z, L z*augmentedLeading m f ε z=0) :
    (L (x-1)*augmentedShift m f ε 0 (x-1)) *ᵥ v=0 := by
  obtain ⟨B,H,hH,hrow⟩ := augmented_matrix_germs hm hf ε hε hlaw BG G hG hGF
  exact IsLeadingVector.first_shift B G (augmentedLeading m f ε) (augmentedShift m f ε)
    H L hG (augmentedShift_analytic m f ε) hH hL hLA hrow x v hv hshift

#print axioms augmentedLeading_analytic
#print axioms augmentedShift_analytic
#print axioms augmented_first_shift_constraint
end SmallLevelTwentyOneKnownWords
