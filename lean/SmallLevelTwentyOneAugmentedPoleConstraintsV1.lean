module

public import SmallLevelTwentyOnePoleWordRowsV1
public import SmallLevelTwentyOneTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix Filter Set SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- Original-input endpoint for the additional word rows. Every putative
pole has a rightmost integer translate and ONE nonzero principal vector
satisfying all closed word and source-to-infinity equations. The continuation,
Fricke law and vector are derived, not hypotheses replacing modularity.
This is an input to pole exclusion, not a claim of pole exclusion. -/
theorem original_augmented_pole_constraints {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        ∀ x : ℂ, (∃ i, meromorphicOrderAt (fun z => G z i) x<0) →
          ∃ n : ℕ, ∃ v : Fin 42 → ℂ,
            IsLeadingVector G (x+n) v ∧
            (∀ a : ℕ, 0<a → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n+a)) ∧
            (leadingMatrix m f ε (x+n) *ᵥ v=0) ∧
            (∀ w : Word, coordC w≠0 → ∀ t u : ℤ, wordDen w t≠0 →
              (coordA w*((t:ℝ)/42)+coordB w)/wordDen w t=(u:ℝ)/42 →
              v (gridIndex t)-wordCoefficient m (ε*I^(2*m)) w t 0 (x+n)*v (gridIndex u)=0) ∧
            (∀ w : Word, coordC w≠0 → ∀ t : ℤ, wordDen w t=0 → v (gridIndex t)=0) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<21) hf
  obtain ⟨BG,G,hG,hGF,hhalf,hH,hrow⟩ := continued_system_of_law hm hf ε hε hlaw
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,?_⟩
  intro x hpole
  obtain ⟨n,hn,hshift⟩ := SmallLevelPoleGrid.rightmost_pole
    (fun i z => G z i) hpole BG hhalf
  obtain ⟨v,hv⟩ := exists_leading_vector G (x+n)
    (fun i => (hG i (x+n)).meromorphicAt) hn
  refine ⟨n,v,hv,hshift,?_,?_,?_⟩
  · funext i
    exact hv.taylor hG hshift BG
      (fun z => leadingMatrix m f ε z i)
      (fun a z => shiftMatrix m f ε a z i)
      (fun a z => errorVector m f ε a z i)
      (leadingMatrix_analytic m f ε (x+n) i)
      (fun a => shiftMatrix_analytic m f ε a (x+n) i)
      (fun a z hz => hH a i z hz) (fun a ha => hrow a i (x+n) ha)
  · intro w hC t u ht hu
    exact pole_word_constraint hf ε hε hlaw BG G hG hGF (x+n) v hv hshift w hC t u ht hu
  · intro w hC t ht
    exact pole_infinity_constraint hm hf BG G hG hGF (x+n) v hv w hC t ht

#print axioms original_augmented_pole_constraints
end SmallLevelTwentyOneKnownWords
