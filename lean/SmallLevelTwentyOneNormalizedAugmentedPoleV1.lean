module

public import SmallLevelTwentyOneAugmentedPoleConstraintsV1
public import SmallLevelTwentyOneTheoryV4
public import QuantitativeArithmeticUniversalPoleNormalizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix Filter Set SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- Original-input endpoint for the additional word rows. Every putative
pole has a rightmost integer translate and ONE principal vector normalized at coordinate28
satisfying all closed word and source-to-infinity equations. The continuation,
Fricke law and vector are derived, not hypotheses replacing modularity.
This is an input to pole exclusion, not a claim of pole exclusion. -/
theorem original_normalized_augmented_pole_constraints {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        ∀ x : ℂ, (∃ i, meromorphicOrderAt (fun z => G z i) x<0) →
          ∃ n : ℕ, ∃ v : Fin 42 → ℂ,
            IsLeadingVector G (x+n) v ∧ v 28=1 ∧
            (∀ a : ℕ, 0<a → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n+a)) ∧
            (leadingMatrix m f ε (x+n) *ᵥ v=0) ∧
            (∀ w : Word, coordC w≠0 → ∀ t u : ℤ, wordDen w t≠0 →
              (coordA w*((t:ℝ)/42)+coordB w)/wordDen w t=(u:ℝ)/42 →
              v (gridIndex t)-wordCoefficient m (ε*I^(2*m)) w t 0 (x+n)*v (gridIndex u)=0) ∧
            (∀ w : Word, coordC w≠0 → ∀ t : ℤ, wordDen w t=0 → v (gridIndex t)=0) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,hp⟩ := original_augmented_pole_constraints hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,?_⟩
  intro x hpole
  obtain ⟨n,v,hv,hshift,hker,_hwords,_hinfinity⟩ := hp x hpole
  have h28 : v 28≠0 := fun h => hv.1 (original_rank_coordinate hf hε v hker h)
  obtain ⟨w,hw,hw28,hwe⟩ := hv.normalize 28 h28
  have hscale : w=(v 28)⁻¹ • v := by
    funext j
    rw [hwe j]
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  refine ⟨n,w,hw,hw28,hshift,?_,?_,?_⟩
  · rw [hscale,Matrix.mulVec_smul,hker,smul_zero]
  · intro u hC t q ht hq
    exact pole_word_constraint hf ε hε hlaw BG G hG hGF (x+n) w hw hshift u hC t q ht hq
  · intro u hC t ht
    exact pole_infinity_constraint hm hf BG G hG hGF (x+n) w hw u hC t ht

#print axioms original_normalized_augmented_pole_constraints
end SmallLevelTwentyOneKnownWords
