module

public import SmallLevelTwentyOneAugmentedWordRowsV1
public import SmallLevelTwentyOneAugmentedArithmeticDataV1
public import SmallLevelTwentyOneNormalizedAugmentedPoleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix SmallLevelTwentyOne
open QuantitativeArithmeticUniversalPoleVector

/-- All exported nontrivial word rows, infinity rows, closed Ramanujan
Taylor rows, entire primitive sums, and Hecke2/3/7 rows. -/
abbrev AugmentedRow := Fin 319 ⊕ Fin 34 ⊕ Fin 72 ⊕ Fin 8 ⊕ Fin 41

theorem augmentedRow_card : Fintype.card AugmentedRow=474 := by norm_num [AugmentedRow]

def augmentedLeading (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (s : ℂ) :
    Matrix AugmentedRow (Fin 42) ℂ
  | .inl i => wordLeadingRow m (ε*I^(2*m)) (augmentedWordRows i).row s
  | .inr (.inl i) => fun j => if j=gridIndex (augmentedInfinityRows i).source then 1 else 0
  | .inr (.inr (.inl i)) =>
      let r := augmentedTaylorSpecs i
      ramanujanLeadingRow m f ε r.1 r.2.1 (-(r.2.2/r.2.1)) s
  | .inr (.inr (.inr (.inl i))) =>
      samplingRow (FinitenessRamanujanSum.residues (augmentedEntireSpecs i)) (augmentedEntireSpecs i) 0
  | .inr (.inr (.inr (.inr i))) =>
      heckeCoefficientRow m f (augmentedHeckeSpecs i).1 (augmentedHeckeSpecs i).2 s

/-- Every one of the 474 finite rows is derived from the original Euler
input on the SAME continued grid and principal vector. -/
theorem augmented_leading_pole {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n)) :
    augmentedLeading m f ε x *ᵥ v=0 := by
  funext r
  rcases r with i | i | i | i | i
  · simpa only [augmentedLeading,Matrix.mulVec,dotProduct,wordLeadingRow_apply,
      certificateCoefficient_eq,Pi.zero_apply] using
      pole_certificate hf ε hε hlaw BG G hG hGF x v hv hshift (augmentedWordRows i)
  · simpa [augmentedLeading,Matrix.mulVec,dotProduct] using
      pole_infinity_certificate hm hf BG G hG hGF x v hv (augmentedInfinityRows i)
  · obtain ⟨hq,hqQ,ht,hd,htd⟩ := augmentedTaylorSpecs_valid i
    simpa only [augmentedLeading,Matrix.mulVec,dotProduct,ramanujanLeadingRow_apply,
      Pi.zero_apply] using
      pole_full_taylor hf ε hlaw BG G hG hGF x v hv hshift
        (augmentedTaylorSpecs i).1 hq hqQ (augmentedTaylorSpecs i).2.1
        (augmentedTaylorSpecs i).2.2 ht hd htd
  · simpa only [augmentedLeading,Matrix.mulVec,dotProduct,samplingRow_apply,
      SmallLevelTwentyOne.sampleSum,Pi.zero_apply] using
      pole_full_entire hm hf BG G hG hGF x v hv (augmentedEntireSpecs i)
        (augmentedEntireSpecs_valid i).1 (augmentedEntireSpecs_valid i).2
  · simpa only [augmentedLeading,Matrix.mulVec,dotProduct,heckeCoefficientRow_apply,
      Pi.zero_apply] using
      pole_full_hecke hm hf BG G hG hGF x v hv (augmentedHeckeSpecs i).1
        (augmentedHeckeSpecs_valid i).1 (augmentedHeckeSpecs_valid i).2 (augmentedHeckeSpecs i).2

/-- Concrete original-input endpoint for the entire finite augmented
leading system. No computed row or modularity assumption remains. -/
theorem original_augmented_leading_kernel {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
            leadingMatrix m f ε (x+n) *ᵥ v=0 ∧
            augmentedLeading m f ε (x+n) *ᵥ v=0 := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,hp⟩ := original_normalized_augmented_pole_constraints hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,?_⟩
  intro x hx
  obtain ⟨n,v,hv,h28,hshift,hker,_hw,_hi⟩ := hp x hx
  exact ⟨n,v,hv,h28,hshift,hker,augmented_leading_pole hm hf ε hε hlaw BG G hG hGF
    (x+n) v hv hshift⟩

#print axioms augmentedRow_card
#print axioms augmented_leading_pole
#print axioms original_augmented_leading_kernel
end SmallLevelTwentyOneKnownWords
