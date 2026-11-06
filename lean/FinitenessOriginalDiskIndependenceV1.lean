module

public import FinitenessOriginalEulerFamilyV1
public import FinitenessWeightedIndependenceV1
public import FinitenessSeriesIndependenceV1
public import FinitenessOriginalFourierV1
public import FinitenessDiskJetV1

set_option autoImplicit false

@[expose] public section

namespace FinitenessOriginalDiskIndependence

open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction

theorem polynomial (N k : ℕ) (f : S N k) :
    FinitenessPolynomialSeries.PolynomialBound (fullCoefficients f.val k) := by
  obtain ⟨τ,_,hg⟩ := f.property.growth
  exact polynomial_bound f.property.zero hg k

theorem normalized_independent (N k : ℕ) :
    LinearIndependent ℂ (fun f : S N k => fullCoefficients f.val k) := by
  apply FinitenessWeightedIndependence.independent
    (fun f : S N k => f.val)
    (fun n => ((n:ℝ)^FinitenessCompletedNormalization.alpha k : ℝ))
    (FinitenessOriginalEulerFamily.independent N k)
  · intro f
    exact f.property.zero
  · intro n hn
    exact_mod_cast (Real.rpow_pos_of_pos
      (by exact_mod_cast Nat.pos_of_ne_zero hn) (FinitenessCompletedNormalization.alpha k)).ne'

noncomputable def representative (N k : ℕ) (f : S N k) : FinitenessDiskJet.space :=
  ⟨disk (fullCoefficients f.val k),disk_holomorphic (polynomial N k f)⟩

/-- The canonical disk representatives of all original solutions are
independent. No modularity theorem or Hecke stability of the disk space is used. -/
theorem independent (N k : ℕ) :
    LinearIndependent ℂ (representative N k) := by
  apply LinearIndependent.of_comp FinitenessDiskJet.space.subtype
  exact FinitenessSeriesIndependence.independent
    (fun f : S N k => fullCoefficients f.val k) (polynomial N k)
    (normalized_independent N k) (fun f => disk (fullCoefficients f.val k))
    (fun _ _ hw => ite_eq_left hw)

#print axioms normalized_independent
#print axioms independent

end FinitenessOriginalDiskIndependence
