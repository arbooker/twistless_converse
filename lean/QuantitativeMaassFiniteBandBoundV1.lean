module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
@[expose] public noncomputable section

open scoped BigOperators

namespace QuantitativeMaass

/-- The finite incidence estimate underlying the weight-band argument:
each input can contribute to at most D output bands. -/
theorem finite_band_incidence_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ) (rows : ι → Finset κ) (D : ℕ)
    (hrows : ∀ i∈S,rows i⊆T)
    (hcol : ∀ j∈T,(S.filter (fun i => j∈rows i)).card≤D)
    (a : κ → ℝ) (ha : ∀ j∈T,0≤a j) :
    (∑ i∈S,∑ j∈rows i,a j)≤(D:ℝ)*∑ j∈T,a j := by
  have he (i : ι) (hi : i∈S) :
      (∑ j∈rows i,a j)=∑ j∈T,if j∈rows i then a j else 0 := by
    calc
      _ = ∑ j∈rows i,if j∈rows i then a j else 0 :=
        Finset.sum_congr rfl (fun j hj => by simp only [hj,ite_true])
      _ = _ := Finset.sum_subset (hrows i hi) (fun j _ hj => by simp only [hj,ite_false])
  calc
    _ = ∑ i∈S,∑ j∈T,if j∈rows i then a j else 0 := Finset.sum_congr rfl he
    _ = ∑ j∈T,∑ i∈S,if j∈rows i then a j else 0 := Finset.sum_comm
    _ = ∑ j∈T,((S.filter (fun i => j∈rows i)).card:ℝ)*a j := by
      simp only [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ ∑ j∈T,(D:ℝ)*a j := Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcol j hj) (ha j hj))
    _ = _ := (Finset.mul_sum T a (D:ℝ)).symm

/-- The exact squared-norm estimate for finitely many propagation bands.
No orthogonality of the individual summands in an output band is assumed;
the two multiplicity factors come from the row and column bounds. -/
theorem finite_band_norm_square_bound {ι κ H : Type*} [DecidableEq ι] [DecidableEq κ]
    [NormedAddCommGroup H]
    (S : Finset ι) (T : Finset κ) (rows : ι → Finset κ) (D : ℕ)
    (hrows : ∀ i∈S,rows i⊆T) (hrow : ∀ i∈S,(rows i).card≤D)
    (hcol : ∀ j∈T,(S.filter (fun i => j∈rows i)).card≤D)
    (C : ℝ) (a : κ → ℝ)
    (v : ι → κ → H) (hv : ∀ i∈S,∀ j∈rows i,‖v i j‖≤C*a j) :
    (∑ i∈S,‖∑ j∈rows i,v i j‖^2)≤(D:ℝ)^2*C^2*∑ j∈T,(a j)^2 := by
  have hr (i : ι) (hi : i∈S) :
      ‖∑ j∈rows i,v i j‖^2≤(D:ℝ)*C^2*∑ j∈rows i,(a j)^2 := by
    have hn : ‖∑ j∈rows i,v i j‖≤C*∑ j∈rows i,a j := by
      calc
        _ ≤ ∑ j∈rows i,‖v i j‖ := norm_sum_le _ _
        _ ≤ ∑ j∈rows i,C*a j := Finset.sum_le_sum (fun j hj => hv i hi j hj)
        _ = _ := (Finset.mul_sum _ _ _).symm
    calc
      _ ≤ (C*∑ j∈rows i,a j)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = C^2*(∑ j∈rows i,a j)^2 := mul_pow _ _ _
      _ ≤ C^2*((rows i).card*∑ j∈rows i,(a j)^2) :=
        mul_le_mul_of_nonneg_left (sq_sum_le_card_mul_sum_sq) (sq_nonneg C)
      _ ≤ C^2*((D:ℝ)*∑ j∈rows i,(a j)^2) := by
        gcongr
        exact_mod_cast hrow i hi
      _ = _ := by ring
  calc
    _ ≤ ∑ i∈S,(D:ℝ)*C^2*∑ j∈rows i,(a j)^2 := Finset.sum_le_sum hr
    _ = (D:ℝ)*C^2*(∑ i∈S,∑ j∈rows i,(a j)^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ (D:ℝ)*C^2*((D:ℝ)*∑ j∈T,(a j)^2) :=
      mul_le_mul_of_nonneg_left
        (finite_band_incidence_bound S T rows D hrows hcol (fun j => (a j)^2) (fun j _ => sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg D) (sq_nonneg C))
    _ = _ := by ring

#print axioms finite_band_incidence_bound
#print axioms finite_band_norm_square_bound

end QuantitativeMaass
