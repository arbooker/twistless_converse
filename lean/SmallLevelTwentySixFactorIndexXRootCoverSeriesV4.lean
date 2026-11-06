module
public import SmallLevelTwentySixFactorIndexXRootGeometrySeriesV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixFactor6XRoot
open QuantitativeArithmeticComplexHornerBounds Polynomial Finset

theorem distance_le_norm (i j : Fin 6) (hij : i≠j) :
    (distanceQ i j:ℝ)≤‖ratComplex (centerQ i)-ratComplex (centerQ j)‖ := by
  have h : (distanceQ i j:ℝ)≤max |((centerQ i).1:ℝ)-((centerQ j).1:ℝ)|
      |((centerQ i).2:ℝ)-((centerQ j).2:ℝ)| := by
    exact_mod_cast distance_lower i j hij
  apply h.trans
  apply max_le
  · simpa using Complex.abs_re_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))
  · simpa using Complex.abs_im_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))

theorem center_injective : Function.Injective (fun i : Fin 6 => ratComplex (centerQ i)) := by
  intro i j hij
  change ratComplex (centerQ i)=ratComplex (centerQ j) at hij
  by_contra hne
  have h := distance_le_norm i j hne
  rw [hij,sub_self,norm_zero] at h
  have hp : 0<(distanceQ i j:ℝ) := by exact_mod_cast distance_positive i j
  exact (not_le_of_gt hp) h

theorem radius_positive : 0<(radiusQ:ℝ) := by
  exact_mod_cast (show (0:ℚ)<radiusQ by decide +kernel)

theorem p_bound_erase_product (i : Fin 6) : (pBoundQ i:ℝ)=
    (1/100:ℝ)*(radiusQ:ℝ)*∏ j ∈ (Finset.univ : Finset (Fin 6)).erase i,(distanceQ i j:ℝ) := by
  have h : (pBoundQ i:ℝ)=(1/100:ℝ)*(radiusQ:ℝ)*∏ j : Fin 6,(distanceQ i j:ℝ) := by
    have hq := congrArg (fun q : ℚ => (q:ℝ)) (bound_product i)
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_prod] using hq
  have hp : (∏ j ∈ (Finset.univ : Finset (Fin 6)).erase i,(distanceQ i j:ℝ))=
      ∏ j : Fin 6,(distanceQ i j:ℝ) := by
    simpa only [distance_diagonal,Rat.cast_one,mul_one] using
      Finset.prod_erase_mul Finset.univ (fun j : Fin 6 => (distanceQ i j:ℝ)) (Finset.mem_univ i)
  rw [hp]
  exact h

/-- Every root of the concrete degree-6 polynomial lies in a certified disk.
The proof uses only exact rational certificates and barycentric interpolation. -/
theorem pRoot_root_in_disk (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 6,‖z-ratComplex (centerQ i)‖<(radiusQ:ℝ) := by
  have hsmall : ∑ i : Fin 6,
      ‖Lagrange.nodalWeight Finset.univ (fun j => ratComplex (centerQ j)) i*
        pRoot.eval (ratComplex (centerQ i))‖/(radiusQ:ℝ)<1 := by
    apply lt_of_le_of_lt _ (show (∑ _i : Fin 6,(1/100:ℝ))<1 by norm_num)
    apply Finset.sum_le_sum
    intro i _hi
    apply (div_le_iff₀ radius_positive).mpr
    apply QuantitativeArithmeticPolynomialRootCover.nodal_eval_bound_of_separations
      Finset.univ (fun j => ratComplex (centerQ j)) pRoot i
      (fun j => (distanceQ i j:ℝ)) (1/100:ℝ) (radiusQ:ℝ)
    · intro j _hj
      exact_mod_cast distance_positive i j
    · intro j hj
      exact distance_le_norm i j (Finset.mem_erase.mp hj).1.symm
    · rw [← p_bound_erase_product]
      exact all_P_value_bounds i
  obtain ⟨i,_hi,h⟩ := QuantitativeArithmeticPolynomialRootCover.monic_root_cover
    Finset.univ (fun j => ratComplex (centerQ j)) (fun _ => (radiusQ:ℝ)) pRoot
    center_injective.injOn pRoot_monic (by simpa using pRoot_degree)
    (fun _ _ => radius_positive) hsmall z hz
  exact ⟨i,h⟩

#print axioms center_injective
#print axioms pRoot_root_in_disk
end SmallLevelTwentySixFactor6XRoot
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

namespace SmallLevelTwentySixFactor7XRoot
open QuantitativeArithmeticComplexHornerBounds Polynomial Finset

theorem distance_le_norm (i j : Fin 7) (hij : i≠j) :
    (distanceQ i j:ℝ)≤‖ratComplex (centerQ i)-ratComplex (centerQ j)‖ := by
  have h : (distanceQ i j:ℝ)≤max |((centerQ i).1:ℝ)-((centerQ j).1:ℝ)|
      |((centerQ i).2:ℝ)-((centerQ j).2:ℝ)| := by
    exact_mod_cast distance_lower i j hij
  apply h.trans
  apply max_le
  · simpa using Complex.abs_re_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))
  · simpa using Complex.abs_im_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))

theorem center_injective : Function.Injective (fun i : Fin 7 => ratComplex (centerQ i)) := by
  intro i j hij
  change ratComplex (centerQ i)=ratComplex (centerQ j) at hij
  by_contra hne
  have h := distance_le_norm i j hne
  rw [hij,sub_self,norm_zero] at h
  have hp : 0<(distanceQ i j:ℝ) := by exact_mod_cast distance_positive i j
  exact (not_le_of_gt hp) h

theorem radius_positive : 0<(radiusQ:ℝ) := by
  exact_mod_cast (show (0:ℚ)<radiusQ by decide +kernel)

theorem p_bound_erase_product (i : Fin 7) : (pBoundQ i:ℝ)=
    (1/100:ℝ)*(radiusQ:ℝ)*∏ j ∈ (Finset.univ : Finset (Fin 7)).erase i,(distanceQ i j:ℝ) := by
  have h : (pBoundQ i:ℝ)=(1/100:ℝ)*(radiusQ:ℝ)*∏ j : Fin 7,(distanceQ i j:ℝ) := by
    have hq := congrArg (fun q : ℚ => (q:ℝ)) (bound_product i)
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_prod] using hq
  have hp : (∏ j ∈ (Finset.univ : Finset (Fin 7)).erase i,(distanceQ i j:ℝ))=
      ∏ j : Fin 7,(distanceQ i j:ℝ) := by
    simpa only [distance_diagonal,Rat.cast_one,mul_one] using
      Finset.prod_erase_mul Finset.univ (fun j : Fin 7 => (distanceQ i j:ℝ)) (Finset.mem_univ i)
  rw [hp]
  exact h

/-- Every root of the concrete degree-7 polynomial lies in a certified disk.
The proof uses only exact rational certificates and barycentric interpolation. -/
theorem pRoot_root_in_disk (z : ℂ) (hz : pRoot.eval z=0) :
    ∃ i : Fin 7,‖z-ratComplex (centerQ i)‖<(radiusQ:ℝ) := by
  have hsmall : ∑ i : Fin 7,
      ‖Lagrange.nodalWeight Finset.univ (fun j => ratComplex (centerQ j)) i*
        pRoot.eval (ratComplex (centerQ i))‖/(radiusQ:ℝ)<1 := by
    apply lt_of_le_of_lt _ (show (∑ _i : Fin 7,(1/100:ℝ))<1 by norm_num)
    apply Finset.sum_le_sum
    intro i _hi
    apply (div_le_iff₀ radius_positive).mpr
    apply QuantitativeArithmeticPolynomialRootCover.nodal_eval_bound_of_separations
      Finset.univ (fun j => ratComplex (centerQ j)) pRoot i
      (fun j => (distanceQ i j:ℝ)) (1/100:ℝ) (radiusQ:ℝ)
    · intro j _hj
      exact_mod_cast distance_positive i j
    · intro j hj
      exact distance_le_norm i j (Finset.mem_erase.mp hj).1.symm
    · rw [← p_bound_erase_product]
      exact all_P_value_bounds i
  obtain ⟨i,_hi,h⟩ := QuantitativeArithmeticPolynomialRootCover.monic_root_cover
    Finset.univ (fun j => ratComplex (centerQ j)) (fun _ => (radiusQ:ℝ)) pRoot
    center_injective.injOn pRoot_monic (by simpa using pRoot_degree)
    (fun _ _ => radius_positive) hsmall z hz
  exact ⟨i,h⟩

#print axioms center_injective
#print axioms pRoot_root_in_disk
end SmallLevelTwentySixFactor7XRoot
end
