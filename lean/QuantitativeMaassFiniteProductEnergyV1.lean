module

public import QuantitativeMaassFiniteEnergyPerturbationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {E ι J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

omit [CompleteSpace E] [Fintype ι] in
theorem contraction_list_prod (s : List J) (A : J → E →L[ℂ] E)
    (hA : ∀ j,‖A j‖≤1) : ‖(s.map A).prod‖≤1 := by
  induction s with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons j s ih =>
    simp only [List.map_cons,List.prod_cons]
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (A j),hA j])

/-- Products of approximate local projections have controlled squared
error without any commutativity assumption. -/
theorem finiteBandEnergy_product_difference (b : OrthonormalBasis ι ℂ E)
    (s : List J) (A B : J → E →L[ℂ] E) (hA : ∀ j,‖A j‖≤1) (hB : ∀ j,‖B j‖≤1) :
    finiteBandEnergy b ((s.map A).prod-(s.map B).prod) ≤
      (4:ℝ)^s.length*(s.map (fun j => finiteBandEnergy b (A j-B j))).sum := by
  have hsum (l : List J) : 0≤(l.map (fun j => finiteBandEnergy b (A j-B j))).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact finiteBandEnergy_nonneg b _
  induction s with
  | nil => simp [finiteBandEnergy]
  | cons j s ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,List.sum_cons]
    have hid : A j*(s.map A).prod-B j*(s.map B).prod=
        A j*((s.map A).prod-(s.map B).prod)+(A j-B j)*(s.map B).prod := by
      noncomm_ring
    have ha : ‖A j‖^2≤1 := by nlinarith [hA j,norm_nonneg (A j)]
    have hb : ‖(s.map B).prod‖^2≤1 := by
      nlinarith [contraction_list_prod s B hB,norm_nonneg (s.map B).prod]
    have hl := (finiteBandEnergy_left b (A j) ((s.map A).prod-(s.map B).prod)).trans
      (mul_le_mul_of_nonneg_right ha (finiteBandEnergy_nonneg b _))
    have hr := (finiteBandEnergy_right b (A j-B j) (s.map B).prod).trans
      (mul_le_mul_of_nonneg_right hb (finiteBandEnergy_nonneg b _))
    simp only [one_mul] at hl hr
    rw [hid]
    apply (finiteBandEnergy_add b _ _).trans
    have hc : 1≤(4:ℝ)^s.length := one_le_pow₀ (by norm_num)
    have hzero := finiteBandEnergy_nonneg b (A j-B j)
    have htail := hsum s
    have he := add_le_add (mul_le_mul_of_nonneg_left (hl.trans ih) (by norm_num : (0:ℝ)≤2))
      (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ)≤2))
    apply he.trans
    rw [pow_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hzero,
      mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤4) s.length) htail]

#print axioms contraction_list_prod
#print axioms finiteBandEnergy_product_difference

end QuantitativeMaass
