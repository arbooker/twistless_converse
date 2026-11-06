module

public import AsymptoticFiniteNeumannV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstruction

open ContinuousLinearMap Filter

variable {G E : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [NormedAddCommGroup G] [InnerProductSpace ℂ G] in
theorem power_difference_norm_le (K K' : E →L[ℂ] E) (hK : ‖K‖≤1) (hK' : ‖K'‖≤1)
    (n : ℕ) : ‖K^n-K'^n‖≤(n:ℝ)*‖K-K'‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : K^(n+1)-K'^(n+1)=K*(K^n-K'^n)+(K-K')*K'^n := by
      rw [pow_succ',pow_succ']
      noncomm_ring
    rw [he]
    have hp : ‖K'^n‖≤1 := by simpa only [one_pow] using power_norm_le K' hK' n
    calc
      _ ≤ ‖K‖*‖K^n-K'^n‖+‖K-K'‖*‖K'^n‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1*((n:ℝ)*‖K-K'‖)+‖K-K'‖*1 :=
        add_le_add (mul_le_mul hK ih (norm_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      _ = _ := by push_cast; ring

/-- Perturbing every branch changes a fixed Neumann polynomial by a
uniformly controlled amount. No commutativity of the operators is used. -/
theorem finiteLow_difference_norm_le (K K' : E →L[ℂ] E) (B B' : G →L[ℂ] E)
    (hK : ‖K‖≤1) (hK' : ‖K'‖≤1) (n : ℕ) :
    ‖finiteLow K B n-finiteLow K' B' n‖≤
      (n:ℝ)*‖B-B'‖+(n:ℝ)^2*‖K-K'‖*‖B'‖ := by
  have hS : ‖∑ j∈Finset.range n,K^j‖≤(n:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j∈Finset.range n,(1:ℝ) := Finset.sum_le_sum (fun j _ => by
        simpa only [one_pow] using power_norm_le K hK j)
      _ = _ := by simp
  have hD : ‖(∑ j∈Finset.range n,K^j)-(∑ j∈Finset.range n,K'^j)‖≤(n:ℝ)^2*‖K-K'‖ := by
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j∈Finset.range n,(n:ℝ)*‖K-K'‖ := Finset.sum_le_sum (fun j hj =>
        (power_difference_norm_le K K' hK hK' j).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hj).le) (norm_nonneg _)))
      _ = _ := by simp; ring
  have he : finiteLow K B n-finiteLow K' B' n=
      (∑ j∈Finset.range n,K^j).comp (B-B')+
      ((∑ j∈Finset.range n,K^j)-(∑ j∈Finset.range n,K'^j)).comp B' := by
    simp only [finiteLow,comp_sub,sub_comp]
    abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _)).trans
    (add_le_add (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))))

/-- For each fixed depth, uniform finite-fold approximations can be
substituted into the Neumann polynomial before taking the weight limit. -/
theorem finiteLow_tendstoUniformly_of_approximations {α ι : Type*} {l : Filter ι}
    (K : α → E →L[ℂ] E) (B : α → G →L[ℂ] E)
    (K' : ι → α → E →L[ℂ] E) (B' : ι → α → G →L[ℂ] E)
    {C : ℝ} (hC : 0≤C) (hK : ∀ a,‖K a‖≤1) (hK' : ∀ i a,‖K' i a‖≤1)
    (hB : ∀ a,‖B a‖≤C) (hk : TendstoUniformly K' K l) (hb : TendstoUniformly B' B l)
    (n : ℕ) :
    TendstoUniformly (fun i a => finiteLow (K' i a) (B' i a) n)
      (fun a => finiteLow (K a) (B a) n) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let D : ℝ := 1+(n:ℝ)+(n:ℝ)^2*C
  have hD : 0<D := by dsimp [D]; positivity
  have hδ : 0<ε/D := div_pos hε hD
  filter_upwards [(Metric.tendstoUniformly_iff.mp hk) (ε/D) hδ,
    (Metric.tendstoUniformly_iff.mp hb) (ε/D) hδ] with i hiK hiB
  intro a
  have hkδ : ‖K' i a-K a‖<ε/D := by simpa only [dist_eq_norm,norm_sub_rev] using hiK a
  have hbδ : ‖B' i a-B a‖<ε/D := by simpa only [dist_eq_norm,norm_sub_rev] using hiB a
  rw [dist_eq_norm,norm_sub_rev]
  apply (finiteLow_difference_norm_le (K' i a) (K a) (B' i a) (B a) (hK' i a) (hK a) n).trans_lt
  have he : (n:ℝ)*‖B' i a-B a‖+(n:ℝ)^2*‖K' i a-K a‖*‖B a‖≤
      ((n:ℝ)+(n:ℝ)^2*C)*(ε/D) := by
    calc
      _ ≤ (n:ℝ)*(ε/D)+(n:ℝ)^2*(ε/D)*C :=
        add_le_add (mul_le_mul_of_nonneg_left hbδ.le (Nat.cast_nonneg _))
          (mul_le_mul (mul_le_mul_of_nonneg_left hkδ.le (sq_nonneg _)) (hB a)
            (norm_nonneg _) (by positivity))
      _ = _ := by ring
  apply he.trans_lt
  have hmul : D*(ε/D)=ε := mul_div_cancel₀ ε hD.ne'
  dsimp [D] at hmul
  nlinarith

#print axioms power_difference_norm_le
#print axioms finiteLow_difference_norm_le
#print axioms finiteLow_tendstoUniformly_of_approximations

end AsymptoticReconstruction
