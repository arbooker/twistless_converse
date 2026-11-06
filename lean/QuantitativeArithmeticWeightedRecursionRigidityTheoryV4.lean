module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Consolidated chapter: QuantitativeArithmeticWeightedRecursionRigidity. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticWeightedRecursionRigidityV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticWeightedRecursionRigidity

/-- A finite recursion cannot support a nonzero function whose weighted norm
is bounded if its total weighted amplification is strictly less than one. -/
theorem weighted_recursion_zero {X I : Type*} [Nonempty X] [Fintype I]
    (D : X → ℂ) (T : I → X → X) (c : I → ℂ) (w : X → ℝ) (q : I → ℝ)
    (hw : ∀ x, 0<w x) (hq : ∀ i, 0≤q i)
    (hsmall : ∑ i, q i < 1)
    (hweight : ∀ i x, ‖c i‖*w x ≤ q i*w (T i x))
    (hrec : ∀ x, D x=∑ i, c i*D (T i x))
    (hbound : BddAbove (Set.range (fun x => ‖D x‖*w x))) : D=0 := by
  let V : X → ℝ := fun x => ‖D x‖*w x
  let S : ℝ := ⨆ x, V x
  have hle (x : X) : V x≤S := le_ciSup hbound x
  have hnonneg : 0≤S := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact le_trans (mul_nonneg (norm_nonneg _) (le_of_lt (hw x))) (hle x)
  have hx (x : X) : V x≤(∑ i, q i)*S := by
    calc
      V x = ‖∑ i, c i*D (T i x)‖*w x := by
        change ‖D x‖*w x=_
        conv_lhs => rw [hrec x]
      _ ≤ (∑ i, ‖c i*D (T i x)‖)*w x :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (le_of_lt (hw x))
      _ = ∑ i, ‖c i*D (T i x)‖*w x := Finset.sum_mul _ _ _
      _ ≤ ∑ i, q i*S := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        calc
          ‖c i‖*‖D (T i x)‖*w x = ‖D (T i x)‖*(‖c i‖*w x) := by ring
          _ ≤ ‖D (T i x)‖*(q i*w (T i x)) :=
            mul_le_mul_of_nonneg_left (hweight i x) (norm_nonneg _)
          _ = q i*V (T i x) := by dsimp [V]; ring
          _ ≤ q i*S := mul_le_mul_of_nonneg_left (hle _) (hq i)
      _ = (∑ i, q i)*S := (Finset.sum_mul _ _ _).symm
  have hs : S≤(∑ i, q i)*S := ciSup_le hx
  have hs0 : S=0 := by nlinarith
  funext x
  have hv : ‖D x‖*w x≤0 := by simpa [V,hs0] using hle x
  have hd : ‖D x‖=0 := by nlinarith [norm_nonneg (D x),hw x]
  exact norm_eq_zero.mp hd
#print axioms weighted_recursion_zero
end QuantitativeArithmeticWeightedRecursionRigidity
end
end

/-! ## QuantitativeArithmeticExpandingRecursionRigidityV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticWeightedRecursionRigidity

/-- Faster than polynomial decay on an invariant expanding set forces a
finite homogeneous recursion to vanish, for arbitrary fixed coefficients. -/
theorem expanding_recursion_zero {X I : Type*} [Nonempty X] [Fintype I]
    (D : X → ℂ) (T : I → X → X) (c : I → ℂ) (height : X → ℝ)
    (hpos : ∀ x, 0<height x)
    (hexpand : ∀ i x, 2*height x≤height (T i x))
    (hrec : ∀ x, D x=∑ i, c i*D (T i x))
    (hbound : ∀ L : ℕ, BddAbove (Set.range (fun x => ‖D x‖*height x^L))) : D=0 := by
  obtain ⟨L,hL⟩ := pow_unbounded_of_one_lt (∑ i, ‖c i‖) (by norm_num : (1:ℝ)<2)
  have hpow : (0:ℝ)<2^L := pow_pos (by norm_num) _
  apply weighted_recursion_zero D T c (fun x => height x^L) (fun i => ‖c i‖/2^L)
  · intro x
    exact pow_pos (hpos x) _
  · intro i
    exact div_nonneg (norm_nonneg _) (le_of_lt hpow)
  · rw [← Finset.sum_div]
    exact (div_lt_one hpow).mpr hL
  · intro i x
    have hh : (2:ℝ)^L*height x^L≤height (T i x)^L := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg (by norm_num) (le_of_lt (hpos x))) (hexpand i x) L
    calc
      ‖c i‖*height x^L = (‖c i‖/2^L)*((2:ℝ)^L*height x^L) := by field_simp
      _ ≤ (‖c i‖/2^L)*height (T i x)^L :=
        mul_le_mul_of_nonneg_left hh (div_nonneg (norm_nonneg _) (le_of_lt hpow))
  · exact hrec
  · exact hbound L
#print axioms expanding_recursion_zero
end QuantitativeArithmeticWeightedRecursionRigidity
end
end

/-! ## QuantitativeArithmeticRecursionConstantV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticWeightedRecursionRigidity

/-- A constant forcing term is incompatible with decay along an unbounded
height on which the recursion never moves downwards. -/
theorem forcing_zero {X I : Type*} [Fintype I]
    (D : X → ℂ) (T : I → X → X) (c : I → ℂ) (d : ℂ) (height : X → ℝ)
    (hpos : ∀ x, 0<height x) (hmove : ∀ i x, height x≤height (T i x))
    (hunbounded : ∀ R : ℝ, ∃ x, R<height x)
    (hrec : ∀ x, D x=(∑ i, c i*D (T i x))+d)
    (hbound : BddAbove (Set.range (fun x => ‖D x‖*height x))) : d=0 := by
  obtain ⟨C,hC⟩ := hbound
  have hc (x : X) : ‖D x‖*height x≤C := hC (Set.mem_range_self x)
  have hd (x : X) : ‖d‖*height x≤C+∑ i, ‖c i‖*C := by
    have he : d=D x-∑ i, c i*D (T i x) := by rw [hrec x]; ring
    calc
      ‖d‖*height x = ‖D x-∑ i, c i*D (T i x)‖*height x := by rw [he]
      _ ≤ (‖D x‖+‖∑ i, c i*D (T i x)‖)*height x :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (le_of_lt (hpos x))
      _ ≤ (‖D x‖+∑ i, ‖c i*D (T i x)‖)*height x :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl (norm_sum_le _ _)) (le_of_lt (hpos x))
      _ = ‖D x‖*height x+∑ i, ‖c i*D (T i x)‖*height x := by rw [add_mul,Finset.sum_mul]
      _ ≤ C+∑ i, ‖c i‖*C := by
        apply add_le_add (hc x)
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact le_trans (mul_le_mul_of_nonneg_left (hmove i x) (norm_nonneg _)) (hc _)
  by_contra hn
  have hnpos : 0<‖d‖ := norm_pos_iff.mpr hn
  obtain ⟨x,hx⟩ := hunbounded ((C+∑ i, ‖c i‖*C)/‖d‖)
  have hx' := (div_lt_iff₀ hnpos).mp hx
  have := hd x
  nlinarith

/-- A rapidly approaching constant is preserved exactly by any finite
expanding recurrence. This includes the exceptional coefficient sum one. -/
theorem expanding_recursion_constant {X I : Type*} [Nonempty X] [Fintype I]
    (A : X → ℂ) (T : I → X → X) (c : I → ℂ) (a : ℂ) (height : X → ℝ)
    (hpos : ∀ x, 0<height x)
    (hexpand : ∀ i x, 2*height x≤height (T i x))
    (hunbounded : ∀ R : ℝ, ∃ x, R<height x)
    (hrec : ∀ x, A x=∑ i, c i*A (T i x))
    (hbound : ∀ L : ℕ, BddAbove (Set.range (fun x => ‖A x-a‖*height x^L))) :
    A=fun _ => a := by
  let D : X → ℂ := fun x => A x-a
  let d : ℂ := ((∑ i, c i)-1)*a
  have he (x : X) : D x=(∑ i, c i*D (T i x))+d := by
    dsimp [D,d]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hrec x]
    ring
  have hd : d=0 := forcing_zero D T c d height hpos (by
    intro i x
    have := hexpand i x
    linarith [hpos x]) hunbounded he (by simpa [D] using hbound 1)
  have hzero := expanding_recursion_zero D T c height hpos hexpand
    (by intro x; simpa [hd] using he x) hbound
  funext x
  have hx := congrFun hzero x
  exact sub_eq_zero.mp hx
#print axioms forcing_zero
#print axioms expanding_recursion_constant
end QuantitativeArithmeticWeightedRecursionRigidity
end
end
