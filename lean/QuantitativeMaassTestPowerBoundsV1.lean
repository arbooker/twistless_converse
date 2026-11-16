module

public import QuantitativeMaassTestMultiplierV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology ContDiff Distributions

namespace QuantitativeMaass

theorem positiveSmoothTestDeriv_tsupport_subset (φ : PositiveSmoothTest) :
    tsupport (positiveSmoothTestDeriv φ) ⊆ tsupport φ := by
  have he : (positiveSmoothTestDeriv φ : ℝ → ℝ)=deriv (φ : ℝ → ℝ) :=
    funext (positiveSmoothTestDeriv_apply φ)
  rw [he]
  exact tsupport_deriv_subset

theorem positiveTestPower_tsupport_subset (n : ℕ) (φ : PositiveSmoothTest) :
    tsupport (positiveTestPower n φ) ⊆ tsupport φ := by
  apply closure_mono
  intro t ht
  change φ t ≠ 0
  intro hz
  exact ht (by rw [positiveTestPower_apply,hz,zero_mul])

theorem positiveTestPower_succ_eq (n : ℕ) (φ : PositiveSmoothTest) :
    positiveTestPower (n+1) φ=positiveTestPower 1 (positiveTestPower n φ) := by
  ext t
  simp only [positiveTestPower_apply,pow_succ]
  ring

theorem positiveTestPower_one_deriv (φ : PositiveSmoothTest) :
    positiveSmoothTestDeriv (positiveTestPower 1 φ)=
      positiveTestPower 1 (positiveSmoothTestDeriv φ)+φ := by
  simpa only [Nat.cast_zero,zero_add,one_smul,positiveTestPower_zero] using
    positiveTestPower_deriv_succ 0 φ

theorem positiveTestPower_one_second (φ : PositiveSmoothTest) :
    positiveSmoothTestDeriv (positiveSmoothTestDeriv (positiveTestPower 1 φ))=
      positiveTestPower 1 (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ))+
        (2:ℝ) • positiveSmoothTestDeriv φ := by
  rw [positiveTestPower_one_deriv,map_add,positiveTestPower_one_deriv]
  simp only [two_smul,add_assoc]

private theorem time_mul_norm_le (φ ψ : PositiveSmoothTest) (R : ℝ)
    (hψ : tsupport ψ ⊆ tsupport φ) (hR : ∀ t∈tsupport φ,‖t‖≤R) (t : ℝ) :
    ‖positiveTestPower 1 ψ t‖≤R*‖ψ t‖ := by
  rw [positiveTestPower_apply,pow_one,norm_mul,mul_comm]
  by_cases hz : ψ t=0
  · simp only [hz,norm_zero,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hR t (hψ (subset_tsupport _ hz))) (norm_nonneg _)

/-- Multiplication by t^n costs at most (R+2)^n in the common C2 bound.
The support remains fixed; no bound on t outside that support is needed. -/
theorem positiveTestPower_two_derivative_bound (φ : PositiveSmoothTest)
    (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hr : ∀ t∈tsupport φ,‖t‖≤R)
    (h0 : ∀ t,‖φ t‖≤C)
    (h1 : ∀ t,‖positiveSmoothTestDeriv φ t‖≤C)
    (h2 : ∀ t,‖positiveSmoothTestDeriv (positiveSmoothTestDeriv φ) t‖≤C) :
    ∀ n t, ‖positiveTestPower n φ t‖≤C*(R+2)^n ∧
      ‖positiveSmoothTestDeriv (positiveTestPower n φ) t‖≤C*(R+2)^n ∧
      ‖positiveSmoothTestDeriv (positiveSmoothTestDeriv (positiveTestPower n φ)) t‖≤C*(R+2)^n := by
  intro n
  induction n with
  | zero =>
    intro t
    simpa only [positiveTestPower_zero,pow_zero,mul_one] using ⟨h0 t,h1 t,h2 t⟩
  | succ n ih =>
    intro t
    let ψ := positiveTestPower n φ
    have hs0 : tsupport ψ ⊆ tsupport φ := positiveTestPower_tsupport_subset n φ
    have hs1 := (positiveSmoothTestDeriv_tsupport_subset ψ).trans hs0
    have hs2 := (positiveSmoothTestDeriv_tsupport_subset (positiveSmoothTestDeriv ψ)).trans hs1
    have b0 := time_mul_norm_le φ ψ R hs0 hr t
    have b1 := time_mul_norm_le φ (positiveSmoothTestDeriv ψ) R hs1 hr t
    have b2 := time_mul_norm_le φ (positiveSmoothTestDeriv (positiveSmoothTestDeriv ψ)) R hs2 hr t
    have i0 := (ih t).1
    have i1 := (ih t).2.1
    have i2 := (ih t).2.2
    have hn : 0≤C*(R+2)^n := by positivity
    rw [positiveTestPower_succ_eq]
    change ‖positiveTestPower 1 ψ t‖≤_ ∧ _
    refine ⟨?_,?_,?_⟩
    · calc
        _ ≤ R*‖ψ t‖ := b0
        _ ≤ R*(C*(R+2)^n) := mul_le_mul_of_nonneg_left i0 hR
        _ ≤ C*(R+2)^(n+1) := by rw [pow_succ]; nlinarith
    · rw [positiveTestPower_one_deriv]
      change ‖positiveTestPower 1 (positiveSmoothTestDeriv ψ) t+ψ t‖≤_
      calc
        _ ≤ ‖positiveTestPower 1 (positiveSmoothTestDeriv ψ) t‖+‖ψ t‖ := norm_add_le _ _
        _ ≤ R*(C*(R+2)^n)+C*(R+2)^n := add_le_add
          (b1.trans (mul_le_mul_of_nonneg_left i1 hR)) i0
        _ ≤ C*(R+2)^(n+1) := by rw [pow_succ]; nlinarith
    · rw [positiveTestPower_one_second]
      change ‖positiveTestPower 1 (positiveSmoothTestDeriv (positiveSmoothTestDeriv ψ)) t+
        (2:ℝ)*positiveSmoothTestDeriv ψ t‖≤_
      calc
        _ ≤ ‖positiveTestPower 1 (positiveSmoothTestDeriv (positiveSmoothTestDeriv ψ)) t‖+
          ‖(2:ℝ)*positiveSmoothTestDeriv ψ t‖ := norm_add_le _ _
        _ ≤ R*(C*(R+2)^n)+2*(C*(R+2)^n) := by
          rw [norm_mul,show ‖(2:ℝ)‖=2 by norm_num]
          exact add_le_add (b2.trans (mul_le_mul_of_nonneg_left i2 hR))
            (mul_le_mul_of_nonneg_left i1 (by norm_num))
        _ = C*(R+2)^(n+1) := by rw [pow_succ]; ring

/-- Every fixed positive smooth test has exponential bounds for the first
two derivatives of all its polynomially weighted tests. -/
theorem positiveTestPower_exists_two_derivative_bound (φ : PositiveSmoothTest) :
    ∃ C R : ℝ,0≤C ∧ 0≤R ∧ ∀ n t,
      ‖positiveTestPower n φ t‖≤C*R^n ∧
      ‖positiveSmoothTestDeriv (positiveTestPower n φ) t‖≤C*R^n ∧
      ‖positiveSmoothTestDeriv (positiveSmoothTestDeriv (positiveTestPower n φ)) t‖≤C*R^n := by
  obtain ⟨C0,h0⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
  obtain ⟨C1,h1⟩ := (positiveSmoothTestDeriv φ).hasCompactSupport.exists_bound_of_continuous
    (positiveSmoothTestDeriv φ).continuous
  obtain ⟨C2,h2⟩ := (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)).hasCompactSupport.exists_bound_of_continuous
    (positiveSmoothTestDeriv (positiveSmoothTestDeriv φ)).continuous
  let C := |C0|+|C1|+|C2|
  let I := positiveSmoothTestInterval φ
  have hc : 0≤C := by positivity
  refine ⟨C,I.right+2,hc,by linarith [I.right_nonneg],?_⟩
  apply positiveTestPower_two_derivative_bound φ C I.right hc I.right_nonneg
  · intro t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (le_trans I.left_pos.le (I.subset ht).1)]
    exact (I.subset ht).2
  · intro t; exact (h0 t).trans (by dsimp [C]; linarith [le_abs_self C0,abs_nonneg C1,abs_nonneg C2])
  · intro t; exact (h1 t).trans (by dsimp [C]; linarith [le_abs_self C1,abs_nonneg C0,abs_nonneg C2])
  · intro t; exact (h2 t).trans (by dsimp [C]; linarith [le_abs_self C2,abs_nonneg C0,abs_nonneg C1])

#print axioms positiveTestPower_two_derivative_bound
#print axioms positiveTestPower_exists_two_derivative_bound

end QuantitativeMaass
