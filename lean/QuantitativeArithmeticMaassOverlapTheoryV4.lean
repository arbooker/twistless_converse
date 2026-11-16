module

public import AsymptoticCongruenceStripV1
public import Mathlib.Tactic
public import QuantitativeMaassQuotientLocalL2V1
public import QuantitativeMaassRadialKernelSymmetryV1

/-! Consolidated chapter: QuantitativeArithmeticMaassOverlap. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticMaassOverlapGeometryV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix
open scoped MatrixGroups

namespace QuantitativeArithmeticMaassOverlap

/-- The bottom-row Euclidean norm is controlled by hyperbolic displacement.
This uses the actual integral modular action. -/
theorem bottom_row_sq_le_exp (A : SL(2,ℤ)) :
    (A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2 ≤ Real.exp (dist (A • I) I) := by
  have hD : Complex.normSq (denom (A : GL (Fin 2) ℝ) I) =
      (A 1 0 : ℝ)^2 + (A 1 1 : ℝ)^2 := by
    simp [denom, Complex.normSq, pow_two, add_comm]
  have hpos : 0 < Complex.normSq (denom (A : GL (Fin 2) ℝ) I) :=
    normSq_denom_pos _ (by simp)
  have h := im_le_im_mul_exp_dist I (A • I)
  rw [ModularGroup.im_smul_eq_div_normSq] at h
  simp only [I_im, dist_comm I (A • I), div_mul_eq_mul_div, one_mul] at h
  have hh := (le_div_iff₀ hpos).mp h
  simpa only [one_mul, hD] using hh

/-- Each integral entry is at most exp(T) when displacement of i is at most 2T. -/
theorem entry_abs_le_exp (A : SL(2,ℤ)) (T : ℝ)
    (hA : dist (A • I) I ≤ 2*T) (i j : Fin 2) :
    |(A i j : ℝ)| ≤ Real.exp T := by
  have hSI : ModularGroup.S • I = I := by
    rw [modular_S_smul]
    apply UpperHalfPlane.ext
    simp
  have hSA : dist ((ModularGroup.S*A) • I) I = dist (A • I) I := by
    rw [mul_smul]
    simpa only [hSI] using QuantitativeMaass.integral_action_dist ModularGroup.S (A • I) I
  have hbottom := (bottom_row_sq_le_exp A).trans (Real.exp_le_exp.mpr hA)
  have htop := bottom_row_sq_le_exp (ModularGroup.S*A)
  rw [hSA] at htop
  have htop' : (A 0 0 : ℝ)^2 + (A 0 1 : ℝ)^2 ≤ Real.exp (2*T) := by
    convert htop.trans (Real.exp_le_exp.mpr hA) using 1
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, ModularGroup.S]
  have hexp : Real.exp (2*T) = (Real.exp T)^2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [hexp] at hbottom htop'
  have hsq : (A i j : ℝ)^2 ≤ (Real.exp T)^2 := by
    fin_cases i <;> fin_cases j
    · change (A 0 0 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 0 1 : ℝ)]
    · change (A 0 1 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 0 0 : ℝ)]
    · change (A 1 0 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 1 1 : ℝ)]
    · change (A 1 1 : ℝ)^2 ≤ _
      nlinarith [sq_nonneg (A 1 0 : ℝ)]
  have habsq : |(A i j : ℝ)|^2 = (A i j : ℝ)^2 := sq_abs _
  nlinarith [abs_nonneg (A i j : ℝ), Real.exp_pos T]

#print axioms bottom_row_sq_le_exp
#print axioms entry_abs_le_exp
end QuantitativeArithmeticMaassOverlap
end
end

/-! ## QuantitativeArithmeticMaassOverlapBoxV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix AsymptoticCongruenceStrip
open scoped MatrixGroups

namespace QuantitativeArithmeticMaassOverlap

/-- The chosen integral representative is injective on the actual projective
congruence group; no double counting of scalar matrix labels is introduced. -/
theorem representative_injective (N : ℕ) :
    Function.Injective (representative (N := N)) := by
  intro g h he
  apply Subtype.ext
  have hh := congrArg AsymptoticCongruenceLabels.integralLabel he
  simpa only [representative_label] using hh

/-- A literal entry-box count for finite subsets of the projective group.
The bound is uniform in the congruence level. -/
theorem gamma_entry_card_bound (N B : ℕ) (S : Finset (gamma N))
    (hS : ∀ g∈S, ∀ i j : Fin 2,
      |((representative g) i j : ℤ)| ≤ (B : ℤ)) :
    S.card ≤ (2*B+1)^4 := by
  classical
  let J : Finset ℤ := Finset.Icc (-(B : ℤ)) B
  let enc : S → (Fin 2 → Fin 2 → J) := fun g i j =>
    ⟨representative g.val i j, Finset.mem_Icc.mpr (abs_le.mp (hS g.val g.property i j))⟩
  have hinj : Function.Injective enc := by
    intro g h he
    apply Subtype.ext
    apply representative_injective N
    apply Subtype.ext
    funext i j
    exact congrArg Subtype.val (congrFun (congrFun he i) j)
  have hcard : Fintype.card J = 2*B+1 := by
    simp only [Fintype.card_coe, J, Int.card_Icc]
    omega
  have hc := Fintype.card_le_of_injective enc hinj
  rw [Fintype.card_pi_const, Fintype.card_pi_const, hcard] at hc
  simpa only [Fintype.card_coe, ← pow_mul] using hc

#print axioms representative_injective
#print axioms gamma_entry_card_bound
end QuantitativeArithmeticMaassOverlap
end
end

/-! ## QuantitativeArithmeticMaassOverlapEnergySupportV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuantitativeArithmeticMaassOverlap
open QuantitativeMaass

/-- The fixed-support square bound with its proved overlap multiplicity supplied explicitly. -/
theorem compact_poincare_square_bound_of_overlap {G A : Type*} [Group G]
    [TopologicalSpace A] [MulAction G A] [ProperlyDiscontinuousSMul G A]
    (K : Set A) (hK : IsCompact K) (M : ℕ)
    (hM : ∀ x : A, ∀ S : Finset G, (∀ g∈S, g•x∈K) → S.card≤M) :
    ∀ f : A → ℂ, Function.support f ⊆ K → ∀ x,
      ‖poincareSum (G := G) f x‖^2≤(M:ℝ)*∑' g : G, ‖f (g•x)‖^2 := by
  classical
  intro f hf x
  let hS := compact_orbit_point_finite (G := G) K hK x
  let S := hS.toFinset
  have hout (g : G) (hg : g∉S) : f (g•x)=0 := by
    by_contra hne
    exact hg (hS.mem_toFinset.mpr (hf hne))
  have hcard : S.card≤M := hM x S (fun g hg => hS.mem_toFinset.mp hg)
  have hp : poincareSum (G := G) f x=∑ g∈S, f (g•x) := tsum_eq_sum hout
  have hq : (∑' g : G, ‖f (g•x)‖^2)=∑ g∈S, ‖f (g•x)‖^2 :=
    tsum_eq_sum (fun g hg => by simp [hout g hg])
  rw [hp,hq]
  calc
    ‖∑ g∈S, f (g•x)‖^2 ≤ (∑ g∈S, ‖f (g•x)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (S.card:ℝ)*∑ g∈S, ‖f (g•x)‖^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The existing quotient-unfolding energy argument retains the supplied explicit multiplicity. -/
theorem compact_poincare_energy_bound_of_overlap {G A : Type*} [Group G] [Countable G]
    [TopologicalSpace A] [MeasurableSpace A] [MulAction G A]
    [ProperlyDiscontinuousSMul G A]
    (μ : Measure A) (hmp : ∀ g : G, MeasurePreserving (fun x : A => g•x) μ μ)
    (ρ : A → ℝ≥0∞) (hρ : Measurable ρ) (hn : ∀ x, ∑' g : G, ρ (g•x)=1)
    (K : Set A) (hK : IsCompact K) (M : ℕ)
    (hM : ∀ x : A, ∀ S : Finset G, (∀ g∈S, g•x∈K) → S.card≤M) :
    ∀ f : A → ℂ, Measurable f → Function.support f ⊆ K →
      (∫⁻ x, ENNReal.ofReal (‖poincareSum (G := G) f x‖^2) ∂μ.withDensity ρ)≤
        (M:ℝ≥0∞)*∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ := by
  classical
  have hsquare := compact_poincare_square_bound_of_overlap K hK M hM
  intro f hm hf
  have hpoint (x : A) : ENNReal.ofReal (‖poincareSum (G := G) f x‖^2)≤
      (M:ℝ≥0∞)*∑' g : G, ENNReal.ofReal (‖f (g•x)‖^2) := by
    have hs : Summable (fun g : G => ‖f (g•x)‖^2) := by
      apply summable_of_hasFiniteSupport
      apply (compact_orbit_point_finite (G := G) K hK x).subset
      intro g hg
      apply hf
      intro hz
      exact hg (by simp [hz])
    have hb := ENNReal.ofReal_le_ofReal (hsquare f hf x)
    rwa [ENNReal.ofReal_mul (Nat.cast_nonneg M),ENNReal.ofReal_natCast,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs] at hb
  calc
    _ ≤ ∫⁻ x, (M:ℝ≥0∞)*∑' g : G, ENNReal.ofReal (‖f (g•x)‖^2) ∂μ.withDensity ρ :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp),
        lintegral_poincare_unfold μ hmp ρ hρ hn _ (hm.norm.pow_const 2).ennreal_ofReal]

#print axioms compact_poincare_square_bound_of_overlap
#print axioms compact_poincare_energy_bound_of_overlap

end QuantitativeArithmeticMaassOverlap
end
end

/-! ## QuantitativeArithmeticMaassOverlapV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open UpperHalfPlane Matrix AsymptoticCongruenceStrip
open scoped MatrixGroups

namespace QuantitativeArithmeticMaassOverlap

/-- An explicit integer-box multiplicity for translates of a hyperbolic ball.
The level is positive, B is natural, and its only size condition is numerical.
The relative translates and their integral representatives are constructed
inside the actual projective congruence group used by quotientMeasure. -/
theorem ball_overlap_bound (N : ℕ) [NeZero N] (o : ℍ) (U : ℝ) (B : ℕ)
    (hB : Real.exp (U + dist o I) ≤ (B : ℝ))
    (x : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S, dist (g • x) o ≤ U) : S.card ≤ (2*B+1)^4 := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨g₀,hg₀⟩ := hne
    let rel : gamma N → gamma N := fun g => g*g₀⁻¹
    have hrel : Function.Injective rel := (Equiv.mulRight g₀⁻¹).injective
    have hbox : ∀ g∈S.image rel, ∀ i j : Fin 2,
        |((representative g) i j : ℤ)| ≤ (B : ℤ) := by
      intro d hd i j
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
      have hy : dist (g₀ • x) I ≤ U+dist o I :=
        (dist_triangle (g₀ • x) o I).trans (add_le_add (hS g₀ hg₀) le_rfl)
      have hz : dist (g • x) I ≤ U+dist o I :=
        (dist_triangle (g • x) o I).trans (add_le_add (hS g hg) le_rfl)
      have he : rel g • (g₀ • x) = g • x := by
        simp only [rel, mul_smul, inv_smul_smul]
      have hd : dist (rel g • I) I ≤ 2*(U+dist o I) := by
        calc
          _ ≤ dist (rel g • I) (rel g • (g₀ • x)) +
              dist (rel g • (g₀ • x)) I := dist_triangle _ _ _
          _ = dist I (g₀ • x) + dist (g • x) I := by
            rw [QuantitativeMaass.congruence_action_dist, he]
          _ ≤ (U+dist o I)+(U+dist o I) :=
            add_le_add (by simpa only [dist_comm] using hy) hz
          _ = _ := by ring
      have ha : representative (rel g) • I = rel g • I := by
        rw [← integralLabel_action, representative_label]
        rfl
      have hb := entry_abs_le_exp (representative (rel g)) (U+dist o I)
        (by simpa only [ha] using hd) i j
      exact_mod_cast hb.trans hB
    have hc := gamma_entry_card_bound N B (S.image rel) hbox
    rwa [Finset.card_image_of_injective S hrel] at hc
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.zero_le]

/-- A closed formula replacing the unspecified compact overlap constant.
For radial kernels, use U=R+L. -/
theorem ball_overlap_explicit (N : ℕ) [NeZero N] (o : ℍ) (U : ℝ)
    (x : ℍ) (S : Finset (gamma N))
    (hS : ∀ g∈S, dist (g • x) o ≤ U) :
    S.card ≤ (2*⌈Real.exp (U + dist o I)⌉₊+1)^4 :=
  ball_overlap_bound N o U _ (Nat.le_ceil _) x S hS

#print axioms ball_overlap_bound
#print axioms ball_overlap_explicit
end QuantitativeArithmeticMaassOverlap
end
end
