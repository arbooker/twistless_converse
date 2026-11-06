module

public import SmallLevelThirtyFourGridWordRowsV1
public import SmallLevelTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct FinitenessRamanujanFourier
open SmallLevelAdditive SmallLevelTaylor Complex Set MeasureTheory
open SmallLevelThirtyFourGroup (W)
open scoped MatrixGroups ModularForm

/-- Literal coherent physical laws, supplied for every original solution. -/
def GridFrickeLaws (k : ℕ) (f : ℕ→ℂ) (ε : ℂ) : Prop :=
  ∀ q : ℕ, 0<q → ∀ z : ℂ, 0<z.im →
    FinitenessAnalyticReconstruction.twist (fourier (fullCoefficients f k)) q z=
      (root 34 f q*ε*Complex.I^k)/(((Real.sqrt (Nat.lcm 34 (q^2)):ℂ)*z)^k)*
        FinitenessAnalyticReconstruction.twist (fourier (fullCoefficients f k)) q
          (-1/((Nat.lcm 34 (q^2):ℕ)*z))

theorem original_grid_fricke_laws {k : ℕ} {f : ℕ→ℂ} (hf : IsSolution 34 k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ GridFrickeLaws k f ε :=
  FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<34) hf

theorem grid_physical_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    ε*Complex.I^(2*m)=1 ∨ ε*Complex.I^(2*m)= -1 := by
  have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,Complex.I_sq]
  rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [hi,h]

theorem grid_fricke_of_laws (m : ℕ) {f : ℕ→ℂ} {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      (ε*Complex.I^(2*m)) • SmallLevelOriginal.fourierFunction (2*m) f := by
  have h:=fricke_law 34 (2*m) (by decide)
    (fourier (fullCoefficients f (2*m))) (ε*Complex.I^(2*m)) (by
      intro z hz
      simpa [root,FinitenessAnalyticReconstruction.twist,Finset.sum_range_succ] using hlaw 1 (by decide) z hz)
  change SmallLevelOriginal.fourierFunction (2*m) f=(ε*Complex.I^(2*m)) •
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W) at h
  rcases grid_physical_sign m hε with hc|hc
  · rw [hc] at h ⊢; simpa using h.symm
  · rw [hc] at h ⊢
    simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm

/-- All-order Ramanujan Taylor rows retain the explicitly supplied coherent
sign, so their sign cannot be chosen independently of the matrix rows. -/
theorem grid_twisted_taylor_of_laws (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 34 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (q : ℕ) (hq : 0<q) (r : ℝ) (hr : r≠0) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 34 (q^2)) r (root 34 f q*ε*Complex.I^(2*m)) M))
        {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        transform (fullCoefficients (twisted f q) (2*m)) r s-
          (root 34 f q*ε*Complex.I^(2*m))*
            (((Nat.lcm 34 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
            normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
              (Nat.lcm 34 (q^2)) r M s=
          mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
            (Nat.lcm 34 (q^2)) r (root 34 f q*ε*Complex.I^(2*m)) M) s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hL : 0<Nat.lcm 34 (q^2):=Nat.lcm_pos (by decide) (pow_pos hq _)
  apply normalized_taylor_mellin_rows (by exact_mod_cast hL) hr (2*m) (even_two_mul m)
    (polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) (2*m))
    (fullCoefficients_zero (twisted_zero hf.zero q) (2*m)) (root 34 f q*ε*Complex.I^(2*m))
  intro z hz
  have hreflect : 0<(-1/((Nat.lcm 34 (q^2):ℕ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (Nat.lcm 34 (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [Complex.ofReal_natCast,fourier_twisted hf.zero hg q (2*m) hz,
    fourier_twisted hf.zero hg q (2*m) hreflect] using hlaw q hq z hz

theorem grid_ramanujan_taylor_of_laws (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 34 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (q : ℕ) (hq : 0<q) (r : ℝ) (hr : r≠0) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 34 (q^2)) r (root 34 f q*ε*Complex.I^(2*m)) M))
        {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        ramanujanAdditive (2*m) f q r s-
          (root 34 f q*ε*Complex.I^(2*m))*
            (((Nat.lcm 34 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
            ramanujanTaylorSum (2*m) f q (Nat.lcm 34 (q^2)) r M s=
          mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
            (Nat.lcm 34 (q^2)) r (root 34 f q*ε*Complex.I^(2*m)) M) s := by
  obtain ⟨B,hB⟩:=grid_twisted_taylor_of_laws m hf hlaw q hq r hr
  obtain ⟨C,hC⟩:=ramanujan_additive_sum hf q
  refine ⟨max B C,?_⟩
  intro M
  constructor
  · intro s hs
    apply (hB M).1 s
    change max B C-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    linarith [le_max_left B C]
  · intro s hs
    have hsB : B<s.re:=lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : C<s.re:=lt_of_le_of_lt (le_max_right _ _) hs
    have hm:=(hB M).2 s hsB
    rw [hC r s hsC] at hm
    have he : normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 34 (q^2)) r M s=ramanujanTaylorSum (2*m) f q (Nat.lcm 34 (q^2)) r M s := by
      unfold normalizedTaylorSum ramanujanTaylorSum ramanujanAdditive
      apply Finset.sum_congr rfl
      intro n _
      rw [hC _ (s+(n:ℂ)) (by
        simp only [Complex.add_re,Complex.natCast_re]
        exact lt_of_lt_of_le hsC (le_add_of_nonneg_right (Nat.cast_nonneg n)))]
    rw [he] at hm
    exact hm

#print axioms original_grid_fricke_laws
#print axioms grid_fricke_of_laws
#print axioms grid_ramanujan_taylor_of_laws
end SmallLevelThirtyFourGrid
