module

public import FinitenessOriginalTwistedContinuationsV1
public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelRamanujanAdditiveV1
public import SmallLevelTaylorRowNormalizationV1
public import SmallLevelTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticCoherentTaylor. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelCoherentTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticCoherentTaylor
open SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessFourierConstruction

/-- The actual Fourier transformation laws, retaining the original common sign. -/
def CoherentLaw (N k : ℕ) (f : ℕ → ℂ) (ε : ℂ) : Prop :=
  ∀ q : ℕ, 0<q → ∀ z : ℂ, 0<z.im →
    FinitenessAnalyticReconstruction.twist
      (fourier (fullCoefficients f k)) q z=
    (root N f q*ε*I^k)/((((Real.sqrt (Nat.lcm N (q^2)):ℝ):ℂ)*z)^k)*
      FinitenessAnalyticReconstruction.twist
        (fourier (fullCoefficients f k)) q (-1/((Nat.lcm N (q^2):ℕ)*z))

theorem original_coherent_law {N k : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ CoherentLaw N k f ε :=
  FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf

/-- The paper's full Taylor--Fricke identity for every positive Ramanujan
modulus, every nonzero real translation, and every Taylor order. All analytic
bounds and the transformation law follow from the original Euler input.
The sign is chosen once, before q, and zero twists are included. -/
theorem ramanujan_taylor_rows_of_law {N k : ℕ} (hN : 0<N) (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) (ε : ℂ)
    (hlaw : CoherentLaw N k f ε) :
    ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M))
          {s : ℂ | B-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          SmallLevelAdditive.transform (fullCoefficients (twisted f q) k) r s-
            (root N f q*ε*I^k)*(((Nat.lcm N (q^2):ℝ)*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
              normalizedTaylorSum k (fullCoefficients (twisted f q) k) (Nat.lcm N (q^2)) r M s=
            mellin (frickeError k (fullCoefficients (twisted f q) k)
              (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  intro q hq r hr
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  apply normalized_taylor_mellin_rows (by exact_mod_cast hL) hr k hk
    (polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k)
    (fullCoefficients_zero (twisted_zero hf.zero q) k) (root N f q*ε*I^k)
  intro z hz
  have hreflect : 0<(-1/((Nat.lcm N (q^2):ℕ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [Complex.ofReal_natCast,fourier_twisted hf.zero hg q k hz,
    fourier_twisted hf.zero hg q k hreflect] using hlaw q hq z hz

#print axioms original_coherent_law
#print axioms ramanujan_taylor_rows_of_law
end QuantitativeArithmeticCoherentTaylor
end
end

/-! ## QuantitativeArithmeticSmallLevelCoherentAdditiveV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticCoherentTaylor
open SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessRamanujanSum FinitenessFourierConstruction FinitenessAnalyticReconstruction

/-- The full manuscript Taylor--Fricke row, with every twist expanded as
an explicit primitive finite sum of the original additive transforms. -/
theorem finite_sum_taylor_rows_of_law {N k : ℕ} (hN : 0<N) (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) (ε : ℂ)
    (hlaw : CoherentLaw N k f ε) :
    ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) r (FinitenessNormalizedTwistProduct.root N f q*ε*I^k) M))
          {s : ℂ | B-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          ramanujanAdditive k f q r s-
            (FinitenessNormalizedTwistProduct.root N f q*ε*I^k)*
              (((Nat.lcm N (q^2):ℝ)*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
              ramanujanTaylorSum k f q (Nat.lcm N (q^2)) r M s=
            mellin (frickeError k (fullCoefficients (twisted f q) k)
              (Nat.lcm N (q^2)) r (FinitenessNormalizedTwistProduct.root N f q*ε*I^k) M) s := by
  have hrows := ramanujan_taylor_rows_of_law hN hk hf ε hlaw
  intro q hq r hr
  obtain ⟨B,hB⟩ := hrows q hq r hr
  obtain ⟨C,hC⟩ := ramanujan_additive_sum hf q
  refine ⟨max B C,?_⟩
  intro M
  constructor
  · intro s hs
    apply (hB M).1 s
    change max B C-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    linarith [le_max_left B C]
  · intro s hs
    have hsB : B<s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : C<s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hm := (hB M).2 s hsB
    rw [hC r s hsC] at hm
    have he : normalizedTaylorSum k (fullCoefficients (twisted f q) k)
        (Nat.lcm N (q^2)) r M s=ramanujanTaylorSum k f q (Nat.lcm N (q^2)) r M s := by
      unfold normalizedTaylorSum ramanujanTaylorSum ramanujanAdditive
      apply Finset.sum_congr rfl
      intro n _
      rw [hC _ (s+(n:ℂ)) (by
        simp only [Complex.add_re,Complex.natCast_re]
        exact lt_of_lt_of_le hsC (le_add_of_nonneg_right (Nat.cast_nonneg n)))]
    rw [he] at hm
    exact hm

#print axioms finite_sum_taylor_rows_of_law
end QuantitativeArithmeticCoherentTaylor
end
end

/-! ## QuantitativeArithmeticSmallLevelCoherentGridV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticCoherentTaylor
open SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessRamanujanSum FinitenessNormalizedTwistProduct SmallLevelAdditive

/-- Actual closed-grid Taylor rows from the original Euler input. The
same finite target grid supplies every positive shift; no continuation
of its coordinates is assumed. Determinant/rank certificates are separate. -/
theorem closed_grid_taylor_rows_of_law {N k : ℕ} (hN : 0<N) (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) (ε : ℂ)
    (hlaw : CoherentLaw N k f ε) :
    ∀ Q q : ℕ, 0<Q → 0<q → q∣Q →
      ∀ t d : ℤ, t≠0 → (Nat.lcm N (q^2):ℤ)*d=(Q:ℤ)^2 → t∣d →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) ((t:ℝ)/(Q:ℝ)) (root N f q*ε*I^k) (M+1)))
          {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          gridSum k f Q q t s-
            taylorRowScalar k (Nat.lcm N (q^2)) ((t:ℝ)/(Q:ℝ)) (root N f q*ε*I^k) 0 s*
              gridSum k f Q q (- (d/t)) s=
            mellin (frickeError k (fullCoefficients (twisted f q) k)
              (Nat.lcm N (q^2)) ((t:ℝ)/(Q:ℝ)) (root N f q*ε*I^k) (M+1)) s+
            ∑ n∈Finset.range M,
              taylorRowScalar k (Nat.lcm N (q^2)) ((t:ℝ)/(Q:ℝ)) (root N f q*ε*I^k) (n+1) s*
                gridSum k f Q q (- (d/t)) (s+((n:ℂ)+1)) := by
  have hrows := finite_sum_taylor_rows_of_law hN hk hf ε hlaw
  intro Q q hQ hq hqQ t d ht hd htd
  have hr : (t:ℝ)/(Q:ℝ)≠0 := div_ne_zero (by exact_mod_cast ht) (by exact_mod_cast ne_of_gt hQ)
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  obtain ⟨B,hB⟩ := hrows q hq ((t:ℝ)/(Q:ℝ)) hr
  refine ⟨B,?_⟩
  intro M
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using (hB (M+1)).1
  · intro s hs
    have hm := (hB (M+1)).2 s hs
    rw [ramanujanTaylorSum_split] at hm
    rw [ramanujanAdditive_grid k f hQ hq hqQ,
      fricke_grid_partner hQ hL ht hd htd] at hm
    simp_rw [ramanujanAdditive_grid k f hQ hq hqQ] at hm
    simp only [Nat.cast_add,Nat.cast_one] at hm
    change gridSum k f Q q t s-(_*gridSum k f Q q (- (d/t)) s+_)=_ at hm
    unfold gridSum at hm ⊢
    linear_combination hm

#print axioms closed_grid_taylor_rows_of_law
end QuantitativeArithmeticCoherentTaylor
end
end

/-! ## QuantitativeArithmeticSmallLevelCoherentFrickeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticCoherentTaylor
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem fricke_sign_of_law {N : ℕ} (hN : 0<N) (m : ℕ) {f : ℕ → ℂ}
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) (hlaw : CoherentLaw N (2*m) f ε) :
    (ε*Complex.I^(2*m)=1 ∨ ε*Complex.I^(2*m)= -1) ∧
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke N hN=
        (ε*Complex.I^(2*m)) • SmallLevelOriginal.fourierFunction (2*m) f := by
  let χ : ℂ := ε*Complex.I^(2*m)
  have hχ : χ=1 ∨ χ= -1 := by
    have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul, Complex.I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [χ,hi,h]
  have h := fricke_law N (2*m) hN
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f (2*m))) χ (by
      intro z hz
      simpa [χ,FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
        Finset.sum_range_succ] using hlaw 1 (by decide) z hz)
  refine ⟨hχ,?_⟩
  change _=χ • _
  change SmallLevelOriginal.fourierFunction (2*m) f=χ •
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke N hN) at h
  rcases hχ with hc|hc
  · rw [hc] at h ⊢
    simpa using h.symm
  · rw [hc] at h ⊢
    simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm

#print axioms fricke_sign_of_law
end QuantitativeArithmeticCoherentTaylor
end
end
