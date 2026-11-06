module

public import QuantitativeArithmeticMatrixInfinityMellinTheoryV4
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4
public import SmallLevelOddWordsV1
public import SmallLevelOriginalTaylorRowsV1
public import SmallLevelTaylorTheoryV4
public import SmallLevelThirtySixFourierV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveOriginalRowsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyFive
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct FinitenessRamanujanFourier
open SmallLevelTaylor Complex MeasureTheory
open scoped MatrixGroups ModularForm

def knownTwo : SL(2,ℤ) := ⟨!![2,-1;-25,13],by decide⟩

theorem knownTwo_factorization : knownTwo = (oddMatrix 25 13 (by decide))⁻¹ := by decide

theorem original_knownTwo {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 25 k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] knownTwo =
      SmallLevelOriginal.fourierFunction k f := by
  rw [knownTwo_factorization]
  exact (slashStabilizer (k:ℤ) (SmallLevelOriginal.fourierFunction k f)).inv_mem
    (original_odd (by decide) (by decide : 2*13=25+1) (by decide) hf)

/-- Every exact transformation used by the 150-grid word rows follows
from the untwisted and modulus-two Fricke laws, uniformly in eigenvalues. -/
theorem original_word {m : ℕ} {f : ℕ → ℂ} (hf : IsSolution 25 (2*m) f)
    (w : List (Fin 7)) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      oddWord 25 13 (by decide) w = SmallLevelOriginal.fourierFunction (2*m) f := by
  exact oddWord_mem 25 13 (by decide)
    (slashStabilizer ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f))
    (original_T _ _) (original_lower (by decide) hf)
    (SmallLevelThirtySix.slash_neg_one_even _ m)
    (original_odd (by decide) (by decide : 2*13=25+1) (by decide) hf) w

/-- The highly ramified local factor makes every Ramanujan root correction
trivial at level25, including moduli divisible by five. -/
theorem twist_root_one (f : ℕ → ℂ) (q : ℕ) : root 25 f q = 1 := by
  unfold root
  apply Finset.prod_eq_one
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hbad : ¬ (p ∣ 25 ∧ ¬ p^2 ∣ 25) := by
    rintro ⟨hp25,hpsq⟩
    have hp5 : p ∣ 5 := hprime.dvd_of_dvd_pow (by simpa using hp25 : p ∣ 5^2)
    have he : p=5 := (Nat.prime_dvd_prime_iff_eq hprime (by decide)).mp hp5
    subst p
    exact hpsq (by decide)
  simp only [FinitenessNormalizedTwistLocal.sign,hbad,ite_false,ite_self]

theorem original_complete_five_zero {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 25 k f)
    {z : ℂ} (hz : 0 < z.im) :
    QuantitativeArithmeticRetainedReconstruction.completeTwist
      (fourier (fullCoefficients f k)) 5 z = 0 :=
  SmallLevelThirtySix.square_prime_average_zero hf.toEulerData (by decide) (by decide) k hz

/-- All Taylor sources carry one original sign, with no additional
character-twist continuation or restriction on the Hecke eigenvalues. -/
theorem original_taylor_source {k : ℕ} (hk : Even k) {f : ℕ → ℂ}
    (hf : IsSolution 25 k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm 25 (q^2)) r (ε*Complex.I^k) M))
          {s : ℂ | B-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, B<s.re →
          SmallLevelAdditive.transform (fullCoefficients (twisted f q) k) r s-
            (ε*Complex.I^k)*(((Nat.lcm 25 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
              normalizedTaylorSum k (fullCoefficients (twisted f q) k) (Nat.lcm 25 (q^2)) r M s=
            mellin (frickeError k (fullCoefficients (twisted f q) k)
              (Nat.lcm 25 (q^2)) r (ε*Complex.I^k) M) s := by
  simpa only [twist_root_one,one_mul] using
    original_ramanujan_taylor_rows (by decide : 0<25) hk hf

#print axioms original_knownTwo
#print axioms original_word
#print axioms twist_root_one
#print axioms original_complete_five_zero
#print axioms original_taylor_source
end QuantitativeArithmeticSmallLevelTwentyFive
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxiliaryRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyFive
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticRetainedReconstruction

def entireSpecs : Fin 12 → ℕ := ![1,2,3,5,6,10,15,25,30,50,75,150]

theorem entireSpecs_valid : ∀ i : Fin 12, 0<entireSpecs i ∧ entireSpecs i ∣ 150 := by decide

/-- All twelve entire Ramanujan rows of the complete150-grid certificate,
with one common initial half-plane and literal original Euler input. -/
theorem original_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : IsSolution 25 k f) :
    (∀ i : Fin 12, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 25 k f (entireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 12, ∀ s : ℂ, B<s.re →
        ramanujanEntire 25 k f (entireSpecs i) s=gridSum k f 150 (entireSpecs i) 0 s := by
  have hh (i : Fin 12) := original_ramanujan_entire (by decide : 0<25) hk hf (entireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
    rw [hb i s (lt_of_le_of_lt hbi hs)]
    have hg := ramanujanAdditive_grid k f (by decide : 0<150)
      (entireSpecs_valid i).1 (entireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

/-- The p=5 row has identically zero eigenvalue and no second Euler term.
It is proved directly by Mellin integration of the complete average. -/
theorem original_additive_five_zero {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 25 k f) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range 5, original k f (r+(j:ℝ)/5) s)=0 := by
  obtain ⟨σ,_,hg⟩ := hf.growth
  obtain ⟨B,hB⟩ := additive_convergence_halfplane
    (polynomial_bound hf.zero hg k) (fullCoefficients_zero hf.zero k)
  refine ⟨B,fun r s hs => ?_⟩
  let a := fullCoefficients f k
  have he : EqOn
      (fun y : ℝ => ∑ j∈Finset.range 5, fourier a (((r+(j:ℝ)/5:ℝ):ℂ)+(y:ℂ)*I))
      (fun _ => 0) (Ioi 0) := by
    intro y hy
    have hh := original_complete_five_zero hf (z := (r:ℂ)+(y:ℂ)*I) (by simpa using hy)
    change completeTwist (fourier a) 5 ((r:ℂ)+(y:ℂ)*I)=0 at hh
    rw [← hh]
    unfold completeTwist
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  have hsum : mellin
      (fun y : ℝ => ∑ j∈Finset.range 5, fourier a (((r+(j:ℝ)/5:ℝ):ℂ)+(y:ℂ)*I)) s=
      ∑ j∈Finset.range 5, original k f (r+(j:ℝ)/5) s := by
    unfold mellin
    simp only [Finset.smul_sum]
    rw [integral_finsetSum (Finset.range 5) (fun j _ => (hB (r+(j:ℝ)/5) s hs).1)]
    apply Finset.sum_congr rfl
    intro j _
    exact (hB (r+(j:ℝ)/5) s hs).2
  rw [← hsum,mellin_congr_positive he s]
  simp [mellin]

theorem original_five_grid {k : ℕ} {f : ℕ → ℂ} (hf : IsSolution 25 k f) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re →
      (∑ t∈Finset.range 5, grid k f 150 (j+30*(t:ℤ)) s)=0 := by
  obtain ⟨B,hB⟩ := original_additive_five_zero hf
  refine ⟨B,fun j s hs => ?_⟩
  have he := hB ((j:ℝ)/150) s hs
  convert he using 1
  apply Finset.sum_congr rfl
  intro t _
  unfold grid
  congr 1
  push_cast
  ring

#print axioms original_entire_rows
#print axioms original_additive_five_zero
#print axioms original_five_grid
end QuantitativeArithmeticSmallLevelTwentyFive
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveWordTaylorV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyFive
open Matrix ModularGroup UpperHalfPlane SmallLevelGenerators SmallLevelOriginal SmallLevelAdditive
open FinitenessOriginalFourier FinitenessFourierConstruction MeasureTheory
open scoped MatrixGroups ModularForm

theorem invariant_matrix_fourier (k : ℕ) (f : ℕ → ℂ) (g : SL(2,ℤ))
    (hg : fourierFunction k f ∣[(k:ℤ)] g=fourierFunction k f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f k) z=
      1/(((g.val 1 0:ℤ):ℂ)*z+((g.val 1 1:ℤ):ℂ))^k*
        fourier (fullCoefficients f k)
          ((((g.val 0 0:ℤ):ℂ)*z+((g.val 0 1:ℤ):ℂ))/
            (((g.val 1 0:ℤ):ℂ)*z+((g.val 1 1:ℤ):ℂ))) := by
  have h := congrFun hg ⟨z,hz⟩
  rw [ModularForm.SL_slash_apply] at h
  simp only [fourierFunction,coe_specialLinearGroup_apply,zpow_neg,zpow_natCast] at h
  norm_num [denom,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe] at h
  simpa only [one_div,mul_comm] using h.symm

/-- Every non-affine, finite-target word row in the continuation
certificate is an actual all-order Taylor identity, before any continuation. -/
theorem original_word_taylor {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (w : List (Fin 7))
    (hC : ((oddWord 25 13 (by decide) w).val 1 0:ℝ)≠0)
    (r : ℝ) (hr : ((oddWord 25 13 (by decide) w).val 1 0:ℝ)*r+
      ((oddWord 25 13 (by decide) w).val 1 1:ℝ)≠0) :
    let g := oddWord 25 13 (by decide) w
    let A : ℝ := g.val 0 0
    let B : ℝ := g.val 0 1
    let C : ℝ := g.val 1 0
    let D : ℝ := g.val 1 1
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform (fullCoefficients f (2*m)) r s-
          (((C*r+D)^2:ℝ):ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*((C*(C*r+D):ℝ):ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            transform (fullCoefficients f (2*m)) ((A*r+B)/(C*r+D))
              (s+(n:ℂ)))=error M s := by
  let g := oddWord 25 13 (by decide) w
  obtain ⟨σ,_,hg⟩ := hf.growth
  have hdetZ : g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hdet : (g.val 0 0:ℝ)*(g.val 1 1:ℝ)-(g.val 0 1:ℝ)*(g.val 1 0:ℝ)=1 := by
    exact_mod_cast hdetZ
  have hF := invariant_matrix_fourier (2*m) f g (original_word hf w)
  have he := QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m)) m
    (g.val 0 0:ℝ) (g.val 0 1:ℝ) (g.val 1 0:ℝ) (g.val 1 1:ℝ) r hC
    (by rw [hdet]; norm_num) hr 1
    (by simpa only [hdet,Complex.ofReal_one,one_pow,mul_one,Complex.ofReal_intCast] using hF)
  simpa only [hdet,div_one,one_mul] using he

/-- A word sending a source cusp to infinity supplies an entire extension
of its additive twist. This is the actual source of the singleton rows. -/
theorem original_word_infinity {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (w : List (Fin 7))
    (hC : ((oddWord 25 13 (by decide) w).val 1 0:ℝ)≠0)
    (r : ℝ) (hr : ((oddWord 25 13 (by decide) w).val 1 0:ℝ)*r+
      ((oddWord 25 13 (by decide) w).val 1 1:ℝ)=0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∃ B : ℝ,
      ∀ s : ℂ, B<s.re → G s=original (2*m) f r s := by
  let g := oddWord 25 13 (by decide) w
  obtain ⟨σ,_,hg⟩ := hf.growth
  have ha := polynomial_bound hf.zero hg (2*m)
  have ha0 := fullCoefficients_zero hf.zero (2*m)
  have hdetZ : g.val 0 0*g.val 1 1-g.val 0 1*g.val 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hdet : (g.val 0 0:ℝ)*(g.val 1 1:ℝ)-(g.val 0 1:ℝ)*(g.val 1 0:ℝ)=1 := by
    exact_mod_cast hdetZ
  have hF := invariant_matrix_fourier (2*m) f g (original_word hf w)
  have he := QuantitativeArithmeticMatrixInfinityMellin.matrix_source_entire ha ha0 (2*m)
    (by omega) (g.val 0 0:ℝ) (g.val 0 1:ℝ) (g.val 1 0:ℝ) (g.val 1 1:ℝ) r hC
    (by rw [hdet]; norm_num) hr 1 (by norm_num)
    (by simpa only [Complex.ofReal_intCast] using hF)
  obtain ⟨B,hB⟩ := SmallLevelTaylor.additive_convergence_halfplane ha ha0
  exact ⟨_,he,B,fun s hs => (hB r s hs).2⟩

#print axioms original_word_taylor
#print axioms original_word_infinity
end QuantitativeArithmeticSmallLevelTwentyFive
end
end
