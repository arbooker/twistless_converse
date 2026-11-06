module

public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticMatrixInfinityMellinTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4
public import SmallLevelAdditiveTheoryV4
public import SmallLevelContinuationTheoryV4
public import SmallLevelTaylorTheoryV4
public import SmallLevelTwentyOneAugmentedRatesV1
public import SmallLevelTwentyOneCoherentWordTaylorV1
public import SmallLevelTwentyOneIntegerWordRatesV1

/-! Consolidated chapter: SmallLevelTwentyOneFiniteGrid. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneFiniteGridWordsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFiniteGrid
open Complex Set Filter SmallLevelAdditive SmallLevelTaylor
open FinitenessOriginalFourier
open SmallLevelTwentyOneKnownWords
open scoped Topology

variable (Q : ℕ) (hQ : 0<Q)

def gridIndex (t : ℤ) : Fin Q :=
  ⟨(t%(Q:ℤ)).toNat,by
    have h := Int.emod_lt_of_pos t (show (0:ℤ)<Q by exact_mod_cast hQ)
    omega⟩

def gridVector (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : Fin Q → ℂ :=
  fun j => grid k f Q (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (t : ℤ) :
    gridVector Q k f s (gridIndex Q hQ t)=grid k f Q t s := by
  unfold gridVector
  have he : ((gridIndex Q hQ t).val:ℤ)=t%Q :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [he]
  exact grid_mod k f hQ t s


def wordDen (w : Word) (t : ℤ) : ℝ := coordC w*((t:ℝ)/Q)+coordD w

def wordCoefficient (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ) (n : ℕ) (s : ℂ) : ℂ :=
  character χ w*(((wordDen Q w t)^2:ℝ):ℂ)^(s-(m:ℂ))*
    (I*((coordC w*wordDen Q w t:ℝ):ℂ))^n*
      Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

theorem wordCoefficient_analytic (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ)
    (ht : wordDen Q w t≠0) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (wordCoefficient Q m χ w t n) z := by
  have hc : (((wordDen Q w t)^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ ht)
  have hp : AnalyticAt ℂ (fun s : ℂ => (((wordDen Q w t)^2:ℝ):ℂ)^(s-(m:ℂ))) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul
    (SmallLevelTaylor.binomial_shift_analytic (2*m) n z)

/-- Every word whose rational source and partner lie on the grid supplies
an actual row. The sign is the same one used for the Ramanujan rows. -/
theorem word_grid_rows_of_law {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (w : Word) (hC : coordC w≠0) (t u : ℤ) (ht : wordDen Q w t≠0)
    (hu : (coordA w*((t:ℝ)/Q)+coordB w)/wordDen Q w t=(u:ℝ)/Q) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector Q (2*m) f s (gridIndex Q hQ t)-
          wordCoefficient Q m (ε*I^(2*m)) w t 0 s*gridVector Q (2*m) f s (gridIndex Q hQ u)=
        error M s+∑ n∈Finset.range M,
          wordCoefficient Q m (ε*I^(2*m)) w t (n+1) s*
            gridVector Q (2*m) f (s+((n:ℂ)+1)) (gridIndex Q hQ u) := by
  obtain ⟨B,error,hrow⟩ := word_taylor_of_law hf ε hε hlaw w hC ((t:ℝ)/Q) ht
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrow (M+1)).1
  · intro s hs
    have he := (hrow (M+1)).2 s hs
    change _-character (ε*I^(2*m)) w*(((wordDen Q w t)^2:ℝ):ℂ)^(s-(m:ℂ))*
      (∑ n∈Finset.range (M+1), (I*((coordC w*wordDen Q w t:ℝ):ℂ))^n*
        Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
        transform (fullCoefficients f (2*m))
          ((coordA w*((t:ℝ)/Q)+coordB w)/wordDen Q w t) (s+(n:ℂ)))=_ at he
    rw [hu,Finset.sum_range_succ'] at he
    simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,
      Nat.cast_add,Nat.cast_one] at he
    simp only [gridVector_index,grid,original,wordCoefficient,Nat.cast_zero,add_zero,
      pow_zero,Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
    rw [mul_add,Finset.mul_sum] at he
    simp only [mul_assoc,one_mul] at he ⊢
    linear_combination he

/-- The complete family of closed group-word rows holds as germs on the
continued grid. Neither grid continuation nor the original sign is re-chosen. -/
theorem word_grid_germs_of_law {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin Q → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector Q (2*m) f z)
    (w : Word) (hC : coordC w≠0) (t u : ℤ) (ht : wordDen Q w t≠0)
    (hu : (coordA w*((t:ℝ)/Q)+coordB w)/wordDen Q w t=(u:ℝ)/Q) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ x : ℂ, B-((M:ℝ)+1)<x.re →
        (fun s => G s (gridIndex Q hQ t)-
          wordCoefficient Q m (ε*I^(2*m)) w t 0 s*G s (gridIndex Q hQ u)) =ᶠ[𝓝[≠] x]
        (fun s => error M s+∑ n∈Finset.range M,
          wordCoefficient Q m (ε*I^(2*m)) w t (n+1) s*
            G (s+((n:ℂ)+1)) (gridIndex Q hQ u)) := by
  obtain ⟨B,error,hrow⟩ := word_grid_rows_of_law Q hQ hf ε hε hlaw w hC t u ht hu
  refine ⟨B,error,?_⟩
  intro M
  refine ⟨(hrow M).1,?_⟩
  intro x hx
  apply SmallLevelContinuation.halfplane_germ_identity
    (B-((M:ℝ)+1)) (max B BG) _ _ _ x hx
  · intro z _
    exact (hG (gridIndex Q hQ t) z).meromorphicAt.sub
      ((wordCoefficient_analytic Q m _ w t ht 0 z).meromorphicAt.mul
        (hG (gridIndex Q hQ u) z).meromorphicAt)
  · intro z hz
    apply ((hrow M).1 z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro n _
    exact (wordCoefficient_analytic Q m _ w t ht (n+1) z).meromorphicAt.mul
      ((hG (gridIndex Q hQ u) (z+((n:ℂ)+1))).meromorphicAt.comp_analyticAt
        (g:=fun s : ℂ => s+((n:ℂ)+1)) (by fun_prop))
  · intro z hz
    have hzB : B<z.re := lt_of_le_of_lt (le_max_left B BG) hz
    have hzG : BG<z.re := lt_of_le_of_lt (le_max_right B BG) hz
    dsimp only
    rw [hGF z hzG,(hrow M).2 z hzB]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have hs : BG<(z+((n:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [hGF _ hs]

#print axioms wordCoefficient_analytic
#print axioms word_grid_rows_of_law
#print axioms word_grid_germs_of_law
end SmallLevelTwentyOneFiniteGrid
end
end

/-! ## SmallLevelTwentyOneFiniteGridWordRatesV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFiniteGrid
open Matrix Complex SmallLevelTwentyOneKnownWords
variable (Q : ℕ) (hQ : 0<Q)

def rawDen (w : Word) (t : ℤ) : ℝ := rawC w*((t:ℝ)/Q)+rawD w

theorem wordDen_raw (w : Word) (t : ℤ) : wordDen Q w t=wordScale w*rawDen Q w t := by
  rw [wordDen,rawDen,(raw_coordinates w).2.2.1,(raw_coordinates w).2.2.2]
  ring

theorem raw_rate (w : Word) (t : ℤ) :
    (wordDen Q w t)^2=(rawDen Q w t)^2/(raw w).det := by
  rw [wordDen_raw Q]
  apply (eq_div_iff (raw_det_pos w).ne').mpr
  calc
    (wordScale w*rawDen Q w t)^2*(raw w).det=
        ((wordScale w)^2*(raw w).det)*(rawDen Q w t)^2 := by ring
    _ = (rawDen Q w t)^2 := by rw [raw_det_scale,one_mul]

theorem raw_derivative_rate (w : Word) (t : ℤ) :
    coordC w*wordDen Q w t=rawC w*rawDen Q w t/(raw w).det := by
  rw [wordDen_raw Q,(raw_coordinates w).2.2.1]
  apply (eq_div_iff (raw_det_pos w).ne').mpr
  calc
    (wordScale w*rawC w*(wordScale w*rawDen Q w t))*(raw w).det=
        ((wordScale w)^2*(raw w).det)*(rawC w*rawDen Q w t) := by ring
    _ = rawC w*rawDen Q w t := by rw [raw_det_scale,one_mul]

theorem raw_partner (w : Word) (t : ℤ) :
    (coordA w*((t:ℝ)/Q)+coordB w)/wordDen Q w t=
      (rawA w*((t:ℝ)/Q)+rawB w)/rawDen Q w t := by
  rw [(raw_coordinates w).1,(raw_coordinates w).2.1,wordDen_raw Q]
  rw [show wordScale w*rawA w*((t:ℝ)/Q)+wordScale w*rawB w=
    wordScale w*(rawA w*((t:ℝ)/Q)+rawB w) by ring]
  exact mul_div_mul_left _ _ (wordScale_pos w).ne'

theorem raw_den_ne_zero (w : Word) (t : ℤ) : wordDen Q w t≠0 ↔ rawDen Q w t≠0 := by
  rw [wordDen_raw Q,mul_ne_zero_iff]
  exact and_iff_right (wordScale_pos w).ne'

/-- This is exactly the coefficient used by the rational projective-matrix
builder, including every positive Taylor coefficient. -/
theorem wordCoefficient_raw (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ) (n : ℕ) (s : ℂ) :
    wordCoefficient Q m χ w t n s=
      character χ w*(((rawDen Q w t)^2/(raw w).det:ℝ):ℂ)^(s-(m:ℂ))*
        (I*((rawC w*rawDen Q w t/(raw w).det:ℝ):ℂ))^n*
          Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  rw [wordCoefficient,raw_rate Q,raw_derivative_rate Q]

def integerDen (w : Word) (t : ℤ) : ℤ :=
  integerRaw w 1 0*t+integerRaw w 1 1*Q

def integerNumer (w : Word) (t : ℤ) : ℤ :=
  integerRaw w 0 0*t+integerRaw w 0 1*Q

def rationalRate (w : Word) (t : ℤ) : ℚ :=
  (integerDen Q w t : ℚ)^2/((integerRaw w).det*Q^2)

def rationalDerivative (w : Word) (t : ℤ) : ℚ :=
  (integerRaw w 1 0 : ℚ)*integerDen Q w t/((integerRaw w).det*Q)

include hQ

theorem raw_den_integer (w : Word) (t : ℤ) :
    rawDen Q w t=(integerDen Q w t : ℝ)/Q := by
  have hQR : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  simp only [rawDen,rawC,rawD,raw_integer,Matrix.map_apply,Int.coe_castRingHom,
    integerDen,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  field_simp

theorem raw_numer_integer (w : Word) (t : ℤ) :
    rawA w*((t:ℝ)/Q)+rawB w=(integerNumer Q w t : ℝ)/Q := by
  have hQR : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  simp only [rawA,rawB,raw_integer,Matrix.map_apply,Int.coe_castRingHom,
    integerNumer,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  field_simp

theorem word_den_integer (w : Word) (t : ℤ) :
    wordDen Q w t≠0 ↔ integerDen Q w t≠0 := by
  rw [raw_den_ne_zero Q,raw_den_integer Q hQ]
  simp [hQ.ne']

/-- Closing a row on the grid is an integer identity. It does not require
numerical comparison of the normalized real matrices. -/
theorem word_partner_integer (w : Word) (t u : ℤ)
    (ht : integerDen Q w t≠0) (hu : Q*integerNumer Q w t=u*integerDen Q w t) :
    (coordA w*((t:ℝ)/Q)+coordB w)/wordDen Q w t=(u:ℝ)/Q := by
  rw [raw_partner Q,raw_numer_integer Q hQ,raw_den_integer Q hQ]
  have htR : (integerDen Q w t : ℝ)≠0 := by exact_mod_cast ht
  have huR : (Q:ℝ)*(integerNumer Q w t : ℝ)=(u:ℝ)*(integerDen Q w t : ℝ) := by
    exact_mod_cast hu
  have hQR : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  field_simp
  nlinarith

theorem word_rate_rational (w : Word) (t : ℤ) :
    (wordDen Q w t)^2=(rationalRate Q w t : ℝ) := by
  rw [raw_rate Q,raw_den_integer Q hQ,raw_det_integer]
  simp only [rationalRate,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_intCast,
    Rat.cast_natCast]
  ring

theorem word_derivative_rational (w : Word) (t : ℤ) :
    coordC w*wordDen Q w t=(rationalDerivative Q w t : ℝ) := by
  rw [raw_derivative_rate Q,raw_den_integer Q hQ,raw_det_integer]
  simp only [rawC,raw_integer,Matrix.map_apply,Int.coe_castRingHom,
    rationalDerivative,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_natCast]
  ring

/-- Exact equality for the complete Taylor coefficient, not just its leading
term. All matrix-dependent data on the right are rational or integral. -/
theorem wordCoefficient_rational (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ)
    (n : ℕ) (s : ℂ) :
    wordCoefficient Q m χ w t n s=
      χ^(frickeCount w)*(rationalRate Q w t : ℂ)^(s-(m:ℂ))*
        (I*(rationalDerivative Q w t : ℂ))^n*
          Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  rw [wordCoefficient,character_count,word_rate_rational Q hQ,word_derivative_rational Q hQ]
  simp only [Complex.ofReal_ratCast]


#print axioms word_partner_integer
#print axioms wordCoefficient_rational
end SmallLevelTwentyOneFiniteGrid
end
end

/-! ## SmallLevelTwentyOneFiniteGridCertificateV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFiniteGrid
open Complex SmallLevelTwentyOneKnownWords SmallLevelTaylor Set

/-- Exact word data for an arbitrary positive grid denominator. -/
structure WordCertificate (Q : ℕ) where
  word : Word
  source : ℤ
  target : ℤ
  nonaffine : integerRaw word 1 0≠0
  denominator : integerDen Q word source≠0
  closed : (Q:ℤ)*integerNumer Q word source=target*integerDen Q word source
  rate : ℚ
  slope : ℚ
  count : ℕ
  powers : ℤ×ℤ×ℤ×ℤ
  rate_eq : rationalRate Q word source=rate
  slope_eq : rationalDerivative Q word source=slope
  count_eq : frickeCount word=count
  powers_eq : rate=(2:ℚ)^powers.1*(3:ℚ)^powers.2.1*(7:ℚ)^powers.2.2.1*(5:ℚ)^powers.2.2.2

def coefficient {Q : ℕ} (r : WordCertificate Q) (m : ℕ) (χ : ℂ)
    (n : ℕ) (s : ℂ) : ℂ :=
  χ^r.count*(r.rate:ℂ)^(s-(m:ℂ))*(I*(r.slope:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

def fourPrimeMonomial (e : ℤ×ℤ×ℤ×ℤ) (x y z b : ℂ) : ℂ :=
  x^e.1*y^e.2.1*z^e.2.2.1*b^e.2.2.2

theorem rational_four_prime_power (r : ℚ) (e : ℤ×ℤ×ℤ×ℤ)
    (hr : r=(2:ℚ)^e.1*(3:ℚ)^e.2.1*(7:ℚ)^e.2.2.1*(5:ℚ)^e.2.2.2) (s : ℂ) :
    (r:ℂ)^s=fourPrimeMonomial e ((2:ℂ)^s) ((3:ℂ)^s) ((7:ℂ)^s) ((5:ℂ)^s) := by
  have hreal : (r:ℝ)=(2:ℝ)^e.1*(3:ℝ)^e.2.1*(7:ℝ)^e.2.2.1*(5:ℝ)^e.2.2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q:ℝ)) hr
  have hc : (r:ℂ)=(((2:ℝ)^e.1*(3:ℝ)^e.2.1*(7:ℝ)^e.2.2.1*(5:ℝ)^e.2.2.2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ratCast] using congrArg (fun t : ℝ => (t:ℂ)) hreal
  rw [hc,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [positive_zpow_cpow_direct (by norm_num : (0:ℝ)<2),
    positive_zpow_cpow_direct (by norm_num : (0:ℝ)<3),
    positive_zpow_cpow_direct (by norm_num : (0:ℝ)<7),
    positive_zpow_cpow_direct (by norm_num : (0:ℝ)<5)]
  rfl

theorem coefficient_eq {Q : ℕ} (hQ : 0<Q) (r : WordCertificate Q)
    (m : ℕ) (χ : ℂ) (n : ℕ) (s : ℂ) :
    wordCoefficient Q m χ r.word r.source n s=coefficient r m χ n s := by
  rw [wordCoefficient_rational Q hQ]
  simp only [coefficient,r.rate_eq,r.slope_eq,r.count_eq]

theorem coefficient_analytic {Q : ℕ} (hQ : 0<Q) (r : WordCertificate Q)
    (m : ℕ) (χ : ℂ) (n : ℕ) (s : ℂ) : AnalyticAt ℂ (coefficient r m χ n) s := by
  have he : coefficient r m χ n=wordCoefficient Q m χ r.word r.source n :=
    funext (fun s => (coefficient_eq hQ r m χ n s).symm)
  rw [he]
  exact wordCoefficient_analytic Q m χ r.word r.source
    ((word_den_integer Q hQ r.word r.source).mpr r.denominator) n s

theorem coefficient_leading {Q : ℕ} (r : WordCertificate Q) (m : ℕ) (χ s : ℂ) :
    coefficient r m χ 0 s=χ^r.count*fourPrimeMonomial r.powers
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 7 m s) (primeParameter 5 m s) := by
  simp only [coefficient,pow_zero,Ring.choose_zero_right,mul_one]
  rw [rational_four_prime_power _ _ r.powers_eq]
  rfl

/-- Exported exact word data supply genuine Taylor rows of the original
additive transforms on any positive grid. -/
theorem certificate_rows {Q : ℕ} (hQ : 0<Q) (r : WordCertificate Q)
    {m : ℕ} {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector Q (2*m) f s (gridIndex Q hQ r.source)-
          coefficient r m (ε*I^(2*m)) 0 s*gridVector Q (2*m) f s (gridIndex Q hQ r.target)=
        error M s+∑ n∈Finset.range M,
          coefficient r m (ε*I^(2*m)) (n+1) s*
            gridVector Q (2*m) f (s+((n:ℂ)+1)) (gridIndex Q hQ r.target) := by
  simpa only [coefficient_eq hQ] using word_grid_rows_of_law Q hQ hf ε hε hlaw r.word
    ((SmallLevelTwentyOneKnownWords.word_C_integer r.word).mpr r.nonaffine)
    r.source r.target ((word_den_integer Q hQ r.word r.source).mpr r.denominator)
    (word_partner_integer Q hQ r.word r.source r.target r.denominator r.closed)

#print axioms rational_four_prime_power
#print axioms coefficient_analytic
#print axioms certificate_rows
end SmallLevelTwentyOneFiniteGrid
end
end

/-! ## SmallLevelTwentyOneFiniteGridHeckeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFiniteGrid
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive Filter
open scoped Topology
variable (Q : ℕ) (hQ : 0<Q)

def heckeLeading (m : ℕ) (f : ℕ→ℂ) (p : ℕ) (j : ℤ) (s : ℂ) : ℂ :=
  (∑ a∈Finset.range p, grid (2*m) f Q (j+(a:ℤ)*(Q/p:ℕ)) s)-
    ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*grid (2*m) f Q ((p:ℤ)*j) s+
    if p∣21 then 0 else
      ((p:ℂ)^((m:ℂ)-s))^2*grid (2*m) f Q ((p:ℤ)^2*j) s

include hQ in
theorem original_hecke_grid {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    {p : ℕ} (hp : p.Prime) (hpQ : p∣Q) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → heckeLeading Q m f p j s=0 := by
  have hsum (j : ℤ) (s : ℂ) :
      (∑ a∈Finset.range p, original (2*m) f ((j:ℝ)/Q+(a:ℝ)/p) s)=
      ∑ a∈Finset.range p, grid (2*m) f Q (j+(a:ℤ)*(Q/p:ℕ)) s := by
    apply Finset.sum_congr rfl
    intro a _
    unfold grid
    congr 1
    simpa only [Nat.cast_ofNat] using
      (grid_translation hQ hp.pos hpQ (t := j) (j := a))
  have h1 (j : ℤ) : (p:ℝ)*((j:ℝ)/Q)=(((p:ℤ)*j:ℤ):ℝ)/Q := by
    push_cast
    ring
  have h2 (j : ℤ) : (p:ℝ)^2*((j:ℝ)/Q)=(((p:ℤ)^2*j:ℤ):ℝ)/Q := by
    push_cast
    ring
  by_cases hb : p∣21
  · obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.normalized_additive_bad_hecke hm hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/Q) s hs
    rw [hsum,h1] at hh
    simpa only [heckeLeading,ite_eq_left hb,add_zero,grid,Nat.cast_ofNat] using hh
  · obtain ⟨B,hB⟩ := normalized_additive_hecke hf hp hb
    refine ⟨B,?_⟩
    intro j s hs
    have hh := hB ((j:ℝ)/Q) s hs
    rw [hsum,h1,h2] at hh
    simpa only [heckeLeading,ite_eq_right hb,grid,Nat.cast_ofNat] using hh


def completeSum (p : ℕ) (t : ℤ) (w : Fin Q → ℂ) : ℂ :=
  ∑ a∈Finset.range p, w (gridIndex Q hQ (t+(a:ℤ)*(Q/p:ℕ)))

def fullHeckeRow (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (j : ℤ)
    (s : ℂ) (v : Fin Q → ℂ) : ℂ :=
  completeSum Q hQ p j v-((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*v (gridIndex Q hQ ((p:ℤ)*j))+
    if p∣21 then 0 else ((p:ℂ)^((m:ℂ)-s))^2*v (gridIndex Q hQ ((p:ℤ)^2*j))

theorem fullHeckeRow_grid (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (j : ℤ) (s : ℂ) :
    fullHeckeRow Q hQ m f p j s (gridVector Q (2*m) f s)=
      heckeLeading Q m f p j s := by
  simp only [fullHeckeRow,completeSum,gridVector_index,
    heckeLeading]

theorem fullHeckeRow_meromorphic (m : ℕ) (f : ℕ → ℂ)
    {p : ℕ} (hp : 0<p) (j : ℤ) (G : ℂ → Fin Q → ℂ)
    (hG : ∀ i z, MeromorphicAt (fun w => G w i) z) (s : ℂ) :
    MeromorphicAt (fun z => fullHeckeRow Q hQ m f p j z (G z)) s := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  have hP : AnalyticAt ℂ (fun z : ℂ => (p:ℂ)^((m:ℂ)-z)) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hp0]
    fun_prop
  have hsum : MeromorphicAt (fun z => completeSum Q hQ p j (G z)) s := by
    apply MeromorphicAt.fun_sum
    intro a _
    exact hG _ s
  unfold fullHeckeRow
  apply (hsum.sub ((analyticAt_const.mul hP).meromorphicAt.mul (hG _ s))).add
  by_cases hb : p∣21
  · simpa only [ite_eq_left hb] using (analyticAt_const (v := (0:ℂ))).meromorphicAt
  · simpa only [ite_eq_right hb] using (hP.fun_pow 2).meromorphicAt.fun_mul (hG _ s)

/-- Every good or bad prime row on the closed grid holds after continuation,
for every numerator. No prime eigenvalue is assumed nonzero. -/
theorem original_full_hecke_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin Q → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector Q (2*m) f z)
    {p : ℕ} (hp : p.Prime) (hpQ : p∣Q) (j : ℤ) (x : ℂ) :
    (fun z => fullHeckeRow Q hQ m f p j z (G z))=ᶠ[𝓝[≠] x] (fun _ => 0) := by
  obtain ⟨B,hB⟩ := original_hecke_grid Q hQ
    hm hf hp hpQ
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact fullHeckeRow_meromorphic Q hQ m f hp.pos j G (fun i w => (hG i w).meromorphicAt) z
  · intro z _
    exact analyticAt_const.meromorphicAt
  · intro z hz
    dsimp only
    rw [hGF z (lt_of_le_of_lt (le_max_right B BG) hz),fullHeckeRow_grid]
    exact hB j z (lt_of_le_of_lt (le_max_left B BG) hz)


#print axioms original_hecke_grid
#print axioms original_full_hecke_germs
end SmallLevelTwentyOneFiniteGrid
end
end

/-! ## SmallLevelTwentyOneFiniteGridInfinityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFiniteGrid
open Complex Filter Set MeasureTheory SmallLevelAdditive SmallLevelTaylor
open FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelTwentyOneKnownWords
open scoped Topology

variable (Q : ℕ) (hQ : 0<Q)

def sourceEntire (k : ℕ) (f : ℕ → ℂ) (t : ℤ) : ℂ → ℂ :=
  mellin (fun y : ℝ => fourier (fullCoefficients f k) ((((t:ℝ)/Q:ℝ):ℂ)+(y:ℂ)*I))

theorem original_word_source_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (w : Word) (hC : coordC w≠0) (t : ℤ) (ht : wordDen Q w t=0) :
    Differentiable ℂ (sourceEntire Q (2*m) f t) := by
  obtain ⟨χ,hχ,hwords⟩ := original_words hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hne : character χ w≠0 := by
    rcases character_sign hχ w with hh|hh <;> simp [hh]
  unfold sourceEntire
  exact QuantitativeArithmeticMatrixInfinityMellin.matrix_source_entire
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m))
    (2*m) (by omega) (coordA w) (coordB w) (coordC w) (coordD w) ((t:ℝ)/Q)
    hC (by rw [coordinate_det]; norm_num) ht (character χ w) hne
    (word_fourier_of_slash m f χ hχ w (hwords w))

/-- The source-to-infinity rows are entire on the actual continued grid;
these are the `ginf` rows in the finite pole system. -/
theorem original_word_infinity_germ {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin Q → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector Q (2*m) f z)
    (w : Word) (hC : coordC w≠0) (t : ℤ) (ht : wordDen Q w t=0) :
    (∀ x : ℂ, AnalyticAt ℂ (sourceEntire Q (2*m) f t) x) ∧
      ∀ x : ℂ, (fun s => G s (gridIndex Q hQ t)) =ᶠ[𝓝[≠] x] sourceEntire Q (2*m) f t := by
  have hE := original_word_source_entire Q hm hf w hC t ht
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  refine ⟨fun x => hE.analyticAt x,?_⟩
  intro x
  apply SmallLevelContinuation.halfplane_germ_identity
    (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact (hG (gridIndex Q hQ t) z).meromorphicAt
  · intro z _
    exact (hE.analyticAt z).meromorphicAt
  · intro z hz
    have hzB : B<z.re := lt_of_le_of_lt (le_max_left B BG) hz
    have hzG : BG<z.re := lt_of_le_of_lt (le_max_right B BG) hz
    dsimp only
    rw [hGF z hzG,gridVector_index]
    change original (2*m) f ((t:ℝ)/Q) z=
      mellin (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((((t:ℝ)/Q:ℝ):ℂ)+(y:ℂ)*I)) z
    exact ((hB ((t:ℝ)/Q) z hzB).2).symm

#print axioms original_word_source_entire
#print axioms original_word_infinity_germ
end SmallLevelTwentyOneFiniteGrid
end
end

/-! ## SmallLevelTwentyOneFiniteGridSamplesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneFiniteGrid
open Complex SmallLevelTaylor SmallLevelAdditive FinitenessRamanujanSum
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessNormalizedTwistProduct
open MeasureTheory Set

variable (Q : ℕ) (hQ : 0<Q)

def sampleSum (q : ℕ) (t : ℤ) (w : Fin Q → ℂ) : ℂ :=
  ∑ j∈residues q, w (gridIndex Q hQ (t+(j:ℤ)*(Q/q:ℕ)))

theorem sampleSum_grid (k : ℕ) (f : ℕ → ℂ) (q : ℕ) (t : ℤ) (s : ℂ) :
    sampleSum Q hQ q t (gridVector Q k f s)=gridSum k f Q q t s := by
  simp only [sampleSum,gridSum,gridVector_index]

theorem sampleSum_add (q : ℕ) (t : ℤ) (w z : Fin Q → ℂ) :
    sampleSum Q hQ q t (w+z)=sampleSum Q hQ q t w+sampleSum Q hQ q t z := by
  simp [sampleSum,Finset.sum_add_distrib]

theorem sampleSum_smul (q : ℕ) (t : ℤ) (c : ℂ) (w : Fin Q → ℂ) :
    sampleSum Q hQ q t (c • w)=c*sampleSum Q hQ q t w := by
  simp [sampleSum,Finset.mul_sum]

def taylorCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t : ℤ) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (Nat.lcm 21 (q^2)) ((t:ℝ)/(Q:ℝ))
    (root 21 f q*ε*I^k) n s

def taylorError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t : ℤ) (M : ℕ) : ℂ → ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f q) k)
    (Nat.lcm 21 (q^2)) ((t:ℝ)/(Q:ℝ)) (root 21 f q*ε*I^k) (M+1))

theorem original_taylor_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (q : ℕ) (hq : 0<q) (hqQ : q∣Q) (t d : ℤ) (ht : t≠0)
    (hd : (Nat.lcm 21 (q^2):ℤ)*d=(Q:ℤ)^2) (htd : t∣d) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (taylorError Q (2*m) f ε q t M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        sampleSum Q hQ q t (gridVector Q (2*m) f s)-
          taylorCoefficient Q (2*m) f ε q t 0 s*
            sampleSum Q hQ q (-(d/t)) (gridVector Q (2*m) f s)=
        taylorError Q (2*m) f ε q t M s+∑ n∈Finset.range M,
          taylorCoefficient Q (2*m) f ε q t (n+1) s*
            sampleSum Q hQ q (-(d/t)) (gridVector Q (2*m) f (s+((n:ℂ)+1))) := by
  simpa only [sampleSum_grid,taylorCoefficient,taylorError] using
    QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
      (by decide : 0<21) (even_two_mul m) hf ε hlaw Q q hQ hq hqQ t d ht hd htd

theorem original_entire_row {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 k f)
    (q : ℕ) (hq : 0<q) (hqQ : q∣Q) :
    (∀ s, AnalyticAt ℂ (ramanujanEntire 21 k f q) s) ∧
      ∃ B : ℝ, ∀ s : ℂ, B<s.re →
        sampleSum Q hQ q 0 (gridVector Q k f s)=ramanujanEntire 21 k f q s := by
  obtain ⟨he,B,hB⟩ := original_ramanujan_entire (by decide : 0<21) hk hf hq
  refine ⟨he,B,?_⟩
  intro s hs
  rw [sampleSum_grid,hB s hs]
  have hh := ramanujanAdditive_grid k f hQ hq hqQ 0 s
  simpa only [Int.cast_zero,zero_div,gridSum] using hh.symm

#print axioms original_taylor_rows
#print axioms original_entire_row
end SmallLevelTwentyOneFiniteGrid
end
end
