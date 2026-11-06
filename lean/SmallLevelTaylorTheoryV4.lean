module

public import FinitenessAllLevelGoodTraceV1
public import FinitenessAllLevelMellinPairV1
public import FinitenessOriginalTwistedContinuationsV1
public import QuantitativeArithmeticTwoSequenceStripRowsV1
public import SmallLevelAdditiveConvergenceV1
public import SmallLevelAdditiveTheoryV4
public import SmallLevelFrickeMellinRemainderV1
public import SmallLevelRamanujanAdditiveV1
public import SmallLevelTaylorRowNormalizationV1
public import SmallLevelThirtySixFourierV1

/-! Consolidated chapter: SmallLevelTaylor. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticNormalizedTaylorBoundedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
theorem normalized_taylor_bounded_rows {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) (hk : Even k) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError k a L r χ M)) {s : ℂ | B-(M:ℝ)<s.re} ∧
      QuantitativeArithmeticMellinStrip.BoundedSubstrips (B-(M:ℝ))
        (mellin (frickeError k a L r χ M)) ∧
      ∀ s : ℂ, B<s.re →
        SmallLevelAdditive.transform a r s-
          χ*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*normalizedTaylorSum k a L r M s=
          mellin (frickeError k a L r χ M) s := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticTwoSequenceTaylor.two_taylor_bounded_rows hL hr k ha ha0 ha ha0 χ hF
  refine ⟨B,fun M => ⟨(hB M).1,(hB M).2.1,?_⟩⟩
  intro s hs
  rw [← normalized_taylor_sum hL hr k hk a χ s M]
  exact (hB M).2.2 s hs

#print axioms normalized_taylor_bounded_rows
end SmallLevelTaylor
end
end

/-! ## QuantitativeArithmeticOriginalTaylorBoundedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessFourierConstruction

/-- The paper's full Taylor--Fricke identity for every positive Ramanujan
modulus, every nonzero real translation, and every Taylor order. All analytic
bounds and the transformation law follow from the original Euler input.
The sign is chosen once, before q, and zero twists are included. -/
theorem original_ramanujan_bounded_taylor_rows {N k : ℕ} (hN : 0<N) (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M))
          {s : ℂ | B-(M:ℝ)<s.re} ∧
        QuantitativeArithmeticMellinStrip.BoundedSubstrips (B-(M:ℝ))
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M)) ∧
        ∀ s : ℂ, B<s.re →
          SmallLevelAdditive.transform (fullCoefficients (twisted f q) k) r s-
            (root N f q*ε*I^k)*(((Nat.lcm N (q^2):ℝ)*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*
              normalizedTaylorSum k (fullCoefficients (twisted f q) k) (Nat.lcm N (q^2)) r M s=
            mellin (frickeError k (fullCoefficients (twisted f q) k)
              (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M) s := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨ε,hε,?_⟩
  intro q hq r hr
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  apply normalized_taylor_bounded_rows (by exact_mod_cast hL) hr k hk
    (polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k)
    (fullCoefficients_zero (twisted_zero hf.zero q) k) (root N f q*ε*I^k)
  intro z hz
  have hreflect : 0<(-1/((Nat.lcm N (q^2):ℕ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [Complex.ofReal_natCast,fourier_twisted hf.zero hg q k hz,
    fourier_twisted hf.zero hg q k hreflect] using hlaw q hq z hz

#print axioms original_ramanujan_bounded_taylor_rows
end SmallLevelTaylor
end
end

/-! ## SmallLevelRamanujanEntireV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessFourierConstruction FinitenessAllLevelAxisDecay

/-- Unscaling the imaginary-axis Mellin integral preserves entireness. -/
theorem axis_unscaled_mellin {L : ℕ} (hL : 0<L) (a : ℕ → ℂ) (s : ℂ) :
    mellin (fun y : ℝ => fourier a ((y:ℂ)*I)) s=
      (Real.sqrt L:ℂ)^(-s)*mellin (axis L a) s := by
  have hs : 0<Real.sqrt (L:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  have he : (fun y : ℝ => fourier a ((y:ℂ)*I))=
      (fun y : ℝ => axis L a (Real.sqrt L*y)) := by
    funext y
    simp only [axis,mul_div_cancel_left₀ y (ne_of_gt hs)]
  rw [he,mellin_comp_mul_left (axis L a) s hs,smul_eq_mul]

def ramanujanEntire (_N k : ℕ) (f : ℕ → ℂ) (q : ℕ) (s : ℂ) : ℂ :=
  mellin (fun y : ℝ => fourier (fullCoefficients (twisted f q) k) ((y:ℂ)*I)) s

/-- The entire Ramanujan rows are actual Mellin integrals, and agree with
the primitive additive sums on a right half-plane. -/
theorem original_ramanujan_entire {N k : ℕ} (hN : 0<N) (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) {q : ℕ} (hq : 0<q) :
    (∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire N k f q) s) ∧
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → ramanujanEntire N k f q s=ramanujanAdditive k f q 0 s := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  have ha := polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k
  have ha0 := fullCoefficients_zero (twisted_zero hf.zero q) k
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  have hroot : root N f q*ε≠0 := by
    rcases root_unit hf.toEulerData q with h|h <;> rcases hε with he|he <;> simp [h,he]
  have hfr : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients (twisted f q) k) z=
      ((root N f q*ε)*I^k)/(((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^k)*
        fourier (fullCoefficients (twisted f q) k) (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
    intro z hz
    have hreflect : 0<(-1/((Nat.lcm N (q^2):ℂ)*z)).im := by
      simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
        (L := (Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
    simpa only [fourier_twisted hf.zero hg q k hz,fourier_twisted hf.zero hg q k hreflect] using hlaw q hq z hz
  have hm := (FinitenessAllLevelMellinPair.mellin_entire hL hk _ ha ha0 (root N f q*ε) hroot hfr).1
  constructor
  · intro s
    unfold ramanujanEntire
    simp_rw [axis_unscaled_mellin hL]
    have hp : AnalyticAt ℂ (fun z : ℂ => (Real.sqrt (Nat.lcm N (q^2)):ℂ)^(-z)) s := by
      have hs0 : (Real.sqrt (Nat.lcm N (q^2)):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hL)))
      simp_rw [Complex.cpow_def_of_ne_zero hs0]
      fun_prop
    exact hp.mul (hm.analyticAt s)
  · obtain ⟨B,hB⟩ := additive_convergence_halfplane ha ha0
    obtain ⟨C,hC⟩ := ramanujan_additive_sum hf q
    refine ⟨max B C,?_⟩
    intro s hs
    have he := (hB 0 s (lt_of_le_of_lt (le_max_left _ _) hs)).2
    simp only [Complex.ofReal_zero,zero_add] at he
    exact he.trans (hC 0 s (lt_of_le_of_lt (le_max_right _ _) hs))

#print axioms axis_unscaled_mellin
#print axioms original_ramanujan_entire
end SmallLevelTaylor
end
end

/-! ## QuantitativeArithmeticRamanujanEntireBoundedV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessFourierConstruction FinitenessAllLevelAxisDecay

theorem original_ramanujan_mellin_convergent {N k : ℕ} (hN : 0<N) (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) {q : ℕ} (hq : 0<q) (s : ℂ) :
    MellinConvergent (fun y : ℝ => fourier (fullCoefficients (twisted f q) k) ((y:ℂ)*I)) s := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  have ha := polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k
  have ha0 := fullCoefficients_zero (twisted_zero hf.zero q) k
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  have hroot : root N f q*ε≠0 := by
    rcases root_unit hf.toEulerData q with h|h <;> rcases hε with he|he <;> simp [h,he]
  have hfr : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients (twisted f q) k) z=
      ((root N f q*ε)*I^k)/(((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^k)*
        fourier (fullCoefficients (twisted f q) k) (-1/((Nat.lcm N (q^2):ℂ)*z)) := by
    intro z hz
    have hreflect : 0<(-1/((Nat.lcm N (q^2):ℂ)*z)).im := by
      simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
        (L := (Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
    simpa only [fourier_twisted hf.zero hg q k hz,fourier_twisted hf.zero hg q k hreflect] using hlaw q hq z hz
  let P := FinitenessAllLevelMellinPair.pair hL hk _ ha ha0 (root N f q*ε) hroot hfr
  have hP : IsStrongFEPair P := ⟨rfl,rfl⟩
  have hh := (hP.hasMellin s).1
  change MellinConvergent (axis (Nat.lcm N (q^2)) (fullCoefficients (twisted f q) k)) s at hh
  have hs : 0<Real.sqrt (Nat.lcm N (q^2):ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hL)
  have he : (fun y : ℝ => fourier (fullCoefficients (twisted f q) k) ((y:ℂ)*I))=
      (fun y : ℝ => axis (Nat.lcm N (q^2)) (fullCoefficients (twisted f q) k)
        (Real.sqrt (Nat.lcm N (q^2):ℝ)*y)) := by
    funext y
    simp only [axis,mul_div_cancel_left₀ y hs.ne']
  rw [he]
  exact MellinConvergent.comp_mul_left hs |>.mpr hh

theorem original_ramanujan_bounded_strips {N k : ℕ} (hN : 0<N) (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) {q : ℕ} (hq : 0<q) (b : ℝ) :
    QuantitativeArithmeticMellinStrip.BoundedSubstrips b (ramanujanEntire N k f q) := by
  intro l u _ _
  exact QuantitativeArithmeticMellinStrip.bounded_strip _ l u
    (original_ramanujan_mellin_convergent hN hk hf hq l)
    (original_ramanujan_mellin_convergent hN hk hf hq u)
#print axioms original_ramanujan_mellin_convergent
#print axioms original_ramanujan_bounded_strips
end SmallLevelTaylor
end
end

/-! ## SmallLevelAdditiveHeckeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessPolynomialSeries FinitenessOriginalFourier
open FinitenessFourierConstruction QuantitativeArithmeticRetainedReconstruction

/-- Dilating the entire vertical ray has its exact Mellin scaling factor. -/
theorem dilated_ray_hasMellin {a : ℕ → ℂ} {t : ℝ} (ht : 0<t) (r : ℝ) (s : ℂ)
    (h : MellinConvergent (fun y : ℝ => fourier a (((t*r:ℝ):ℂ)+(y:ℂ)*I)) s) :
    HasMellin (fun y : ℝ => fourier a ((t:ℂ)*((r:ℂ)+(y:ℂ)*I))) s
      ((t:ℂ)^(-s)*mellin (fun y : ℝ => fourier a (((t*r:ℝ):ℂ)+(y:ℂ)*I)) s) := by
  have he : (fun y : ℝ => fourier a ((t:ℂ)*((r:ℂ)+(y:ℂ)*I)))=
      (fun y : ℝ => fourier a (((t*r:ℝ):ℂ)+((t*y:ℝ):ℂ)*I)) := by
    funext y
    congr 1
    push_cast
    ring
  rw [he]
  constructor
  · exact (MellinConvergent.comp_mul_left ht).mpr h
  · simpa only [smul_eq_mul] using mellin_comp_mul_left
      (fun y : ℝ => fourier a (((t*r:ℝ):ℂ)+(y:ℂ)*I)) s ht

/-- Good-prime Hecke rows for actual additive Mellin transforms, derived
from the original Euler product. The eigenvalue is unrestricted. -/
theorem original_additive_hecke {N k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) {p : ℕ} (hp : p.Prime) (hgood : ¬p∣N) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range p, SmallLevelAdditive.original k f (r+(j:ℝ)/p) s)=
        (((p:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f p*(p:ℂ)^(-s)*
          SmallLevelAdditive.original k f ((p:ℝ)*r) s-
        (p:ℂ)^k*((p:ℂ)^2)^(-s)*SmallLevelAdditive.original k f ((p:ℝ)^2*r) s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  obtain ⟨B,hB⟩ := additive_convergence_halfplane (polynomial_bound hf.zero hg k) (fullCoefficients_zero hf.zero k)
  refine ⟨B,?_⟩
  intro r s hs
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
  let a := fullCoefficients f k
  let C : ℂ := (((p:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f p
  have h1 := dilated_ray_hasMellin hpR r s (hB ((p:ℝ)*r) s hs).1
  have h2 := dilated_ray_hasMellin (sq_pos_of_pos hpR) r s (hB ((p:ℝ)^2*r) s hs).1
  have he : EqOn
      (fun y : ℝ => ∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I))
      (fun y : ℝ => C*fourier a ((p:ℂ)*((r:ℂ)+(y:ℂ)*I))-
        (p:ℂ)^k*fourier a (((p:ℝ)^2:ℝ)*((r:ℂ)+(y:ℂ)*I))) (Ioi 0) := by
    intro y hy
    dsimp only
    have he := FinitenessAllLevelGoodTrace.original_complete hf.toEulerData hp hgood k (z := (r:ℂ)+(y:ℂ)*I)
      (by simpa using hy)
    change completeTwist (fourier a) p ((r:ℂ)+(y:ℂ)*I)=_ at he
    have hsum : (∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I))=
        completeTwist (fourier a) p ((r:ℂ)+(y:ℂ)*I) := by
      unfold completeTwist
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      push_cast
      ring
    rw [hsum,he]
    simp only [Complex.ofReal_pow,Complex.ofReal_natCast,C,a]
  have hsum : mellin
      (fun y : ℝ => ∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I)) s=
      ∑ j∈Finset.range p, SmallLevelAdditive.original k f (r+(j:ℝ)/p) s := by
    unfold mellin
    simp only [Finset.smul_sum]
    rw [integral_finsetSum (Finset.range p) (fun j _ => (hB (r+(j:ℝ)/p) s hs).1)]
    apply Finset.sum_congr rfl
    intro j _
    exact (hB (r+(j:ℝ)/p) s hs).2
  have hm := (hasMellin_sub (h1.1.const_smul C) (h2.1.const_smul ((p:ℂ)^k))).2
  rw [mellin_const_smul,mellin_const_smul,h1.2,h2.2,
    (hB ((p:ℝ)*r) s hs).2,(hB ((p:ℝ)^2*r) s hs).2] at hm
  rw [← hsum,mellin_congr_positive he s]
  simpa only [smul_eq_mul,Complex.ofReal_pow,Complex.ofReal_natCast,C,a,SmallLevelAdditive.original,mul_assoc] using hm

#print axioms dilated_ray_hasMellin
#print axioms original_additive_hecke
end SmallLevelTaylor
end
end

/-! ## SmallLevelClosedGridRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessRamanujanSum FinitenessNormalizedTwistProduct SmallLevelAdditive

/-- A finite sum of coordinates of the original additive grid. -/
def gridSum (k : ℕ) (f : ℕ → ℂ) (Q q : ℕ) (t : ℤ) (s : ℂ) : ℂ :=
  ∑ j∈residues q, grid k f Q (t+(j:ℤ)*(Q/q:ℕ)) s

theorem ramanujanTaylorSum_split (k : ℕ) (f : ℕ → ℂ) (q : ℕ)
    (L r : ℝ) (χ s : ℂ) (M : ℕ) :
    χ*((L*r^2:ℝ):ℂ)^(s-((k:ℂ)/2))*ramanujanTaylorSum k f q L r (M+1) s=
      taylorRowScalar k L r χ 0 s*ramanujanAdditive k f q (-1/(L*r)) s+
        ∑ n∈Finset.range M, taylorRowScalar k L r χ (n+1) s*
          ramanujanAdditive k f q (-1/(L*r)) (s+((n+1:ℕ):ℂ)) := by
  unfold ramanujanTaylorSum
  rw [Finset.sum_range_succ',mul_add,Finset.mul_sum]
  simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,one_mul]
  rw [add_comm]
  congr 1
  · simp [taylorRowScalar]
  · apply Finset.sum_congr rfl
    intro n _
    unfold taylorRowScalar
    ring

/-- Actual closed-grid Taylor rows from the original Euler input. The
same finite target grid supplies every positive shift; no continuation
of its coordinates is assumed. Determinant/rank certificates are separate. -/
theorem original_closed_grid_taylor_rows {N k : ℕ} (hN : 0<N) (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ Q q : ℕ, 0<Q → 0<q → q∣Q →
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
  obtain ⟨ε,hε,hrows⟩ := original_finite_sum_taylor_rows hN hk hf
  refine ⟨ε,hε,?_⟩
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

#print axioms ramanujanTaylorSum_split
#print axioms original_closed_grid_taylor_rows
end SmallLevelTaylor
end
end

/-! ## SmallLevelHeckeRowNormalizationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor
open Complex

theorem hecke_first_scalar {p : ℕ} (hp : 0<p) (m : ℕ) (v s : ℂ) :
    (((p:ℝ)^((((2*m:ℕ):ℝ)+1)/2):ℝ):ℂ)*v*(p:ℂ)^(-s)=
      (Real.sqrt p:ℂ)*v*(p:ℂ)^((m:ℂ)-s) := by
  rw [FinitenessAllLevelGoodTrace.first_weight_even p m hp]
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  rw [show (m:ℂ)-s=(m:ℂ)+(-s) by ring,Complex.cpow_add _ _ hp0,Complex.cpow_natCast]
  push_cast
  ring

theorem hecke_second_scalar {p : ℕ} (hp : 0<p) (m : ℕ) (s : ℂ) :
    (p:ℂ)^(2*m)*((p:ℂ)^2)^(-s)=((p:ℂ)^((m:ℂ)-s))^2 := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  rw [← Complex.natCast_cpow_natCast_mul p 2 (-s),← Complex.cpow_natCast (p:ℂ) (2*m),
    ← Complex.cpow_add _ _ hp0,← Complex.cpow_nat_mul (p:ℂ) 2 ((m:ℂ)-s)]
  congr 1
  push_cast
  ring

/-- Exact normalized good-prime Hecke row. This includes zero eigenvalues. -/
theorem normalized_additive_hecke {N m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f) {p : ℕ} (hp : p.Prime) (hgood : ¬p∣N) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range p, SmallLevelAdditive.original (2*m) f (r+(j:ℝ)/p) s)-
        ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*
          SmallLevelAdditive.original (2*m) f ((p:ℝ)*r) s+
        ((p:ℂ)^((m:ℂ)-s))^2*SmallLevelAdditive.original (2*m) f ((p:ℝ)^2*r) s=0 := by
  obtain ⟨B,hB⟩ := original_additive_hecke hf hp hgood
  refine ⟨B,?_⟩
  intro r s hs
  rw [hB r s hs,hecke_first_scalar hp.pos m (f p) s,hecke_second_scalar hp.pos m s]
  ring

theorem hecke_parameter_analytic {p : ℕ} (hp : 0<p) (m : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (p:ℂ)^((m:ℂ)-z)) s := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  simp_rw [Complex.cpow_def_of_ne_zero hp0]
  fun_prop

#print axioms normalized_additive_hecke
#print axioms hecke_parameter_analytic
end SmallLevelTaylor
end
end

/-! ## SmallLevelRamanujanMellinRemainderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessFourierConstruction

/-- Every positive Ramanujan twist of the original Euler input has a genuine
movable Mellin remainder. The same original sign epsilon is used for every q,
including identically zero twists. The remainder is currently expressed by
Cauchy Taylor coefficients, whose shifted-Mellin identification is still needed. -/
theorem original_ramanujan_mellin_remainders {N k : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ q : ℕ, 0<q → ∀ r : ℝ, r≠0 →
      ∃ K : ℕ, ∀ M : ℕ,
        AnalyticOnNhd ℂ
          (mellin (frickeError k (fullCoefficients (twisted f q) k)
            (Nat.lcm N (q^2)) r (root N f q*ε*I^k) M))
          {s : ℂ | (K:ℝ)-(M:ℝ)<s.re} := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨ε,hε,?_⟩
  intro q hq r hr
  have hL : 0<Nat.lcm N (q^2) := Nat.lcm_pos hN (pow_pos hq _)
  apply frickeError_mellin_analytic (by exact_mod_cast hL) hr k
    (polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) k)
    (fullCoefficients_zero (twisted_zero hf.zero q) k) (root N f q*ε*I^k)
  intro z hz
  have hreflect : 0<(-1/((Nat.lcm N (q^2):ℕ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (Nat.lcm N (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [Complex.ofReal_natCast,fourier_twisted hf.zero hg q k hz,
    fourier_twisted hf.zero hg q k hreflect] using hlaw q hq z hz

#print axioms original_ramanujan_mellin_remainders

end SmallLevelTaylor
end
end

/-! ## SmallLevelSquarePrimeAdditiveV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace SmallLevelTaylor
open Complex Set MeasureTheory FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticRetainedReconstruction

/-- A square-dividing prime gives an exact zero additive Mellin row on
one common original half-plane, for every translate. -/
theorem original_square_prime_additive {N k : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) {p : ℕ}
    (hp : p.Prime) (hsq : p^2∣N) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range p, SmallLevelAdditive.original k f (r+(j:ℝ)/p) s)=0 := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  obtain ⟨B,hB⟩:=additive_convergence_halfplane
    (polynomial_bound hf.zero hg k) (fullCoefficients_zero hf.zero k)
  refine ⟨B,?_⟩
  intro r s hs
  let a:=fullCoefficients f k
  have he : EqOn
      (fun y : ℝ => ∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I))
      (fun _ => (0:ℂ)) (Ioi 0) := by
    intro y hy
    have hh:=SmallLevelThirtySix.square_prime_average_zero hf.toEulerData hp hsq k
      (z:=(r:ℂ)+(y:ℂ)*I) (by simpa using hy)
    change completeTwist (fourier a) p ((r:ℂ)+(y:ℂ)*I)=0 at hh
    rw [←hh]
    unfold completeTwist
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  have hsum : mellin
      (fun y : ℝ => ∑ j∈Finset.range p, fourier a (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I)) s=
      ∑ j∈Finset.range p, SmallLevelAdditive.original k f (r+(j:ℝ)/p) s := by
    unfold mellin
    simp only [Finset.smul_sum]
    rw [integral_finsetSum (Finset.range p) (fun j _ => (hB (r+(j:ℝ)/p) s hs).1)]
    apply Finset.sum_congr rfl
    intro j _
    exact (hB (r+(j:ℝ)/p) s hs).2
  rw [←hsum,mellin_congr_positive he s]
  simp [mellin]

#print axioms original_square_prime_additive
end SmallLevelTaylor
end
end

/-! ## SmallLevelTaylorLeadingMellinV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTaylor

open Complex Filter Asymptotics Set Metric MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped NNReal ENNReal

theorem frickeTaylorPolynomial_one (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    {L r y : ℝ} (hL : 0<L) (hr : r≠0) (hy : 0<y) :
    frickeTaylorPolynomial k a L r 1 y=
      fourier a (((-1/(L*r):ℝ):ℂ)+((y/(L*r^2):ℝ):ℂ)*I) := by
  have hc : 0<L*r^2 := mul_pos hL (sq_pos_of_ne_zero hr)
  have hd : DifferentiableOn ℂ (deformed k a (-1/(L*r)) (L*r^2) y) (closedBall 0 (1/2)) := by
    intro u hu
    apply (deformed_analytic k ha _ hc hy _).differentiableAt.differentiableWithinAt
    simpa only [mem_closedBall,dist_zero_right] using hu
  unfold frickeTaylorPolynomial FormalMultilinearSeries.partialSum
  rw [Finset.sum_range_one]
  have hz := (hd.hasFPowerSeriesOnBall (R := (1/2:ℝ≥0)) (by norm_num)).coeff_zero
    (fun _ => ((y/r:ℝ):ℂ)*I)
  simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hz
  rw [hz]
  simp only [deformed,deformPoint,add_zero,one_pow,inv_one,one_mul,div_one]

theorem frickeTaylorPolynomial_one_mellin (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    {L r : ℝ} (hL : 0<L) (hr : r≠0) (s : ℂ) :
    mellin (frickeTaylorPolynomial k a L r 1) s=
      ((L*r^2:ℝ):ℂ)^s*mellin
        (fun y : ℝ => fourier a (((-1/(L*r):ℝ):ℂ)+(y:ℂ)*I)) s := by
  have hc : 0<L*r^2 := mul_pos hL (sq_pos_of_ne_zero hr)
  have he : EqOn (frickeTaylorPolynomial k a L r 1)
      (fun y : ℝ => fourier a (((-1/(L*r):ℝ):ℂ)+(((L*r^2)⁻¹*y:ℝ):ℂ)*I)) (Ioi 0) := by
    intro y hy
    rw [frickeTaylorPolynomial_one k ha hL hr hy]
    congr 1
    simp only [div_eq_inv_mul]
  rw [mellin_congr_positive he s]
  rw [mellin_comp_mul_left (fun y : ℝ => fourier a (((-1/(L*r):ℝ):ℂ)+(y:ℂ)*I)) s
    (inv_pos.mpr hc),Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hc.le,← Complex.cpow_neg,neg_neg,smul_eq_mul]

/-- The first actual Taylor row, with the literal additive Mellin transforms
and an explicitly constructed remainder analytic one strip farther left.
Higher Taylor rows require the remaining coefficient-Mellin identities. -/
theorem leading_taylor_mellin_row {L r : ℝ} (hL : 0<L) (hr : r≠0)
    (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → fourier a z=
      χ/(((Real.sqrt L:ℂ)*z)^k)*fourier a (-1/((L:ℂ)*z))) :
    ∃ B : ℝ, AnalyticOnNhd ℂ (mellin (frickeError k a L r χ 1)) {s : ℂ | B-1<s.re} ∧
      ∀ s : ℂ, B<s.re →
        SmallLevelAdditive.transform a r s-
          (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k))*((L*r^2:ℝ):ℂ)^s*
            SmallLevelAdditive.transform a (-1/(L*r)) s=
          mellin (frickeError k a L r χ 1) s := by
  obtain ⟨K,hK⟩ := frickeError_mellin_analytic hL hr k ha ha0 χ hF
  obtain ⟨B,hB⟩ := additive_convergence_halfplane ha ha0
  refine ⟨max B (K:ℝ),?_,?_⟩
  · intro s hs
    apply hK 1 s
    simp only [Set.mem_ofPred_eq,Nat.cast_one]
    change max B (K:ℝ)-1<s.re at hs
    linarith [le_max_right B (K:ℝ)]
  · intro s hs
    have hsB : B<s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hc : 0<L*r^2 := mul_pos hL (sq_pos_of_ne_zero hr)
    have hpoly : MellinConvergent (frickeTaylorPolynomial k a L r 1) s := by
      have he : EqOn (frickeTaylorPolynomial k a L r 1)
          (fun y : ℝ => fourier a (((-1/(L*r):ℝ):ℂ)+(((L*r^2)⁻¹*y:ℝ):ℂ)*I)) (Ioi 0) := by
        intro y hy
        rw [frickeTaylorPolynomial_one k ha hL hr hy]
        congr 1
        simp only [div_eq_inv_mul]
      apply (mellinConvergent_congr_positive he s).mpr
      exact (MellinConvergent.comp_mul_left (inv_pos.mpr hc)).mpr (hB (-1/(L*r)) s hsB).1
    have hm := (hasMellin_sub (hB r s hsB).1
      (hpoly.const_smul (χ/(((Real.sqrt L:ℂ)*(r:ℂ))^k)))).2
    rw [mellin_const_smul,frickeTaylorPolynomial_one_mellin k ha hL hr s,
      (hB r s hsB).2,(hB (-1/(L*r)) s hsB).2] at hm
    change mellin (frickeError k a L r χ 1) s=_ at hm
    simpa only [smul_eq_mul,mul_assoc] using hm.symm

#print axioms frickeTaylorPolynomial_one
#print axioms frickeTaylorPolynomial_one_mellin
#print axioms leading_taylor_mellin_row

end SmallLevelTaylor
end
end
