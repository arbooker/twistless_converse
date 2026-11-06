module

public import QuantitativeArithmeticGaussianStripTheoryV4
public import QuantitativeArithmeticQuadraticTwistInversionTheoryV4
public import QuantitativeArithmeticTwoSequenceStripRowsV1
public import SmallLevelAdditiveMellinV1
public import SmallLevelRamanujanAdditiveV1
public import SmallLevelTaylorRowCoefficientsV1

/-! Consolidated chapter: SmallLevelAdditive. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticAdditiveInitialRapidV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelAdditive
open Complex Filter Asymptotics FinitenessPolynomialSeries QuantitativeArithmeticGaussianStrip

theorem transform_rapid_halfplane {a : ℕ → ℂ} (ha : PolynomialBound a) :
    ∃ B : ℝ,∀ r σ : ℝ,B<σ → RapidLine (transform a r) σ := by
  obtain ⟨d,hd⟩ := FinitenessAllLevelMellinDirichlet.polynomial_growth ha
  refine ⟨(d:ℝ)+1,?_⟩
  intro r σ hσ
  have hs0 : 0<σ := by linarith [Nat.cast_nonneg (α:=ℝ) d]
  let K : ℝ := ∑' n : ℕ,‖LSeries.term (coefficients a r) (σ:ℂ) n‖
  have hK : 0≤K := tsum_nonneg (fun _ => norm_nonneg _)
  have hL (s : ℂ) (hs : s.re=σ) : ‖LSeries (coefficients a r) s‖≤K := by
    have hsum := summable_at hd r (by simpa only [hs] using hσ : (d:ℝ)+1<s.re)
    apply (norm_tsum_le_tsum_norm hsum.norm).trans_eq
    apply tsum_congr
    intro n
    simp only [LSeries.norm_term_eq,hs,Complex.ofReal_re]
  have hpow (s : ℂ) (hs : s.re=σ) :
      ‖((2*Real.pi:ℝ):ℂ)^(-s)‖=(2*Real.pi)^(-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re,hs]
  have hg : FinitenessBoundaryDecay.Rapid Complex.Gamma σ := by
    simpa only [Complex.ofReal_zero,add_zero] using
      (FinitenessBoundaryDecay.gamma_shift (σ:=σ) (α:=0) (by simpa using hs0))
  apply rapidLine_of_rapid
  apply FinitenessBoundaryDecay.of_norm_le hg (by positivity : 0≤(2*Real.pi)^(-σ)*K)
  intro s hs
  rw [transform,norm_mul,norm_mul,hpow s hs]
  have hh := mul_le_mul_of_nonneg_left (hL s hs)
    (by positivity : 0≤‖Gamma s‖*(2*Real.pi)^(-σ))
  nlinarith
#print axioms transform_rapid_halfplane
end SmallLevelAdditive
end
end

/-! ## QuantitativeArithmeticAdditiveInitialStripBoundV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelAdditive
open Complex MeasureTheory
open FinitenessPolynomialSeries FinitenessFourierConstruction QuantitativeArithmeticMellinStrip

theorem common_bounded_halfplane {a : ℕ → ℂ} (ha : PolynomialBound a) (ha0 : a 0=0) :
    ∃ B : ℝ,∀ r : ℝ,BoundedSubstrips B (transform a r) := by
  obtain ⟨B,hB⟩ := SmallLevelTaylor.additive_convergence_halfplane ha ha0
  refine ⟨B,?_⟩
  intro r l u hl hu
  obtain ⟨C,hC,hbound⟩ := bounded_strip _ l u ((hB r l hl).1) ((hB r u hu).1)
  refine ⟨C,hC,?_⟩
  intro s hsl hsu
  rw [← (hB r s (hl.trans_le hsl)).2]
  exact hbound s hsl hsu

theorem original_bounded_halfplane {N k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ B : ℝ,∀ r : ℝ,BoundedSubstrips B (original k f r) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  exact common_bounded_halfplane (FinitenessOriginalFourier.polynomial_bound hf.zero hg k)
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero k)
#print axioms original_bounded_halfplane
end SmallLevelAdditive
end
end

/-! ## SmallLevelAdditiveGridV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelAdditive
open Complex

theorem phase_add_int (r : ℝ) (m : ℤ) (n : ℕ) : phase (r+(m:ℝ)) n=phase r n := by
  unfold phase
  have he : (((2*Real.pi*(n:ℝ)*(r+(m:ℝ)):ℝ):ℂ)*I)=
      (((2*Real.pi*(n:ℝ)*r:ℝ):ℂ)*I)+(((n:ℤ)*m:ℤ):ℂ)*(2*Real.pi*I) := by
    push_cast
    ring
  rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]

theorem transform_add_int (a : ℕ → ℂ) (r : ℝ) (m : ℤ) (s : ℂ) :
    transform a (r+(m:ℝ)) s=transform a r s := by
  have he : coefficients a (r+(m:ℝ))=coefficients a r := by
    funext n
    rw [coefficients,coefficients,phase_add_int]
  rw [transform,transform,he]

def grid (k : ℕ) (f : ℕ → ℂ) (Q : ℕ) (j : ℤ) (s : ℂ) : ℂ :=
  original k f ((j:ℝ)/(Q:ℝ)) s

theorem grid_period (k : ℕ) (f : ℕ → ℂ) {Q : ℕ} (hQ : 0<Q) (j : ℤ) (s : ℂ) :
    grid k f Q (j+(Q:ℤ)) s=grid k f Q j s := by
  have hQ0 : (Q:ℝ)≠0 := by exact_mod_cast ne_of_gt hQ
  have he : (((j+(Q:ℤ):ℤ):ℝ)/(Q:ℝ))=(j:ℝ)/(Q:ℝ)+(1:ℤ) := by
    push_cast
    field_simp
  unfold grid original
  rw [he,transform_add_int]

theorem grid_mod (k : ℕ) (f : ℕ → ℂ) {Q : ℕ} (hQ : 0<Q) (j : ℤ) (s : ℂ) :
    grid k f Q (j%(Q:ℤ)) s=grid k f Q j s := by
  have hQ0 : (Q:ℝ)≠0 := by exact_mod_cast ne_of_gt hQ
  have hj : (j:ℝ)=((j%(Q:ℤ):ℤ):ℝ)+(Q:ℝ)*((j/(Q:ℤ):ℤ):ℝ) := by
    have h := (Int.emod_add_ediv_mul j (Q:ℤ)).symm
    rw [mul_comm (j/(Q:ℤ))] at h
    exact_mod_cast h
  have he : (j:ℝ)/(Q:ℝ)=((j%(Q:ℤ):ℤ):ℝ)/(Q:ℝ)+((j/(Q:ℤ):ℤ):ℝ) := by
    rw [hj]
    field_simp
  unfold grid original
  rw [he,transform_add_int]

/-- Divisibility places each primitive translation in the same integer grid. -/
theorem grid_translation {Q q : ℕ} (hQ : 0<Q) (hq : 0<q) (hqQ : q∣Q) (t : ℤ) (j : ℕ) :
    (t:ℝ)/(Q:ℝ)+(j:ℝ)/(q:ℝ)=((t+(j:ℤ)*(Q/q:ℕ):ℤ):ℝ)/(Q:ℝ) := by
  have hq0 : (q:ℝ)≠0 := by exact_mod_cast ne_of_gt hq
  have hQ0 : (Q:ℝ)≠0 := by exact_mod_cast ne_of_gt hQ
  have hd : (Q:ℝ)=(q:ℝ)*(Q/q:ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hqQ).symm
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast]
  field_simp
  rw [hd]
  ring

#print axioms phase_add_int
#print axioms grid_mod
end SmallLevelAdditive
end
end

/-! ## SmallLevelFrickeGridClosureV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelAdditive
open Complex SmallLevelTaylor FinitenessRamanujanSum

/-- The divisibility condition for a closed Taylor row gives the exact
integer index of its Fricke partner. Negative translations are included. -/
theorem fricke_grid_partner {Q L : ℕ} (hQ : 0<Q) (hL : 0<L) {t d : ℤ}
    (ht : t≠0) (hd : (L:ℤ)*d=(Q:ℤ)^2) (htd : t∣d) :
    -1/((L:ℝ)*((t:ℝ)/(Q:ℝ)))=((- (d/t):ℤ):ℝ)/(Q:ℝ) := by
  have hQ0 : (Q:ℝ)≠0 := by exact_mod_cast ne_of_gt hQ
  have hL0 : (L:ℝ)≠0 := by exact_mod_cast ne_of_gt hL
  have ht0 : (t:ℝ)≠0 := by exact_mod_cast ht
  have hdt : (d:ℝ)=(t:ℝ)*((d/t:ℤ):ℝ) := by
    exact_mod_cast (Int.mul_ediv_cancel' htd).symm
  have hLd : (L:ℝ)*(d:ℝ)=(Q:ℝ)^2 := by exact_mod_cast hd
  rw [hdt] at hLd
  simp only [Int.cast_neg]
  field_simp
  nlinarith [hLd]

theorem ramanujanAdditive_grid (k : ℕ) (f : ℕ → ℂ) {Q q : ℕ}
    (hQ : 0<Q) (hq : 0<q) (hqQ : q∣Q) (t : ℤ) (s : ℂ) :
    ramanujanAdditive k f q ((t:ℝ)/(Q:ℝ)) s=
      ∑ j∈residues q, grid k f Q (t+(j:ℤ)*(Q/q:ℕ)) s := by
  unfold ramanujanAdditive grid
  apply Finset.sum_congr rfl
  intro j _
  rw [grid_translation hQ hq hqQ]

/-- Every shifted source in the Taylor row is on the same Q-grid. The
integer index is independent of the Taylor order and the Mellin variable. -/
theorem ramanujanTaylorSum_grid (k : ℕ) (f : ℕ → ℂ) {Q q L : ℕ}
    (hQ : 0<Q) (hq : 0<q) (hqQ : q∣Q) (hL : 0<L) {t d : ℤ}
    (ht : t≠0) (hd : (L:ℤ)*d=(Q:ℤ)^2) (htd : t∣d) (M : ℕ) (s : ℂ) :
    ramanujanTaylorSum k f q L ((t:ℝ)/(Q:ℝ)) M s=
      ∑ n∈Finset.range M,
        (I*(L:ℂ)*(((t:ℝ)/(Q:ℝ):ℝ):ℂ))^n*Ring.choose (s+(n:ℂ)-(k:ℂ)) n*
          (∑ j∈residues q, grid k f Q (- (d/t)+(j:ℤ)*(Q/q:ℕ)) (s+(n:ℂ))) := by
  unfold ramanujanTaylorSum
  apply Finset.sum_congr rfl
  intro n _
  rw [fricke_grid_partner hQ hL ht hd htd,ramanujanAdditive_grid k f hQ hq hqQ]
  simp only [Complex.ofReal_natCast]

/-- Folding the integer grid to Q residues changes none of its values,
including at poles of totalized Dirichlet expressions. -/
theorem ramanujan_grid_mod (k : ℕ) (f : ℕ → ℂ) {Q : ℕ} (hQ : 0<Q)
    (q : ℕ) (t : ℤ) (s : ℂ) :
    (∑ j∈residues q, grid k f Q ((t+(j:ℤ)*(Q/q:ℕ))%(Q:ℤ)) s)=
      ∑ j∈residues q, grid k f Q (t+(j:ℤ)*(Q/q:ℕ)) s := by
  apply Finset.sum_congr rfl
  intro j _
  exact grid_mod k f hQ _ s

#print axioms fricke_grid_partner
#print axioms ramanujanTaylorSum_grid
#print axioms ramanujan_grid_mod
end SmallLevelAdditive
end
end

/-! ## SmallLevelSingleTranslateInversionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelAdditive
open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
open FinitenessFourierConstruction MeasureTheory

theorem full_translate (f : ℕ→ℂ) (k : ℕ) (r : ℝ) :
    fullCoefficients (coefficients f r) k=coefficients (fullCoefficients f k) r := by
  funext n
  simp only [fullCoefficients,FinitenessGrowthNormalization.normalized,coefficients]
  ring

/-- Mellin inversion for one additive translate, from an actual entire
finite-order continuation and its reflected functional equation. -/
theorem single_translate_fricke {N k : ℕ} (hN : 0<N) {f : ℕ→ℂ}
    (hf0 : f 0=0) {τ : ℝ} (hg : f=O[atTop] (fun n : ℕ => (n:ℝ)^τ))
    (r : ℝ) (Q : ℂ→ℂ) (hQ : Differentiable ℂ Q) (hfinite : FiniteOrder Q)
    {B : ℝ} (hinit : ∀ s,B<s.re → Q s=original k f r s)
    {ε : ℂ} (hε : ‖ε‖=1)
    (hFE : ∀ s,Q s=ε*(N:ℂ)^((k:ℂ)/2-s)*Q ((k:ℂ)-s)) :
    ∀ z : ℂ,0<z.im → fourier (fullCoefficients f k) (z+r)=
      (ε*I^k)/(((Real.sqrt N:ℂ)*z)^k)*fourier (fullCoefficients f k) (-1/((N:ℂ)*z)+r) := by
  obtain ⟨C,hC⟩:=common_halfplane (polynomial_bound hf0 hg k) (fullCoefficients_zero hf0 k)
  have hi : ∀ s,max B C<s.re → Q s=
      mellin (FinitenessAllLevelAxisDecay.axis 1 (fullCoefficients (coefficients f r) k)) s := by
    intro s hs
    rw [hinit s ((le_max_left _ _).trans_lt hs),full_translate]
    have haxis : FinitenessAllLevelAxisDecay.axis 1 (coefficients (fullCoefficients f k) r)=
        (fun t : ℝ => fourier (fullCoefficients f k) ((r:ℂ)+(t:ℂ)*I)) :=
      funext (axis_one_translate _ r)
    rw [haxis]
    exact (hC r s ((le_max_right _ _).trans_lt hs)).2.symm
  have he:=QuantitativeArithmeticQuadraticTwistInversion.unscaled_mellin_fricke hN
    (coefficients_zero hf0 r) (coefficients_growth hg r) Q hQ hfinite hi hε hFE
  intro z hz
  simpa only [full_translate,fourier_translate] using he z hz

#print axioms full_translate
#print axioms single_translate_fricke
end SmallLevelAdditive
end
end
