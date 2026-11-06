module

public import QuantitativeArithmeticQuadraticTwistInversionTheoryV4
public import SmallLevelContinuationTheoryV4
public import SmallLevelNormalizedFrickeV1
public import SmallLevelQuadraticExponentialTheoryV4
public import SmallLevelTaylorTheoryV4
public import SmallLevelTwentyOneLargeGridModelTheoryV4
public import SmallLevelTwentyOnePartnerModelsV1
public import SmallLevelTwentyOneReflectionAlgebraV1

/-! Consolidated chapter: SmallLevelTwentyOneChiFive. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneChiFiveEntireV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex Filter Set SmallLevelAdditive
open SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneLargeGridModel
open QuantitativeArithmeticSmallLevelNineteen
open scoped Topology

def gridCombination (V : Fin 210 → ℂ) : ℂ :=
  V (gridIndex 210 (by decide) 42)+V (gridIndex 210 (by decide) (-42))-
    (V (gridIndex 210 (by decide) 84)+V (gridIndex 210 (by decide) (-84)))

theorem gridCombination_original (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    gridCombination (gridVector 210 k f s)=quadraticCombination k f s := by
  unfold gridCombination quadraticCombination evenOne evenTwo
  simp only [gridVector_index,grid]
  norm_num

theorem gridCombination_meromorphic (G : ℂ → Fin 210 → ℂ) (s : ℂ)
    (hG : ∀ i, MeromorphicAt (fun z => G z i) s) :
    MeromorphicAt (fun z => gridCombination (G z)) s :=
  ((hG _).add (hG _)).sub ((hG _).add (hG _))

theorem gridCombination_analytic (G : ℂ → Fin 210 → ℂ) (s : ℂ)
    (hG : ∀ i, AnalyticAt ℂ (fun z => G z i) s) :
    AnalyticAt ℂ (fun z => gridCombination (G z)) s :=
  ((hG _).add (hG _)).sub ((hG _).add (hG _))

/-- The normal-form quadratic continuation is entire once the actual
large grid is available. Its possible quotient poles are all removed by
the shifted original-row obstruction. -/
theorem entire_of_continued_grid {f : ℕ → ℂ} {ε : ℂ}
    (S : ContinuedGrid f ε)
    (hE : SmallLevelTwentyOne.phaseRoot 1 ε= -1)
    (hu : SmallLevelTwentyOne.rootU f= -1) (hv : SmallLevelTwentyOne.rootV f=1)
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ))
    (B : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicNFAt G s)
    (hGF : ∀ s, B<s.re → G s=quadraticCombination 2 f s)
    (hreg : ∀ s, denominator 2 f s≠0 → AnalyticAt ℂ G s) :
    Differentiable ℂ G := by
  intro s
  by_cases hs : denominator 2 f s=0
  · have he : G=ᶠ[𝓝[≠] s] (fun z => gridCombination (S.values z)) := by
      apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max B S.bound)
      · exact fun z _ => (hG z).meromorphicAt
      · exact fun z _ => gridCombination_meromorphic S.values z
          (fun i => (S.normal i z).meromorphicAt)
      · intro z hz
        dsimp only
        rw [hGF z (lt_of_le_of_lt (le_max_left _ _) hz),
          S.agree z (lt_of_le_of_lt (le_max_right _ _) hz),gridCombination_original]
      · linarith
    have haG := gridCombination_analytic S.values s
      (S.analytic_at_denominator_root hE hu hv ha hs)
    have hn := ((hG s).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds haG.meromorphicNFAt).mp he
    exact ((analyticAt_congr hn).mpr haG).differentiableAt
  · exact (hreg s hs).differentiableAt

#print axioms entire_of_continued_grid
end SmallLevelTwentyOneChiFive
end
end

/-! ## SmallLevelTwentyOneChiFiveOldGridEntireV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex SmallLevelTwentyOnePartnerModels
open QuantitativeArithmeticSmallLevelNineteen

/-- An entire original42-grid makes the actual quadratic-five continuation
entire in every weight and for every Hecke2 eigenvalue. -/
theorem entire_of_old_grid {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (V : ℂ → Fin 42 → ℂ)
    (hV : ∀ i s, AnalyticAt ℂ (fun z => V z i) s)
    (hVF : ∀ s, BG<s.re → V s=SmallLevelTwentyOne.gridVector (2*m) f s)
    (B0 : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicNFAt G s)
    (hGF : ∀ s, B0<s.re → G s=quadraticCombination (2*m) f s) :
    Differentiable ℂ G := by
  obtain ⟨B1,H1,ha1,he1⟩ := original_partner_models hf ε hlaw BG V hV hVF
    (1/5) (by norm_num) (-10) (by norm_num)
  obtain ⟨B2,H2,ha2,he2⟩ := original_partner_models hf ε hlaw BG V hV hVF
    (-1/5) (by norm_num) 10 (by norm_num)
  obtain ⟨B3,H3,ha3,he3⟩ := original_partner_models hf ε hlaw BG V hV hVF
    (2/5) (by norm_num) (-5) (by norm_num)
  obtain ⟨B4,H4,ha4,he4⟩ := original_partner_models hf ε hlaw BG V hV hVF
    (-2/5) (by norm_num) 5 (by norm_num)
  let B := max (max B1 B2) (max B3 B4)
  have h1 : B1≤B := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : B2≤B := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : B3≤B := (le_max_left _ _).trans (le_max_right _ _)
  have h4 : B4≤B := (le_max_right _ _).trans (le_max_right _ _)
  apply SmallLevelContinuation.entire_of_halfplane_models
    (quadraticCombination (2*m) f) G B0 B hG hGF
    (fun n s => (H1 n s+H2 n s)-(H3 n s+H4 n s))
  · intro n s hs
    exact ((ha1 n s (by linarith)).add (ha2 n s (by linarith))).sub
      ((ha3 n s (by linarith)).add (ha4 n s (by linarith)))
  · intro n s hs
    rw [he1 n s (lt_of_le_of_lt h1 hs),he2 n s (lt_of_le_of_lt h2 hs),
      he3 n s (lt_of_le_of_lt h3 hs),he4 n s (lt_of_le_of_lt h4 hs)]
    rfl

#print axioms entire_of_old_grid
end SmallLevelTwentyOneChiFive
end
end

/-! ## SmallLevelTwentyOneChiFiveUniformOrderV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex Filter Set SmallLevelTaylor
open QuantitativeArithmeticSmallLevelNineteen (heckeScalar oppositeScalar)
open scoped Topology

theorem denominator_quadratic (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator (2*m) f s=1+((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s)+
      ((2:ℂ)^((m:ℂ)-s))^2 := by
  have hfirst := SmallLevelTaylor.hecke_first_scalar (by decide : 0<2) m (f 2) s
  have hsecond := SmallLevelTaylor.hecke_second_scalar (by decide : 0<2) m s
  have hh : heckeScalar (2*m) f s=((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s) := by
    simpa only [heckeScalar,Nat.cast_mul,Nat.cast_ofNat] using hfirst
  have ho : oppositeScalar (2*m) s=1+((2:ℂ)^((m:ℂ)-s))^2 := by
    simpa only [oppositeScalar,Nat.cast_ofNat,show (2:ℂ)^2=4 by norm_num] using
      congrArg (fun z : ℂ => 1+z) hsecond
  rw [denominator,hh,ho]
  ring

theorem uniform_product_identity {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=quadraticCombination (2*m) f s) :
    ∀ s, denominator (2*m) f s*G s=numerator m f s := by
  obtain ⟨C,hC⟩ := original_quotient_identity m hm hf
  have hleft := (denominator_entire (2*m) f).mul hG
  have hright := original_numerator_entire m hm hf
  intro s
  have he : (fun z => denominator (2*m) f z*G z)=ᶠ[𝓝[≠] s] numerator m f := by
    apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max B C)
    · exact fun z _ => (hleft.analyticAt z).meromorphicAt
    · exact fun z _ => (hright.analyticAt z).meromorphicAt
    · intro z hz
      dsimp only
      rw [hGF z (lt_of_le_of_lt (le_max_left _ _) hz)]
      exact (hC z (lt_of_le_of_lt (le_max_right _ _) hz)).symm
    · linarith
  exact (((hleft.analyticAt s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hright.analyticAt s).meromorphicNFAt).mp he).eq_of_nhds

theorem uniform_finiteOrder {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=quadraticCombination (2*m) f s) :
    FinitenessOriginalInput.FiniteOrder G := by
  apply SmallLevelQuadraticExponential.finiteOrder_of_quadratic
    ((Real.sqrt 2:ℂ)*f 2) (m:ℂ)
    (original_numerator_entire m hm hf).continuous
    (FinitenessInputBounds.bound_finiteOrder (original_numerator_bound m hm hf)) hG
  intro s
  rw [← denominator_quadratic]
  exact uniform_product_identity hm hf hG B hGF s

#print axioms denominator_quadratic
#print axioms uniform_finiteOrder
end SmallLevelTwentyOneChiFive
end
end

/-! ## SmallLevelTwentyOneChiFiveUniformLawsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex SmallLevelTwentyOneLargeGridModel

/-- Every original level21 solution in positive even weight has an entire
finite-order quadratic-five additive continuation with its coherent
conductor525 functional equation. The exceptional possible old-grid pole is
handled separately by the actual210-grid; no126-grid entireness is needed. -/
theorem original_uniform_entire_laws {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε ∧
      ∃ (B : ℝ) (G : ℂ → ℂ), Differentiable ℂ G ∧ FinitenessOriginalInput.FiniteOrder G ∧
        (∀ s, B<s.re → G s=quadraticCombination (2*m) f s) ∧
        (∀ s, G s=ε*(525:ℂ)^((m:ℂ)-s)*G (((2*m:ℕ):ℂ)-s)) := by
  obtain ⟨ε,hε,hlaw,BV,V,hV,hVF,hreg,_horder,hparam⟩ :=
    SmallLevelTwentyOneKnownWords.original_full_pole_bound hm hf
  obtain ⟨B,G,hG,hGF,hGreg,hgerm⟩ := original_quadratic_continuation m hm hf
  have hent : Differentiable ℂ G := by
    by_cases hp : ∃ j, meromorphicOrderAt (fun z => V z j) ((2*m:ℕ):ℂ)<0
    · obtain ⟨hm1,hE,hu,hv,ha⟩ := hparam hp
      subst m
      obtain ⟨S⟩ := original_continued_grid hf ε hε hlaw hE hu hv ha BV V hV hVF
        (fun i s hs => hreg s hs i)
      exact entire_of_continued_grid S hE hu hv ha B G hG hGF hGreg
    · have hVa (i : Fin 42) (s : ℂ) : AnalyticAt ℂ (fun z => V z i) s := by
        by_cases hs : s=((2*m:ℕ):ℂ)
        · subst s
          apply (hV i _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
          by_contra! hi
          exact hp ⟨i,hi⟩
        · exact hreg s hs i
      exact entire_of_old_grid hf ε hlaw BV V hVa hVF B G hG hGF
  have hfinite := uniform_finiteOrder hm hf hent B hGF
  have hc := original_center_laws hm hf ε hε hlaw
  have hr := (original_ramanujan_five_laws hm hf ε hε hlaw).2
  have hn := numerator_reflection m f ε (fun b => (hc b).2) hr
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have he := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) (((2*m:ℕ):ℂ)) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm
    (raw_quotient_reflection m f ε hn)
  refine ⟨ε,hε,hlaw,B,G,hent,hfinite,hGF,?_⟩
  simpa only [reflectionMultiplier_even] using he

#print axioms original_uniform_entire_laws
end SmallLevelTwentyOneChiFive
end
end

/-! ## SmallLevelTwentyOneChiFiveFrickeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelNineteen

def quadraticFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/5:ℝ))+
  fourier (fullCoefficients f k) (z+(-1/5:ℝ))-
  fourier (fullCoefficients f k) (z+(2/5:ℝ))-
  fourier (fullCoefficients f k) (z+(-2/5:ℝ))

/-- Genuine quadratic-twist Fourier transformation for every original
level21 solution in positive even weight, retaining its coherent sign. -/
theorem original_quadratic_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε ∧
      ∀ z : ℂ, 0<z.im → quadraticFourier (2*m) f z=
        (ε*I^(2*m))/(((Real.sqrt 525:ℂ)*z)^(2*m))*
          quadraticFourier (2*m) f (-1/((525:ℂ)*z)) := by
  obtain ⟨ε,hε,hlaw,B,G,hent,hfinite,hGF,hFE⟩ := original_uniform_entire_laws hm hf
  obtain ⟨σ,_hσ,hgrowth⟩ := hf.growth
  refine ⟨ε,hε,hlaw,?_⟩
  apply QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (by decide : 0<525) hf.zero hgrowth (1/5) (-1/5) (2/5) (-2/5) G hent hfinite
  · intro s hs
    rw [hGF s hs]
    unfold quadraticCombination evenOne evenTwo
    ring
  · rcases hε with rfl|rfl <;> norm_num
  · have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
    simpa only [Nat.cast_ofNat,he] using hFE

#print axioms original_quadratic_fricke
end SmallLevelTwentyOneChiFive
end
end

/-! ## SmallLevelTwentyOneChiFivePairsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex Matrix UpperHalfPlane SmallLevelNormalized
open FinitenessOriginalFourier FinitenessFourierConstruction FinitenessAnalyticReconstruction
open scoped MatrixGroups ModularForm

theorem twist_five (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (z : ℂ) :
    twist F 5 z=F (z+1/5)+F (z-1/5)+F (z+2/5)+F (z-2/5) := by
  unfold twist
  rw [show (Finset.range 5).filter (fun a => Nat.Coprime a 5)={1,2,3,4} by decide]
  norm_num
  rw [show z+3/5=(z-2/5)+1 by ring,show z+4/5=(z-1/5)+1 by ring,hp,hp]
  ring

/-- The original Ramanujan5 law and quadratic5 law separate into the two
actual even-pair Fricke laws, with the same original sign. -/
theorem second_pair_law {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*quadraticFourier k f (-1/((525:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      fourier (fullCoefficients f k) (z+2/5)+fourier (fullCoefficients f k) (z-2/5)=
        (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*
          (fourier (fullCoefficients f k) (-1/((525:ℂ)*z)+2/5)+
            fourier (fullCoefficients f k) (-1/((525:ℂ)*z)-2/5)) := by
  intro z hz
  have hr := hlaw 5 (by decide) z hz
  rw [show Nat.lcm 21 (5^2)=525 by decide,root_five,one_mul,
    twist_five _ (periodic _),twist_five _ (periodic _)] at hr
  have hc := hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  norm_num only [Nat.cast_ofNat] at hr
  simp only [sub_eq_add_neg] at hr hc ⊢
  linear_combination (hr-hc)/2

/-- The separated quadratic relation in normalized slash notation. -/
theorem second_pair_slash {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*quadraticFourier k f (-1/((525:ℂ)*z))) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 21 (by decide))⁻¹*translation (2/5)*fricke 525 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 21 (by decide))⁻¹*translation (-2/5)*fricke 525 (by decide)))=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (2/5))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-2/5)) := by
  have h := pair_of_fricke 21 525 k (by decide) (by decide) (2/5)
    (fourier (fullCoefficients f k)) (ε*Complex.I^k) 1 (Or.inl rfl)
    (by
      intro z hz
      simpa [FinitenessNormalizedTwistProduct.root,twist,Finset.sum_range_succ] using
        hlaw 1 (by decide) z hz)
    (by
      simpa only [one_mul,Complex.ofReal_div,Complex.ofReal_ofNat,Nat.cast_ofNat] using
        second_pair_law ε hlaw hquad)
  have hfun : (fun z : ℍ => fourier (fullCoefficients f k) z)=SmallLevelOriginal.fourierFunction k f := by
    funext z
    rfl
  rw [hfun] at h
  simpa only [one_smul,neg_div] using h

#print axioms second_pair_law
#print axioms second_pair_slash
end SmallLevelTwentyOneChiFive
end
end

/-! ## SmallLevelTwentyOneChiFiveFirstPairV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex Matrix UpperHalfPlane SmallLevelNormalized
open FinitenessOriginalFourier FinitenessFourierConstruction FinitenessAnalyticReconstruction
open scoped MatrixGroups ModularForm

/-- The original Ramanujan5 law and quadratic5 law separate into the first
actual even-pair Fricke laws, with the same original sign. -/
theorem first_pair_law {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*quadraticFourier k f (-1/((525:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      fourier (fullCoefficients f k) (z+1/5)+fourier (fullCoefficients f k) (z-1/5)=
        (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*
          (fourier (fullCoefficients f k) (-1/((525:ℂ)*z)+1/5)+
            fourier (fullCoefficients f k) (-1/((525:ℂ)*z)-1/5)) := by
  intro z hz
  have hr := hlaw 5 (by decide) z hz
  rw [show Nat.lcm 21 (5^2)=525 by decide,root_five,one_mul,
    twist_five _ (periodic _),twist_five _ (periodic _)] at hr
  have hc := hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  norm_num only [Nat.cast_ofNat] at hr
  simp only [sub_eq_add_neg] at hr hc ⊢
  linear_combination (hr+hc)/2

/-- The first separated quadratic relation in normalized slash notation. -/
theorem first_pair_slash {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*Complex.I^k)/(((Real.sqrt 525:ℂ)*z)^k)*quadraticFourier k f (-1/((525:ℂ)*z))) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 21 (by decide))⁻¹*translation (1/5)*fricke 525 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 21 (by decide))⁻¹*translation (-1/5)*fricke 525 (by decide)))=
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/5))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1/5)) := by
  have h := pair_of_fricke 21 525 k (by decide) (by decide) (1/5)
    (fourier (fullCoefficients f k)) (ε*Complex.I^k) 1 (Or.inl rfl)
    (by
      intro z hz
      simpa [FinitenessNormalizedTwistProduct.root,twist,Finset.sum_range_succ] using
        hlaw 1 (by decide) z hz)
    (by
      simpa only [one_mul,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one,Nat.cast_ofNat] using
        first_pair_law ε hlaw hquad)
  have hfun : (fun z : ℍ => fourier (fullCoefficients f k) z)=SmallLevelOriginal.fourierFunction k f := by
    funext z
    rfl
  rw [hfun] at h
  simpa only [one_smul,neg_div] using h

#print axioms first_pair_law
#print axioms first_pair_slash
end SmallLevelTwentyOneChiFive
end
end
