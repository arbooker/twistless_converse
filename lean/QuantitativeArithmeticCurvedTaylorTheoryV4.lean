module

public import QuantitativeArithmeticMellinTransportTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticCurvedTaylor. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticCurvedLaplaceContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex Filter Set MeasureTheory SmallLevelAdditive
open FinitenessPolynomialSeries
open scoped Topology

/-- Full local analytic transport to a one-sided Laplace continuation with
only a possible simple pole at zero. The initial transform is the actual
integral of the logarithmically parametrized weighted curved ray. -/
theorem laplace_continuation (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) {c : ℝ} (hc : 0<c) (β r : ℝ) (hr : r≠0)
    (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (hGF : ∀ s, BG<s.re → G s=transform a β s) :
    ∃ (B : ℝ) (J : ℂ → ℂ), (∀ s, MeromorphicAt J s) ∧
      (∀ s, s≠0 → AnalyticAt ℂ J s) ∧
      (-1:WithTop ℤ)≤meromorphicOrderAt J 0 ∧
      ∀ s : ℂ, s.re<B → J s=
        QuantitativeArithmeticDilationLaplace.transform
          (fun t => ((Real.exp t:ℝ):ℂ)^(-(k:ℂ))*curved k a β c r (Real.exp t)⁻¹) s := by
  obtain ⟨B,U,hU,hUF⟩ := meromorphic_continuation k ha ha0 hc β r 1 hr zero_lt_one BG G hG hGF
  have hUa := analytic_away_weight k ha ha0 hc β r 1 hr zero_lt_one BG G hG hGa hGo hGF B U hU hUF
  have hUo := weight_pole_bound k ha ha0 hc β r 1 hr zero_lt_one BG G hG hGa hGo hGF B U hU hUF
  obtain ⟨hJ,hJa,hJo⟩ := QuantitativeArithmeticMellinTransport.reflected_pole_bound
    k U (fun s => (hU s).meromorphicAt) hUa hUo
  refine ⟨(k:ℝ)-B,fun z => U ((k:ℂ)-z),hJ,hJa,hJo,?_⟩
  intro s hs
  rw [QuantitativeArithmeticMellinTransport.curved_laplace_identity]
  apply hUF
  simp only [Complex.sub_re,Complex.natCast_re]
  linarith

#print axioms laplace_continuation
end QuantitativeArithmeticCurvedTaylor
end
end

/-! ## QuantitativeArithmeticCurvedMobiusGeometryV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex SmallLevelTaylor

/-- Algebraic form of a fractional-linear image near a finite cusp. -/
theorem fractional_curve (A B C D x t : ℂ) (hC : C≠0) (ht : t≠0)
    (hd : C*(x+I/t)+D≠0) :
    (A*(x+I/t)+B)/(C*(x+I/t)+D)=
      A/C+(t*(A*D-B*C)/C^2)*I/(1-(x+D/C)*t*I) := by
  have he : C*(x+I/t)+D=(C*I/t)*(1-(x+D/C)*t*I) := by
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have hh : 1-(x+D/C)*t*I≠0 := by
    intro h
    apply hd
    rw [he,h,mul_zero]
  have h1 : (x*t+I)*C+t*D≠0 := by
    have hp : (x*t+I)*C+t*D=t*(C*(x+I/t)+D) := by field_simp
    rw [hp]
    exact mul_ne_zero ht hd
  have h2 : C-I*t*(x*C+D)≠0 := by
    have hp : C-I*t*(x*C+D)=C*(1-(x+D/C)*t*I) := by field_simp
    rw [hp]
    exact mul_ne_zero hC hh
  field_simp [hC,ht,hd,hh,h1,h2]
  ring_nf
  norm_num [Complex.I_sq]

/-- Exact Möbius geometry for the real parameters used in curved Mellin
transport. The nonvertical case is enough for the level-25 cusp matrices. -/
theorem mobius_deform_point (A B C D x t : ℝ) (hC : C≠0) (ht : 0<t)
    (_hd : A*D-B*C≠0) (_hx : x+D/C≠0) :
    ((A:ℂ)*((x:ℂ)+I/(t:ℂ))+(B:ℂ))/((C:ℂ)*((x:ℂ)+I/(t:ℂ))+(D:ℂ))=
      deformPoint (A/C) (C^2/(A*D-B*C)) t
        (((t/(-1/(x+D/C)):ℝ):ℂ)*I) := by
  have hCc : (C:ℂ)≠0 := ofReal_ne_zero.mpr hC
  have htc : (t:ℂ)≠0 := ofReal_ne_zero.mpr ht.ne'
  have hden : (C:ℂ)*((x:ℂ)+I/(t:ℂ))+(D:ℂ)≠0 := by
    intro hh
    have hi := congrArg Complex.im hh
    have hi' : C/t=0 := by
      simpa [Complex.add_im,Complex.mul_im,Complex.div_im] using hi
    exact (div_ne_zero hC ht.ne') hi'
  rw [fractional_curve _ _ _ _ _ _ hCc htc hden]
  unfold deformPoint
  push_cast
  congr 1
  have hnum : (t/(C^2/(A*D-B*C)):ℝ)=t*(A*D-B*C)/C^2 := by field_simp
  have hparam : (t/(-1/(x+D/C)):ℝ)= -(x+D/C)*t := by field_simp
  have hcnum := congrArg (fun y : ℝ => (y:ℂ)) hnum
  have hcparam := congrArg (fun y : ℝ => (y:ℂ)) hparam
  push_cast at hcnum hcparam
  rw [hcnum,hcparam]
  ring

#print axioms fractional_curve
#print axioms mobius_deform_point
end QuantitativeArithmeticCurvedTaylor
end
end

/-! ## QuantitativeArithmeticCurvedSlashGeometryV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex SmallLevelTaylor FinitenessPolynomialSeries FinitenessFourierConstruction

theorem denominator_curve (C D x y : ℝ) (hC : C≠0) (hy : 0<y) :
    (C:ℂ)*((x:ℂ)+I*(y:ℂ))+(D:ℂ)=
      ((C:ℂ)*I*(y:ℂ))*(1+(((y⁻¹/(-1/(x+D/C)):ℝ):ℂ)*I)) := by
  have hparam : (y⁻¹/(-1/(x+D/C)):ℝ)= -(x+D/C)/y := by field_simp
  rw [hparam]
  push_cast
  have hCc : (C:ℂ)≠0 := ofReal_ne_zero.mpr hC
  have hyc : (y:ℂ)≠0 := ofReal_ne_zero.mpr hy.ne'
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- The raw weight factor and Möbius map are exactly a weighted curved ray.
The determinant normalization of the slash operator is a constant multiplier. -/
theorem raw_slash_curved (k : ℕ) (a : ℕ → ℂ) (A B C D x y : ℝ)
    (hC : C≠0) (hy : 0<y) (hd : A*D-B*C≠0) (hx : x+D/C≠0) :
    (((C:ℂ)*((x:ℂ)+I*(y:ℂ))+(D:ℂ))^k)⁻¹*
      fourier a (((A:ℂ)*((x:ℂ)+I*(y:ℂ))+(B:ℂ))/
        ((C:ℂ)*((x:ℂ)+I*(y:ℂ))+(D:ℂ)))=
      (((C:ℂ)*I)^k)⁻¹*((y:ℂ)^(-(k:ℂ))*
        curved k a (A/C) (C^2/(A*D-B*C)) (-1/(x+D/C)) y⁻¹) := by
  have hp := mobius_deform_point A B C D x y⁻¹ hC (inv_pos.mpr hy) hd hx
  simp only [ofReal_inv,div_inv_eq_mul] at hp
  rw [hp,denominator_curve C D x y hC hy]
  unfold curved deformed
  rw [Complex.cpow_neg,Complex.cpow_natCast]
  simp only [mul_pow,mul_inv_rev]
  ring

#print axioms denominator_curve
#print axioms raw_slash_curved
end QuantitativeArithmeticCurvedTaylor
end
end

/-! ## QuantitativeArithmeticCurvedSlashContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticCurvedTaylor
open Complex Filter Set MeasureTheory SmallLevelAdditive
open FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology

def rawSlashRay (k : ℕ) (a : ℕ → ℂ) (A B C D x y : ℝ) : ℂ :=
  (((C:ℂ)*((x:ℂ)+I*(y:ℂ))+(D:ℂ))^k)⁻¹*
    fourier a (((A:ℂ)*((x:ℂ)+I*(y:ℂ))+(B:ℂ))/
      ((C:ℂ)*((x:ℂ)+I*(y:ℂ))+(D:ℂ)))

theorem laplace_const_mul (H : ℝ → ℂ) (c s : ℂ) :
    QuantitativeArithmeticDilationLaplace.transform (fun t => c*H t) s=
      c*QuantitativeArithmeticDilationLaplace.transform H s := by
  unfold QuantitativeArithmeticDilationLaplace.transform
  simp_rw [mul_assoc]
  exact integral_const_mul c _

/-- Actual fractional-linear Fourier transport, before the constant determinant
normalization. The only analytic premise is the additive transform at A/C. -/
theorem raw_slash_laplace_continuation (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) (A B C D x : ℝ) (hC : C≠0) (hd : 0<A*D-B*C)
    (hx : x+D/C≠0) (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (hGF : ∀ s, BG<s.re → G s=transform a (A/C) s) :
    ∃ (BJ : ℝ) (J : ℂ → ℂ), (∀ s, MeromorphicAt J s) ∧
      (∀ s, s≠0 → AnalyticAt ℂ J s) ∧
      (-1:WithTop ℤ)≤meromorphicOrderAt J 0 ∧
      ∀ s : ℂ, s.re<BJ → J s=
        QuantitativeArithmeticDilationLaplace.transform
          (fun t => rawSlashRay k a A B C D x (Real.exp t)) s := by
  have hc : 0<C^2/(A*D-B*C) := div_pos (sq_pos_of_ne_zero hC) hd
  have hr : -1/(x+D/C)≠0 := div_ne_zero (by norm_num) hx
  obtain ⟨BJ,U,hU,hUa,hUo,hUF⟩ := laplace_continuation k ha ha0 hc (A/C)
    (-1/(x+D/C)) hr BG G hG hGa hGo hGF
  let c : ℂ := (((C:ℂ)*I)^k)⁻¹
  let H : ℝ → ℂ := fun t => ((Real.exp t:ℝ):ℂ)^(-(k:ℂ))*
    curved k a (A/C) (C^2/(A*D-B*C)) (-1/(x+D/C)) (Real.exp t)⁻¹
  have he : (fun t => rawSlashRay k a A B C D x (Real.exp t))=fun t => c*H t := by
    funext t
    exact raw_slash_curved k a A B C D x (Real.exp t) hC (Real.exp_pos t) hd.ne' hx
  refine ⟨BJ,fun z => c*U z,fun s => analyticAt_const.meromorphicAt.mul (hU s),
    fun s hs => analyticAt_const.mul (hUa s hs),?_,?_⟩
  · change (-1:WithTop ℤ)≤meromorphicOrderAt ((fun _ : ℂ => c)*U) 0
    rw [meromorphicOrderAt_mul analyticAt_const.meromorphicAt (hU 0)]
    have hh := add_le_add (analyticAt_const (v:=c) (x:=(0:ℂ))).meromorphicOrderAt_nonneg hUo
    simpa only [zero_add] using hh
  · intro s hs
    change c*U s=_
    rw [he,laplace_const_mul,hUF s hs]

#print axioms raw_slash_laplace_continuation
end QuantitativeArithmeticCurvedTaylor
end
end
