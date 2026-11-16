module

public import QuantitativeMaassPoincareGradientIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass
open MaassDifferential

/- These are the prescribed-overlap versions of the existing fixed-compact
estimates. Retaining M is necessary when the compact set grows with t. -/

theorem compact_poincare_derivative_sum_of_overlap (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (M : ℕ) (hM : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ M) :
    ∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K →
      ∀ Z : Point,0<Z.2 → ∃ S : Finset (gamma N),S.card≤M ∧
        (∀ w : Point,dir w (congruencePoincareCartesian N u.toFun) Z=
          ∑ g∈S,dir w (u.toFun ∘ integralCuspChart (representative g)) Z) ∧
        (∀ g∉S,g•cartesianLift Z∉K) := by
  classical
  intro u hu Z hZ
  let hfin := compact_orbit_point_finite (G := gamma N) K hK (cartesianLift Z)
  let S := hfin.toFinset
  have hS (g : gamma N) : g∈S ↔ g•cartesianLift Z∈K := hfin.mem_toFinset
  obtain ⟨T,U,hU,hT⟩ := compact_orbit_locally_finite (G := gamma N) K hK (cartesianLift Z)
  have hST : S⊆T := by
    intro g hg
    by_contra hn
    exact hT _ (mem_of_mem_nhds hU) g hn ((hS g).mp hg)
  have hout (y : ℍ) (hy : y∈U) (g : gamma N) (hg : g∉T) :
      upperFunction u.toFun (g•y)=0 := by
    by_contra hn
    exact hT y hy g hg (hu (subset_tsupport _ hn))
  have he : congruencePoincareCartesian N u.toFun =ᶠ[𝓝 Z]
      fun W => ∑ g∈T,u.toFun (integralCuspChart (representative g) W) := by
    filter_upwards [(cartesianLift_continuousAt Z hZ).preimage_mem_nhds hU,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW hpos
    change poincareSum (G := gamma N) (upperFunction u.toFun) (cartesianLift W)=_
    rw [show poincareSum (G := gamma N) (upperFunction u.toFun) (cartesianLift W)=
      ∑ g∈T,upperFunction u.toFun (g•cartesianLift W) from tsum_eq_sum (hout _ hW)]
    exact Finset.sum_congr rfl (fun g _ => congruence_pullback_cartesian N u.toFun g W hpos)
  refine ⟨S,hM _ S (fun g hg => (hS g).mp hg),?_,fun g hg => mt (hS g).mpr hg⟩
  intro w
  calc
    dir w (congruencePoincareCartesian N u.toFun) Z=
        dir w (fun W => ∑ g∈T,u.toFun (integralCuspChart (representative g) W)) Z := by
      unfold dir D
      rw [he.fderiv_eq]
    _ = ∑ g∈T,dir w (u.toFun ∘ integralCuspChart (representative g)) Z :=
      dir_finset_sum T _ (isOpen_lt continuous_const continuous_snd)
        (fun g _ => integralCuspChart_pullback_smooth (representative g) u.smooth) hZ w
    _ = ∑ g∈S,dir w (u.toFun ∘ integralCuspChart (representative g)) Z := by
      symm
      apply Finset.sum_subset hST
      intro g _ hg
      exact congruence_pullback_dir_zero N u.toFun g hZ
        (fun h => hg ((hS g).mpr (hu h))) w

theorem compact_poincare_gradient_square_bound_of_overlap (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (M : ℕ) (hM : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ M) :
    ∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K → ∀ z : ℍ,
      (upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re≤
        (M:ℝ)*∑' g : gamma N,(upperEnergy u.toFun u.toFun (g•z)).re := by
  classical
  have hbound := compact_poincare_derivative_sum_of_overlap N K hK M hM
  intro u hu z
  obtain ⟨S,hcard,hd,hout⟩ := hbound u hu (z.re,z.im) z.im_pos
  have hcart : cartesianLift (z.re,z.im)=z := by
    rw [cartesianLift_positive _ z.im_pos]
    rfl
  have heout (g : gamma N) (hg : g∉S) : upperEnergy u.toFun u.toFun (g•z)=0 := by
    by_contra hn
    rw [hcart] at hout
    exact hout g hg (hu (upperEnergy_support_right _ _ hn))
  rw [tsum_eq_sum (fun g hg => by rw [heout g hg]; rfl)]
  have hnorm (a : gamma N → ℂ) : ‖∑ g∈S,a g‖^2≤(M:ℝ)*∑ g∈S,‖a g‖^2 := by
    calc
      _ ≤ (∑ g∈S,‖a g‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (S.card:ℝ)*∑ g∈S,‖a g‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  let v := fun g : gamma N => u.toFun ∘ integralCuspChart (representative g)
  change (hyperbolicEnergy _ _ (z.re,z.im)).re≤_
  rw [hyperbolicEnergy_self_eq]
  change z.im^2*(‖dir e₁ (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖^2+
    ‖dir e₂ (congruencePoincareCartesian N u.toFun) (z.re,z.im)‖^2)≤_
  rw [hd e₁,hd e₂]
  calc
    _ ≤ z.im^2*((M:ℝ)*(∑ g∈S,‖dir e₁ (v g) (z.re,z.im)‖^2)+
        (M:ℝ)*(∑ g∈S,‖dir e₂ (v g) (z.re,z.im)‖^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hnorm _) (hnorm _)) (sq_nonneg z.im)
    _ = (M:ℝ)*∑ g∈S,(hyperbolicEnergy (v g) (v g) (z.re,z.im)).re := by
      simp only [hyperbolicEnergy_self_eq,X,Y,Finset.sum_add_distrib,←Finset.mul_sum]
      ring
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl (fun g _ => upperEnergy_congruence_pullback N u g z)

theorem compact_poincare_gradient_lintegral_bound_of_overlap (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (M : ℕ) (hM : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ M) :
    ∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K →
      (∫⁻ z,ENNReal.ofReal ((upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re) ∂quotientMeasure N)≤
        (M:ℝ≥0∞)*∫⁻ z : ℍ,ENNReal.ofReal ((upperEnergy u.toFun u.toFun z).re) := by
  classical
  have hbound := compact_poincare_gradient_square_bound_of_overlap N K hK M hM
  intro u hu
  have hpoint (z : ℍ) :
      ENNReal.ofReal ((upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re)≤
        (M:ℝ≥0∞)*∑' g : gamma N,ENNReal.ofReal ((upperEnergy u.toFun u.toFun (g•z)).re) := by
    have hs : Summable (fun g : gamma N => (upperEnergy u.toFun u.toFun (g•z)).re) := by
      apply summable_of_hasFiniteSupport
      apply (compact_orbit_point_finite (G := gamma N) K hK z).subset
      intro g hg
      apply hu
      apply upperEnergy_support_right u.toFun u.toFun
      intro hz
      exact hg (by change (upperEnergy u.toFun u.toFun (g•z)).re=0; rw [hz]; rfl)
    have hn (g : gamma N) : 0≤(upperEnergy u.toFun u.toFun (g•z)).re :=
      hyperbolicEnergy_self_nonneg _ _
    have hb := ENNReal.ofReal_le_ofReal (hbound u hu z)
    rwa [ENNReal.ofReal_mul (Nat.cast_nonneg M),ENNReal.ofReal_natCast,
      ENNReal.ofReal_tsum_of_nonneg hn hs] at hb
  calc
    _ ≤ ∫⁻ z, (M:ℝ≥0∞)*∑' g : gamma N,
        ENNReal.ofReal ((upperEnergy u.toFun u.toFun (g•z)).re) ∂quotientMeasure N :=
      lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp)]
      congr 1
      exact lintegral_poincare_unfold volume
        (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
        (density N) (density_measurable N) (density_orbit_sum N) _
        (Complex.continuous_re.comp (upperEnergy_continuous u.smooth u.smooth)).measurable.ennreal_ofReal

theorem compact_poincare_gradient_integral_bound_of_overlap (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (M : ℕ) (hM : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ M) :
    ∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K →
      (∫ z,(upperEnergy (congruencePoincareCartesian N u.toFun)
        (congruencePoincareCartesian N u.toFun) z).re ∂quotientMeasure N)≤
        (M:ℝ)*∫ z : ℍ,(upperEnergy u.toFun u.toFun z).re := by
  have hbound := compact_poincare_gradient_lintegral_bound_of_overlap N K hK M hM
  intro u hu
  have h1 : Integrable (fun z => (upperEnergy (congruencePoincareCartesian N u.toFun)
      (congruencePoincareCartesian N u.toFun) z).re) (quotientMeasure N) := by
    simpa only [RCLike.re_to_complex] using
      (poincare_green_energy N u.smooth u.smooth u.compact u.compact).1.re
  have h2 : Integrable (fun z : ℍ => (upperEnergy u.toFun u.toFun z).re) := by
    simpa only [RCLike.re_to_complex] using (upperEnergy_integrable u.smooth u.smooth u.compact).re
  have hn1 : ∀ᵐ z ∂quotientMeasure N,0≤(upperEnergy (congruencePoincareCartesian N u.toFun)
      (congruencePoincareCartesian N u.toFun) z).re :=
    Eventually.of_forall (fun _ => hyperbolicEnergy_self_nonneg _ _)
  have hn2 : ∀ᵐ z : ℍ,0≤(upperEnergy u.toFun u.toFun z).re :=
    Eventually.of_forall (fun _ => hyperbolicEnergy_self_nonneg _ _)
  have hb := hbound u hu
  rw [←ofReal_integral_eq_lintegral_ofReal h1 hn1,
    ←ofReal_integral_eq_lintegral_ofReal h2 hn2,←ENNReal.ofReal_natCast,
    ←ENNReal.ofReal_mul (Nat.cast_nonneg M)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg M)
    (integral_nonneg_of_ae hn2))).mp hb

#print axioms compact_poincare_derivative_sum_of_overlap
#print axioms compact_poincare_gradient_square_bound_of_overlap
#print axioms compact_poincare_gradient_lintegral_bound_of_overlap
#print axioms compact_poincare_gradient_integral_bound_of_overlap

end QuantitativeMaass
