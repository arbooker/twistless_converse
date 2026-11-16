module

public import QuantitativeMaassLocalizedGraphResidualV1
public import QuantitativeMaassLocalResidualMassV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass
open MaassDifferential

theorem poincare_local_gradient_mass_le (N : ℕ) (v : SmoothUpperSeed)
    (K : Set ℍ) (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) :
    (∫ z in K, (upperEnergy (congruencePoincareCartesian N v.toFun)
      (congruencePoincareCartesian N v.toFun) z).re) ≤
      (m : ℝ)*‖poincareEnergySeed N v‖^2 := by
  apply le_trans _ (poincareEnergyDensity_local_integral_le N v K hK m hm)
  apply integral_mono
    ((Complex.continuous_re.comp (upperEnergy_continuous
      (congruencePoincareCartesian_smooth N v.smooth v.compact)
      (congruencePoincareCartesian_smooth N v.smooth v.compact))).continuousOn.integrableOn_compact hK)
    ((poincareEnergyDensity_continuous N v).continuousOn.integrableOn_compact hK)
  intro z
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Quantitative graph residual for an actual compact cross-quotient
transfer. Only the original L2 residual and first-order source energy
occur; both geometric multiplicities are retained. -/
theorem cross_seed_residual_norm_sq_le (N M : ℕ) (v b : SmoothUpperSeed)
    (hreal : ∀ W, star (b.toFun W)=b.toFun W)
    (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (μ : ℂ) (B H C : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hlap : ∀ z ∈ K, ‖upperLaplacian b.toFun z‖ ≤ H)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2) :
    let q := b.localized (congruencePoincareCartesian M v.toFun)
      (congruencePoincareCartesian_smooth M v.smooth v.compact)
    ‖poincareSeedVector N q.laplacian-μ • poincareSeedVector N q‖^2 ≤
      3*(mN : ℝ)*(mM : ℝ)*
        (B^2*‖poincareSeedVector M v.laplacian-μ • poincareSeedVector M v‖^2+
          H^2*‖poincareSeedVector M v‖^2+4*C^2*‖poincareEnergySeed M v‖^2) := by
  intro q
  have h := localized_poincare_residual_norm_sq N b
    (congruencePoincareCartesian M v.toFun)
    (congruencePoincareCartesian_smooth M v.smooth v.compact)
    hreal K hK hbK mN hmN μ B H C hB hH hbound hlap hgrad
  have hr := poincare_local_residual_mass_le M v K hK mM hmM μ
  have hv := representative_local_mass_le M K hK mM hmM
    ⟨_,poincareSeed_representative M v⟩
  have he := poincare_local_gradient_mass_le M v K hK mM hmM
  have hv' : (∫ z in K, ‖upperFunction (congruencePoincareCartesian M v.toFun) z‖^2) ≤
      (mM : ℝ)*‖poincareSeedVector M v‖^2 := by
    simp_rw [congruencePoincareCartesian_represents]
    exact hv
  apply (h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hr (sq_nonneg B))
      (mul_le_mul_of_nonneg_left hv' (sq_nonneg H)))
      (mul_le_mul_of_nonneg_left he (by positivity))) (by positivity))).trans_eq
  ring

/-- The source form norm costs only the spectral centre times the L2
mass, together with the actual L2 residual. -/
theorem poincare_energy_residual_bound (N : ℕ) (v : SmoothUpperSeed)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    ‖poincareEnergySeed N v‖^2 ≤ 2*(1+μ)*‖poincareSeedVector N v‖^2+
      ‖poincareSeedVector N v.laplacian-(μ : ℂ) • poincareSeedVector N v‖^2 := by
  rw [quotientEnergy_norm_sq,poincareEnergySeed_value,poincareEnergySeed_laplacian]
  let x := poincareSeedVector N v
  let d := poincareSeedVector N v.laplacian-(μ : ℂ) • x
  have he : poincareSeedVector N v.laplacian=(μ : ℂ) • x+d := by
    dsimp only [d]
    module
  have hs : (inner ℂ x x).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have hpair : (inner ℂ x (poincareSeedVector N v.laplacian)).re=
      μ*‖x‖^2+(inner ℂ x d).re := by
    rw [he,inner_add_right,_root_.inner_smul_right (𝕜 := ℂ) x x (μ : ℂ),
      Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hs]
  have hi : (inner ℂ x d).re ≤ ‖x‖*‖d‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm x d)
  change ‖x‖^2+(inner ℂ x (poincareSeedVector N v.laplacian)).re ≤
    2*(1+μ)*‖x‖^2+‖d‖^2
  rw [hpair]
  nlinarith [sq_nonneg (‖x‖-‖d‖),mul_nonneg hμ (sq_nonneg ‖x‖)]

#print axioms poincare_local_gradient_mass_le
#print axioms cross_seed_residual_norm_sq_le
#print axioms poincare_energy_residual_bound

end QuantitativeMaass
