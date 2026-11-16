module

public import QuantitativeArithmeticMaassGradientCoreV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeArithmeticMaassGradient

open QuantitativeMaass MaassDifferential

theorem poincareCartesian_add (N : ℕ) (u v : SmoothUpperSeed) :
    congruencePoincareCartesian N (u.add v).toFun=
      fun Z => congruencePoincareCartesian N u.toFun Z+congruencePoincareCartesian N v.toFun Z := by
  funext Z
  have hsu : Summable (fun g : gamma N => upperFunction u.toFun (g•cartesianLift Z)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support (upperFunction u.toFun) u.compact _)
  have hsv : Summable (fun g : gamma N => upperFunction v.toFun (g•cartesianLift Z)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support (upperFunction v.toFun) v.compact _)
  exact hsu.tsum_add hsv

theorem poincareCartesian_smul (N : ℕ) (c : ℂ) (u : SmoothUpperSeed) :
    congruencePoincareCartesian N (u.smul c).toFun=
      fun Z => c*congruencePoincareCartesian N u.toFun Z := by
  funext Z
  exact tsum_mul_left

theorem seedGradient_add (N : ℕ) (i : Bool) (u v : SmoothUpperSeed) :
    seedGradient N i (u.add v)=seedGradient N i u+seedGradient N i v := by
  funext z
  unfold seedGradient
  rw [poincareCartesian_add]
  change (z.im : ℂ)*dir (axis i) _ (z.re,z.im)=_
  rw [dir_add_smooth (isOpen_lt continuous_const continuous_snd)
    (congruencePoincareCartesian_smooth N u.smooth u.compact)
    (congruencePoincareCartesian_smooth N v.smooth v.compact) z.im_pos]
  exact mul_add _ _ _

theorem seedGradient_smul (N : ℕ) (i : Bool) (c : ℂ) (u : SmoothUpperSeed) :
    seedGradient N i (u.smul c)=c•seedGradient N i u := by
  funext z
  unfold seedGradient
  rw [poincareCartesian_smul]
  change (z.im : ℂ)*dir (axis i) (fun Z => c*congruencePoincareCartesian N u.toFun Z) (z.re,z.im)=_
  rw [dir_mul_smooth (isOpen_lt continuous_const continuous_snd) contDiffOn_const
    (congruencePoincareCartesian_smooth N u.smooth u.compact) z.im_pos]
  simp only [dir,D,fderiv_fun_const,Pi.zero_apply,zero_apply,zero_mul,zero_add,
    Pi.smul_apply,smul_eq_mul,upperFunction]
  ring

theorem seedGradientLp_add (N : ℕ) (i : Bool) (u v : SmoothUpperSeed) :
    seedGradientLp N i (u.add v)=seedGradientLp N i u+seedGradientLp N i v := by
  unfold seedGradientLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun (seedGradient_add N i u v))

theorem seedGradientLp_smul (N : ℕ) (i : Bool) (c : ℂ) (u : SmoothUpperSeed) :
    seedGradientLp N i (u.smul c)=c•seedGradientLp N i u := by
  unfold seedGradientLp
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun (seedGradient_smul N i c u))

def smoothGradientMap (N : ℕ) (i : Bool) : smoothSeedModule →ₗ[ℂ] Lp ℂ 2 (quotientMeasure N) where
  toFun u := seedGradientLp N i (moduleSeed u)
  map_add' u v := seedGradientLp_add N i (moduleSeed u) (moduleSeed v)
  map_smul' c u := seedGradientLp_smul N i c (moduleSeed u)

theorem smoothGradientMap_bound (N : ℕ) (i : Bool) (u : smoothSeedModule) :
    ‖smoothGradientMap N i u‖≤1*‖smoothEnergyMap N u‖ := by
  change ‖seedGradientLp N i (moduleSeed u)‖≤1*‖(poincareEnergySeed N (moduleSeed u) : QuotientEnergySpace N)‖
  simpa only [one_mul,Completion.norm_coe] using seedGradientLp_norm_le N i (moduleSeed u)

/-- The literal hyperbolic coordinate derivative extends continuously from
compact Poincare seeds to the completed Dirichlet-form domain. -/
def quotientGradient (N : ℕ) (i : Bool) :
    QuotientEnergySpace N →L[ℂ] Lp ℂ 2 (quotientMeasure N) :=
  (smoothGradientMap N i).extendOfNorm (smoothEnergyMap N)

theorem quotientGradient_seed (N : ℕ) (i : Bool) (u : SmoothUpperSeed) :
    quotientGradient N i (poincareEnergySeed N u : QuotientEnergySpace N)=seedGradientLp N i u :=
  LinearMap.extendOfNorm_eq (f := smoothGradientMap N i) (e := smoothEnergyMap N)
    (smoothEnergyMap_dense N) ⟨1,smoothGradientMap_bound N i⟩ (seedModule u)

theorem quotientGradient_norm_le (N : ℕ) (i : Bool) : ‖quotientGradient N i‖≤1 :=
  LinearMap.opNorm_extendOfNorm_le (f := smoothGradientMap N i) (e := smoothEnergyMap N)
    (smoothEnergyMap_dense N) zero_le_one (smoothGradientMap_bound N i)

#print axioms quotientGradient_seed
#print axioms quotientGradient_norm_le

end QuantitativeArithmeticMaassGradient
