module

public import QuantitativeMaassCountingOldPairV1
public import QuantitativeMaassCountingLocalPowerGapV1
public import QuantitativeMaassCountingLocalOperatorGapV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticQuotientOperators
open QuantitativeNewGap ContinuousLinearMap
open scoped lp
namespace QuantitativeMaass.Counting

/-- Exact simple-prime index normalization of the counting old pair. -/
theorem simple_oldPair_normalized (M p : ℕ) [NeZero M] [Fact p.Prime]
    [NeZero (p*M)] (hM : 0<M) (hpM : ¬p∣M) :
    let hN := Nat.mul_pos (Fact.out : p.Prime).pos hM
    (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • oldPair hN (Nat.dvd_mul_left M p))=
      (space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection+
      (space (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p))).starProjection := by
  intro hN
  have hcop := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have huv : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    rw [←Nat.gcd_eq_gcd_ab,hcop.gcd_eq_one,Int.natCast_one]
  have hi := HeckeL2.cover_index M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) huv
  change ((gamma (p*M)).subgroupOf (gamma M)).index=p+1 at hi
  rw [oldPair_projection_formula,smul_smul,hi]
  have hc : (((((p:ℝ)+1)⁻¹:ℝ):ℂ))*((p+1:ℕ):ℂ)=1 := by
    rw [Nat.cast_add,Nat.cast_one,Complex.ofReal_inv,Complex.ofReal_add,
      Complex.ofReal_natCast,Complex.ofReal_one]
    exact inv_mul_cancel₀ (by exact_mod_cast (show (p:ℝ)+1≠0 by positivity))
  rw [hc,one_smul]

/-- The actual finite branch filter at a simple prime converges to the
actual counting new projection, with an explicit geometric error shape. -/
theorem simpleNewFilter_approximation (M p : ℕ) [NeZero M] [Fact p.Prime]
    [NeZero (p*M)] (hM : 0<M) (hpM : ¬p∣M) :
    let hN := Nat.mul_pos (Fact.out : p.Prime).pos hM
    let U := newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
      (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p))
    ∃ ρ : ℝ,0≤ρ ∧ ρ<1 ∧ ∀ (m : ℕ) (v : Space (p*M)),
      ‖simpleNewFilter hN (Nat.dvd_mul_left M p) p m v-U.starProjection v‖^2 ≤
        ρ^m*‖v-U.starProjection v‖^2 := by
  intro hN U
  obtain ⟨ρ,hρ,hρ1,hbound⟩ := prime_old_power_approximation M p hM (Fact.out : p.Prime)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro m v
  let P := (space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection
  let Q := (space (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p))).starProjection
  have hh := hbound m v
  change ‖((1-(1/2:ℂ) • (P.toLinearMap+Q.toLinearMap))^m) v-U.starProjection v‖^2 ≤
    ρ^m*‖v-U.starProjection v‖^2 at hh
  have hT : 1-(1/2:ℂ) • (P.toLinearMap+Q.toLinearMap)=
      (1-(1/2:ℂ) • (P+Q)).toLinearMap := rfl
  rw [hT,←toLinearMap_pow] at hh
  rw [simpleNewFilter,simple_oldPair_normalized M p hM hpM]
  exact hh


theorem simpleNewFilter_operator_approximation (M p : ℕ) [NeZero M] [Fact p.Prime]
    [NeZero (p*M)] (hM : 0<M) (hpM : ¬p∣M) :
    let hN := Nat.mul_pos (Fact.out : p.Prime).pos hM
    let U := newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
      (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p))
    ∃ ρ : ℝ,0≤ρ ∧ ρ<1 ∧ ∀ m : ℕ,
      ‖simpleNewFilter hN (Nat.dvd_mul_left M p) p m-U.starProjection‖ ≤ ρ^m := by
  intro hN U
  obtain ⟨ρ,hρ,hρ1,hbound⟩ := prime_old_operator_approximation M p hM (Fact.out : p.Prime)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro m
  rw [simpleNewFilter,simple_oldPair_normalized M p hM hpM]
  exact hbound m

#print axioms simpleNewFilter_operator_approximation


theorem simpleNewFilter_norm (M p : ℕ) [NeZero M] [Fact p.Prime]
    [NeZero (p*M)] (hM : 0<M) (hpM : ¬p∣M) (m : ℕ) :
    ‖simpleNewFilter (Nat.mul_pos (Fact.out : p.Prime).pos hM)
      (Nat.dvd_mul_left M p) p m‖≤1 := by
  let hN := Nat.mul_pos (Fact.out : p.Prime).pos hM
  let P := (space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection
  let Q := (space (gamma_le_frickeOldGroup hN (Nat.dvd_mul_left M p))).starProjection
  rw [simpleNewFilter,simple_oldPair_normalized M p hM hpM]
  apply opNorm_le_bound _ zero_le_one
  intro x
  have hpp : IsIdempotentElem P.toLinearMap := by
    apply LinearMap.ext; intro y; exact DFunLike.congr_fun (Submodule.isIdempotentElem_starProjection _) y
  have hqq : IsIdempotentElem Q.toLinearMap := by
    apply LinearMap.ext; intro y; exact DFunLike.congr_fun (Submodule.isIdempotentElem_starProjection _) y
  have hh := two_projection_filter_pointwise P.toLinearMap Q.toLinearMap
    (Submodule.starProjection_isSymmetric _) (Submodule.starProjection_isSymmetric _) hpp hqq m x
  have hT : 1-(1/2:ℂ) • (P.toLinearMap+Q.toLinearMap)=
      (1-(1/2:ℂ) • (P+Q)).toLinearMap := rfl
  rw [hT,←toLinearMap_pow] at hh
  rw [one_mul]
  change ‖((1-(1/2:ℂ) • (P+Q))^m) x‖≤‖x‖
  exact hh

#print axioms simpleNewFilter_norm

#print axioms simple_oldPair_normalized
#print axioms simpleNewFilter_approximation
end QuantitativeMaass.Counting
