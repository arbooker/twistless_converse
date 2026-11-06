module

public import QuantitativeArithmeticSmallLevelCircBadEulerV1
public import QuantitativeArithmeticSmallLevelCircHeckeInvariantV1
public import AsymptoticClassicalLocalFrickeMatrixV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc.ModularHecke
open UpperHalfPlane AsymptoticClassicalCusp
open scoped ModularForm

theorem frickeOperator_raw_coe (N : ℕ) (hN : 0 < N) (k : ℤ)
    (f : ModularForm (level N) k) :
    (frickeOperator N hN k f : ℍ → ℂ) =
      (N : ℂ)^(1-(k : ℂ)/2) • ((f : ℍ → ℂ) ∣[k] frickeReal N hN) := rfl

theorem localAtkin_fricke_commute (M p : ℕ) (hM : 0 < M) (hp : 0 < p)
    (A B : ℤ) (hAB : (p : ℤ)*A+(M : ℤ)*B=1) (k : ℤ) :
    Function.Commute (localAtkinOperator M p hp A B hAB k)
      (frickeOperator (p*M) (Nat.mul_pos hp hM) k) := by
  intro f
  apply DFunLike.coe_injective
  rw [localAtkinOperator_coe, frickeOperator_raw_coe,
    ModularForm.smul_slash, ← SlashAction.slash_mul,
    localAtkin_fricke_intertwine M p hp A B hAB hM,
    SlashAction.slash_mul, SlashAction.slash_mul]
  have hi : (f : ℍ → ℂ) ∣[k]
      Matrix.SpecialLinearGroup.mapGL ℝ (localFrickeCommutator M p A B hAB) = f :=
    f.slash_action_eq' _ ⟨_, localFrickeCommutator_mem M p A B hAB, rfl⟩
  rw [hi, frickeOperator_raw_coe, localAtkinOperator_coe]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [σ, localAtkinReal_det, hpR, ite_true, ContinuousAlgEquiv.refl_apply]

end QuantitativeArithmeticSmallLevelCirc.ModularHecke

namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp

/-- All prime Hecke operators, including ramified ones, commute with
global Fricke on the full space Mcirc. -/
theorem primeHecke_fricke_circ (N k : ℕ) [NeZero N] (hN : 0 < N) (hk : Even k)
    (F : ModularForm (level N) (k : ℤ)) (hF : F ∈ space N hN k)
    (p : ℕ) (hp : p.Prime) :
    ModularHecke.primeHecke N p hp (k : ℤ) (ModularHecke.frickeOperator N hN (k : ℤ) F) =
      ModularHecke.frickeOperator N hN (k : ℤ) (ModularHecke.primeHecke N p hp (k : ℤ) F) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hpN : p ∣ N
  · obtain ⟨M, rfl⟩ := hpN
    have hM : 0 < M := Nat.pos_of_mul_pos_left hN
    let : NeZero M := ⟨hM.ne'⟩
    have hj := fricke_mem_space hk F (ModularHecke.frickeOperator (p*M) hN (k : ℤ) F)
      hF (ModularHecke.frickeOperator_coe (p*M) hN (k : ℤ) F)
    have ht := factor_traces M p k hp hM F hF
    have hjt := factor_traces M p k hp hM _ hj
    dsimp only at ht hjt
    simp only [ModularHecke.primeHecke, Nat.dvd_mul_right p M, ite_true]
    by_cases hpM : p ∣ M
    · rw [ModularHecke.upperTrace_repeated_zero_of_trace M p hp hpM (k : ℤ) _ hjt.2,
        ModularHecke.upperTrace_repeated_zero_of_trace M p hp hpM (k : ℤ) F ht.2, map_zero]
    · have hc : p.Coprime M := hp.coprime_iff_not_dvd.mpr hpM
      have hAB : (p : ℤ)*Nat.gcdA p M+(M : ℤ)*Nat.gcdB p M=1 := by
        have hh := Nat.gcd_eq_gcd_ab p M
        rw [hc.gcd_eq_one, Nat.cast_one] at hh
        exact hh.symm
      rw [ModularHecke.upperTrace_simple_eq_neg_local M p hM hpM
          (Nat.gcdA p M) (Nat.gcdB p M) hAB (k : ℤ) _ hjt.2,
        ModularHecke.upperTrace_simple_eq_neg_local M p hM hpM
          (Nat.gcdA p M) (Nat.gcdB p M) hAB (k : ℤ) F ht.2, map_neg]
      exact congrArg Neg.neg (ModularHecke.localAtkin_fricke_commute M p hM hp.pos
        (Nat.gcdA p M) (Nat.gcdB p M) hAB (k : ℤ) F)
  · exact primeHecke_fricke_commute N p hN hp hpN (k : ℤ) F

theorem frickeLinear_val {N k : ℕ} {hN : 0 < N} (hk : Even k) (F : space N hN k) :
    (frickeLinear hk F).val = ModularHecke.frickeOperator N hN (k : ℤ) F.val := by
  apply DFunLike.coe_injective
  exact (frickeValue_coe hk F).trans (ModularHecke.frickeOperator_coe N hN (k : ℤ) F.val).symm

#print axioms ModularHecke.localAtkin_fricke_commute
#print axioms primeHecke_fricke_circ
#print axioms frickeLinear_val
end QuantitativeArithmeticSmallLevelCirc
