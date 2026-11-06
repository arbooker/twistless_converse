module

public import AsymptoticClassicalLocalAtkinTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace AsymptoticClassicalCusp
open UpperHalfPlane
open scoped ModularForm

variable (M p : ℕ) [NeZero M] [Fact p.Prime] (hM : 0 < M) (hpM : ¬ p ∣ M)
variable (A B : ℤ) (hAB : (p : ℤ) * A + (M : ℤ) * B = 1)

include hM hpM in
/-- On the second old-trace kernel the bad-prime operator is minus local Atkin. -/
theorem upperTrace_simple_eq_neg_local (k : ℤ) (f : CuspForm (level (p * M)) k)
    (hf : let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p (Fact.out : p.Prime).pos) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p (Fact.out : p.Prime).pos k f =
      -localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k f := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
  dsimp only
  let hp := (Fact.out : p.Prime).pos
  have hc : (p : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.ne')
  have ht := localAtkin_trace_zero M p hp A B hAB k f hf
  have hh := upperTrace_localAtkin M p hp A B hAB hM hpM k
    (localAtkinOperator M p hp A B hAB k f)
  dsimp only at ht hh
  rw [localAtkinOperator_square, map_smul, ht] at hh
  ext z
  apply mul_left_cancel₀ hc
  have hz := congrFun hh z
  simpa only [FunLike.coe_smul, FunLike.coe_zero, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Pi.zero_apply, zero_sub, Pi.neg_apply, neg_apply] using hz

include hM hpM hAB in
/-- Both old traces give the exact bad-prime quadratic relation. -/
theorem upperTrace_simple_square_of_traces (k : ℤ) (f : CuspForm (level (p * M)) k)
    (hfirst : let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (level M) k f = 0)
    (hsecond : let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
      arithmeticTrace (level (p * M)) (dilationLevel M p (Fact.out : p.Prime).pos) k f = 0) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p (Fact.out : p.Prime).pos k
      (upperTrace (p * M) p (Fact.out : p.Prime).pos k f) = (p : ℂ) ^ (k - 2) • f := by
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
  dsimp only
  rw [upperTrace_simple_eq_neg_local M p hM hpM A B hAB k f hsecond, map_neg]
  have hh := upperTrace_localAtkin M p (Fact.out : p.Prime).pos A B hAB hM hpM k f
  dsimp only at hh
  rw [hfirst] at hh
  ext z
  have hz := congrFun hh z
  simp only [FunLike.coe_zero, Pi.smul_apply, smul_eq_mul, zero_sub, Pi.neg_apply] at hz
  change -(upperTrace (p * M) p (Fact.out : p.Prime).pos k
    (localAtkinOperator M p (Fact.out : p.Prime).pos A B hAB k f) z) =
      (p : ℂ) ^ (k - 2) * f z
  rw [hz]
  ring

/-- The two defining newspace trace equations at a displayed prime factor. -/
theorem new_factor_traces (k : ℤ) (f : CuspForm (level (p * M)) k)
    (hf : f ∈ newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
    arithmeticTrace (level (p * M)) (level M) k f = 0 ∧
      arithmeticTrace (level (p * M)) (dilationLevel M p (Fact.out : p.Prime).pos) k f = 0 := by
  let hp := (Fact.out : p.Prime).pos
  let : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne' (NeZero.ne M)⟩
  dsimp only
  let hN := Nat.mul_pos hp hM
  let q : {q : ℕ // q.Prime ∧ q ∣ p * M} := ⟨p, Fact.out, Nat.dvd_mul_right p M⟩
  have hdiv : (p * M) / p = M := Nat.mul_div_cancel_left M hp
  let : NeZero ((p * M) / p) := ⟨by rw [hdiv]; exact NeZero.ne M⟩
  have ht := prime_trace_eq_zero (p * M) hN k q f hf
  let : (level (p * M)).IsFiniteRelIndex (level ((p * M) / p)) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level ((p * M) / p))).symm).1
  let : (level (p * M)).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (level (p * M)).IsFiniteRelIndex (frickeOldLevel (p * M) ((p * M) / p) hN) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable
        (𝒢 := frickeOldLevel (p * M) ((p * M) / p) hN)).symm).1
  let : (level (p * M)).IsFiniteRelIndex (dilationLevel M p hp) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := dilationLevel M p hp)).symm).1
  constructor
  · apply DFunLike.coe_injective
    change (CuspForm.trace (level M) f : ℍ → ℂ) = 0
    rw [← trace_target_congr k (congrArg level hdiv) f]
    exact congrArg (fun h : CuspForm (level ((p * M) / p)) k => (h : ℍ → ℂ)) ht.1
  · have hg : frickeOldLevel (p * M) ((p * M) / p) hN = dilationLevel M p hp := by
      rw [hdiv]
      exact frickeOldLevel_eq_dilationLevel M p hM hp
    apply DFunLike.coe_injective
    change (CuspForm.trace (dilationLevel M p hp) f : ℍ → ℂ) = 0
    rw [← trace_target_congr k hg f]
    exact congrArg (fun h : CuspForm (frickeOldLevel (p * M) ((p * M) / p) hN) k => (h : ℍ → ℂ)) ht.2

include hpM hAB in
/-- The simple bad-prime square relation on genuine new cusp forms. -/
theorem upperTrace_simple_new_square (k : ℤ) (f : CuspForm (level (p * M)) k)
    (hf : f ∈ newSpace (p * M) (Nat.mul_pos (Fact.out : p.Prime).pos hM) k) :
    let : NeZero (p * M) := ⟨Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne M)⟩
    upperTrace (p * M) p (Fact.out : p.Prime).pos k
      (upperTrace (p * M) p (Fact.out : p.Prime).pos k f) = (p : ℂ) ^ (k - 2) • f := by
  have ht := new_factor_traces M p hM k f hf
  exact upperTrace_simple_square_of_traces M p hM hpM A B hAB k f ht.1 ht.2

#print axioms upperTrace_simple_eq_neg_local
#print axioms upperTrace_simple_square_of_traces
#print axioms new_factor_traces
#print axioms upperTrace_simple_new_square
end AsymptoticClassicalCusp
