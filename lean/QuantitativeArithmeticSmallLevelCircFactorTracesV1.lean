module

public import QuantitativeArithmeticSmallLevelCircModularHeckeTheoryV4
public import QuantitativeArithmeticSmallLevelCircHeckeFirstTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp

/-- The two defining Mcirc traces in the literal ordinary/conjugate
overgroup presentation, for an arbitrary displayed prime factor. -/
theorem factor_traces (M p k : ℕ) [NeZero M] (hp : p.Prime) (hM : 0 < M)
    (F : ModularForm (level (p * M)) (k : ℤ))
    (hF : F ∈ space (p * M) (Nat.mul_pos hp.pos hM) k) :
    let : NeZero (p * M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
    ModularHecke.arithmeticTrace (level (p * M)) (level M) (k : ℤ) F = 0 ∧
      ModularHecke.arithmeticTrace (level (p * M)) (dilationLevel M p hp.pos) (k : ℤ) F = 0 := by
  let : NeZero (p * M) := ⟨(Nat.mul_pos hp.pos hM).ne'⟩
  dsimp only
  obtain ⟨G, hG, _, _, ht⟩ := hF
  let q : {q : ℕ // q.Prime ∧ q ∣ p * M} := ⟨p, hp, Nat.dvd_mul_right p M⟩
  have hGF : G = ModularHecke.frickeOperator (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ) F :=
    DFunLike.coe_injective (hG.trans
      (ModularHecke.frickeOperator_coe (p * M) (Nat.mul_pos hp.pos hM) (k : ℤ) F).symm)
  have hfirst := (primeTrace_factor_zero_iff M p hp (Nat.mul_pos hp.pos hM) (k : ℤ) F).mp (ht q).1
  have hsecond := (primeTrace_factor_zero_iff M p hp (Nat.mul_pos hp.pos hM) (k : ℤ) G).mp (ht q).2
  rw [hGF] at hsecond
  have hconj := (ModularHecke.fricke_trace_swap_zero_iff (p * M) M
    (Nat.mul_pos hp.pos hM) (k : ℤ) F).mp hsecond
  refine ⟨hfirst, ?_⟩
  let : (level (p * M)).IsFiniteRelIndex (dilationLevel M p hp.pos) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := dilationLevel M p hp.pos)).symm).1
  let : (level (p * M)).IsFiniteRelIndex (frickeOldLevel (p * M) M (Nat.mul_pos hp.pos hM)) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (p * M))).trans
      (Subgroup.IsArithmetic.is_commensurable
        (𝒢 := frickeOldLevel (p * M) M (Nat.mul_pos hp.pos hM))).symm).1
  apply DFunLike.coe_injective
  change (ModularForm.trace (dilationLevel M p hp.pos) F : ℍ → ℂ) = 0
  rw [← modularTrace_target_congr F (frickeOldLevel_eq_dilationLevel M p hM hp.pos)]
  exact congrArg (fun h : ModularForm (frickeOldLevel (p * M) M (Nat.mul_pos hp.pos hM))
    (k : ℤ) => (h : ℍ → ℂ)) hconj

#print axioms factor_traces
end QuantitativeArithmeticSmallLevelCirc
