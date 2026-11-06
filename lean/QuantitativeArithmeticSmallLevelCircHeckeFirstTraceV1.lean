module

public import QuantitativeArithmeticSmallLevelCircModularHeckeTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelCirc
open UpperHalfPlane AsymptoticClassicalCusp

theorem primeTrace_factor_zero_iff (M q : ℕ) [NeZero M] (hq : q.Prime)
    (hN : 0<q*M) (k : ℤ) (F : ModularForm (level (q*M)) k) :
    primeTrace (q*M) hN k ⟨q,hq,Nat.dvd_mul_right q M⟩ F = 0 ↔
      (by
        let : NeZero (q*M) := ⟨hN.ne'⟩
        exact ModularHecke.arithmeticTrace (level (q*M)) (level M) k F :
          ModularForm (level M) k) = 0 := by
  let : NeZero (q*M) := ⟨hN.ne'⟩
  let : NeZero ((q*M)/q) := ⟨by rw [Nat.mul_div_cancel_left M hq.pos]; exact NeZero.ne M⟩
  let : (level (q*M)).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (q*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  let : (level (q*M)).IsFiniteRelIndex (level ((q*M)/q)) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level (q*M))).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level ((q*M)/q))).symm).1
  have he := modularTrace_target_congr F (congrArg level (Nat.mul_div_cancel_left M hq.pos))
  constructor <;> intro ht <;> apply DFunLike.coe_injective
  · change (ModularForm.trace (level M) F : ℍ → ℂ) = 0
    rw [← he]
    exact congrArg (fun f : ModularForm (level ((q*M)/q)) k => (f : ℍ → ℂ)) ht
  · change (ModularForm.trace (level ((q*M)/q)) F : ℍ → ℂ) = 0
    rw [he]
    exact congrArg (fun f : ModularForm (level M) k => (f : ℍ → ℂ)) ht

/-- Every ordinary trace kernel in the definition of Mcirc is preserved
by an actual good-prime Hecke operator. -/
theorem primeHecke_first_trace_zero (N p : ℕ) [NeZero N] (hN : 0<N)
    (hp : p.Prime) (hpN : ¬p∣N) (k : ℤ) (F : ModularForm (level N) k)
    (q : {q : ℕ // q.Prime ∧ q∣N})
    (hF : primeTrace N hN k q F = 0) :
    primeTrace N hN k q (ModularHecke.primeHecke N p hp k F) = 0 := by
  rcases q with ⟨q,hq,hqN⟩
  obtain ⟨M,rfl⟩ := hqN
  have hM : 0<M := Nat.pos_of_mul_pos_left hN
  let : NeZero M := ⟨hM.ne'⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpN (dvd_mul_of_dvd_left h M))
  rw [primeTrace_factor_zero_iff M q hq hN k] at hF ⊢
  simp only [ModularHecke.primeHecke, hpN, ite_false]
  rw [
    ModularHecke.dilationTrace_cross_trace M p q hM hp.pos hq hc k F,
    hF, map_zero]

#print axioms primeTrace_factor_zero_iff
#print axioms primeHecke_first_trace_zero
end QuantitativeArithmeticSmallLevelCirc
