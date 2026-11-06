module

public import AsymptoticRationalLocalIntegralV1
public import AsymptoticCongruenceLabelsV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticLocalCongruence

open Matrix AsymptoticIntegralSubgroup
open scoped MatrixGroups

/-- The determinant-one local congruence condition: integral entries
and lower-left entry divisible by the level in the local valuation ring. -/
def Condition (N q : ℕ) (A : SL(2,ℚ)) : Prop :=
  IntegralEntries q A.val ∧ padicNorm q (A.val 1 0/(N:ℚ))≤1

theorem condition_one (N q : ℕ) : Condition N q 1 := by
  refine ⟨integralEntries_one q,?_⟩
  change padicNorm q ((1 : Matrix (Fin 2) (Fin 2) ℚ) 1 0/(N:ℚ))≤1
  norm_num

theorem condition_mul (N q : ℕ) [Fact q.Prime] (A B : SL(2,ℚ))
    (hA : Condition N q A) (hB : Condition N q B) : Condition N q (A*B) := by
  refine ⟨integralEntries_mul q _ _ hA.1 hB.1,?_⟩
  have he : (A*B).val 1 0/(N:ℚ)=
      (A.val 1 0/(N:ℚ))*B.val 0 0+A.val 1 1*(B.val 1 0/(N:ℚ)) := by
    change (A.val*B.val) 1 0/(N:ℚ)=_
    rw [Matrix.mul_apply,Fin.sum_univ_two]
    ring
  rw [he]
  apply (padicNorm.nonarchimedean).trans
  apply max_le
  · rw [padicNorm.mul]
    exact (mul_le_mul_of_nonneg_right hA.2 (padicNorm.nonneg _)).trans
      (by simpa only [one_mul] using hB.1 0 0)
  · rw [padicNorm.mul]
    exact (mul_le_mul_of_nonneg_right (hA.1 1 1) (padicNorm.nonneg _)).trans
      (by simpa only [one_mul] using hB.2)

theorem condition_inv (N q : ℕ) (A : SL(2,ℚ)) (hA : Condition N q A) :
    Condition N q A⁻¹ := by
  constructor
  · intro i j
    rw [SpecialLinearGroup.SL2_inv_expl]
    fin_cases i <;> fin_cases j
    · exact hA.1 1 1
    · change padicNorm q (-A.val 0 1)≤1
      simpa only [padicNorm.neg] using hA.1 0 1
    · change padicNorm q (-A.val 1 0)≤1
      simpa only [padicNorm.neg] using hA.1 1 0
    · exact hA.1 0 0
  · change padicNorm q (A⁻¹.val 1 0/(N:ℚ))≤1
    rw [SpecialLinearGroup.SL2_inv_expl]
    simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,neg_div,padicNorm.neg] using hA.2

def localSL (N q : ℕ) [Fact q.Prime] : Subgroup SL(2,ℚ) where
  carrier := Condition N q
  one_mem' := condition_one N q
  mul_mem' := fun {A B} => condition_mul N q A B
  inv_mem' := fun {A} => condition_inv N q A

/-- Rational determinant-one matrices satisfying the level condition
at every prime outside a specified set. -/
noncomputable def outside (N : ℕ) (S : Set ℕ) : Subgroup SL(2,ℚ) :=
  ⨅ q : ℕ,⨅ hq : q.Prime,⨅ (_ : q∉S),
    letI : Fact q.Prime := ⟨hq⟩
    localSL N q

theorem mem_outside (N : ℕ) (S : Set ℕ) (A : SL(2,ℚ)) :
    A∈outside N S ↔ ∀ q : ℕ,q.Prime → q∉S → Condition N q A := by
  simp only [outside,Subgroup.mem_iInf]
  rfl

theorem outside_mono (N : ℕ) {S T : Set ℕ} (h : S⊆T) : outside N S ≤ outside N T := by
  intro A hA
  rw [mem_outside] at hA ⊢
  intro q hq hqT
  exact hA q hq (fun hqS => hqT (h hqS))

/-- Disjoint permitted prime sets have only globally integral
congruence matrices in their intersection. -/
theorem outside_inf (N : ℕ) (S T : Set ℕ) :
    outside N S⊓outside N T=outside N (S∩T) := by
  ext A
  simp only [Subgroup.mem_inf,mem_outside,Set.mem_inter_iff]
  constructor
  · rintro ⟨hS,hT⟩ q hq hqST
    by_cases hs : q∈S
    · exact hT q hq (fun ht => hqST ⟨hs,ht⟩)
    · exact hS q hq hs
  · intro h
    constructor
    · intro q hq hs
      exact h q hq (fun hh => hs hh.1)
    · intro q hq ht
      exact h q hq (fun hh => ht hh.2)

#print axioms condition_one
#print axioms condition_mul
#print axioms condition_inv
#print axioms mem_outside
#print axioms outside_mono
#print axioms outside_inf

end AsymptoticLocalCongruence
