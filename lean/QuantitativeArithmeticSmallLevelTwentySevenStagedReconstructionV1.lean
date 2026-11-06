module
public import QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStagesClosureV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticTriangularMeromorphicReconstructionTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticRationalRows (extend)
open QuantitativeArithmeticTriangularMeromorphicReconstruction Matrix

section Parameters
variable (x y z w a b c : ℂ)
local notation "C" => coefficient x y z w a b c
local notation "E" => eval x y z w a b c

def stageLead (n : ℕ) : ℂ := C (certificate n) (550+n)
def stageLower (n j : ℕ) : ℂ := C (certificate n) (550+j)
def stageSource (n : ℕ) : ℂ := -C (certificate n) n

def stageRhsMatrix (n : ℕ) (j : Fin 550) : ℂ :=
  if n=j.val then stageSource x y z w a b c n else 0

def sourceMatrix : Matrix (Fin 550) (Fin 607) ℂ := fun i j => C (inputs i.val) j.val
def outputMatrix : Matrix (Fin 321) (Fin 607) ℂ := fun i j => C (inputs (1100+i.val)) j.val

def outputFactor : Matrix (Fin 321) (Fin 550) ℂ :=
  fun i j => -C (certificate (550+i.val)) (550+j.val)/stageLead x y z w a b c (550+i.val)

def stagedLeftMatrix : Matrix (Fin 321) (Fin 550) ℂ :=
  outputFactor x y z w a b c *
    reconstructionMatrix (stageRhsMatrix x y z w a b c)
      (stageLead x y z w a b c) (stageLower x y z w a b c)

theorem stage_relation (v : ℕ → ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (n : ℕ) (hn : n<550) :
    stageLead x y z w a b c n*E v (inputs (550+n))=
      stageSource x y z w a b c n*E v (inputs n)-
        ∑ j : Fin n, stageLower x y z w a b c n j.val*E v (inputs (550+j.val)) := by
  have hs : ∀ t∈certificate n, t.2.1=n ∨ (550≤t.2.1 ∧ t.2.1<550+(n+1)) := by
    intro t ht
    have hh := of_decide_eq_true ((List.all_eq_true.mp (all_support n (by omega))) t ht)
    simp only [ite_eq_left hn] at hh
    omega
  have he := substitution_zero x y z w a b c v hx hy hz hw inputs (certificate n) (all_replays n (by omega))
  rw [eval_spike_block x y z w a b c _ _ n 550 (n+1) (Or.inl hn) hs,
    Fin.sum_univ_castSucc] at he
  simp only [Fin.val_castSucc,Fin.val_last] at he
  dsimp only [stageLead,stageSource,stageLower]
  linear_combination he

theorem output_relation (v : ℕ → ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (i : Fin 321) :
    stageLead x y z w a b c (550+i.val)*E v (inputs (1100+i.val))=
      -∑ j : Fin 550, C (certificate (550+i.val)) (550+j.val)*E v (inputs (550+j.val)) := by
  have hs : ∀ t∈certificate (550+i.val),
      t.2.1=1100+i.val ∨ (550≤t.2.1 ∧ t.2.1<550+550) := by
    intro t ht
    have hh := of_decide_eq_true ((List.all_eq_true.mp (all_support (550+i.val) (by omega))) t ht)
    simp only [show ¬550+i.val<550 by omega,ite_false] at hh
    omega
  have he := substitution_zero x y z w a b c v hx hy hz hw inputs (certificate (550+i.val))
    (all_replays (550+i.val) (by omega))
  rw [eval_spike_block x y z w a b c _ _ (1100+i.val) 550 550 (Or.inr (by omega)) hs] at he
  dsimp only [stageLead]
  have heq : 550+(550+i.val)=1100+i.val := by omega
  rw [heq]
  linear_combination he

theorem stages_recover (v : ℕ → ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hp : ∀ n, n<550 → stageLead x y z w a b c n≠0) (i : Fin 550) :
    (reconstructionMatrix (stageRhsMatrix x y z w a b c)
      (stageLead x y z w a b c) (stageLower x y z w a b c) *ᵥ
        (fun j : Fin 550 => E v (inputs j.val))) i=E v (inputs (550+i.val)) := by
  rw [reconstruction_action]
  apply solve_correct _ _ (fun n => E v (inputs (550+n))) _ 550 hp _ i.val i.isLt
  intro n hn
  have he := stage_relation x y z w a b c v hx hy hz hw n hn
  have hr : (∑ j : Fin 550, stageRhsMatrix x y z w a b c n j*E v (inputs j.val))=
      stageSource x y z w a b c n*E v (inputs n) := by
    rw [show (fun j : Fin 550 => stageRhsMatrix x y z w a b c n j*E v (inputs j.val))=
      (fun j : Fin 550 => (if n=j.val then stageSource x y z w a b c n else 0)*E v (inputs j.val)) from rfl]
    rw [single_sum]
    simp [extend,hn]
  rw [hr]
  exact he

theorem outputs_recover (v : ℕ → ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hp : ∀ n, n<871 → stageLead x y z w a b c n≠0) (i : Fin 321) :
    (stagedLeftMatrix x y z w a b c *ᵥ (fun j : Fin 550 => E v (inputs j.val))) i=
      E v (inputs (1100+i.val)) := by
  rw [stagedLeftMatrix,← Matrix.mulVec_mulVec]
  have hs : reconstructionMatrix (stageRhsMatrix x y z w a b c)
      (stageLead x y z w a b c) (stageLower x y z w a b c) *ᵥ
        (fun j : Fin 550 => E v (inputs j.val)) =
          (fun j : Fin 550 => E v (inputs (550+j.val))) := by
    funext j
    exact stages_recover x y z w a b c v hx hy hz hw (fun n hn => hp n (by omega)) j
  rw [hs]
  change (∑ j : Fin 550, outputFactor x y z w a b c i j*E v (inputs (550+j.val))) = _
  have he := output_relation x y z w a b c v hx hy hz hw i
  have hp' := hp (550+i.val) (by omega)
  dsimp only [outputFactor]
  simp_rw [div_mul_eq_mul_div,neg_mul]
  rw [← Finset.sum_div,Finset.sum_neg_distrib]
  have hneg : -(∑ j : Fin 550, C (certificate (550+i.val)) (550+j.val)*E v (inputs (550+j.val)))=
      stageLead x y z w a b c (550+i.val)*E v (inputs (1100+i.val)) := he.symm
  rw [hneg,mul_div_cancel_left₀ _ hp']

/-- The explicit 321 by 550 left reconstruction matrix recovers all
constant observation rows from the selected source rows. -/
theorem staged_matrix_identity (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (hp : ∀ n, n<871 → stageLead x y z w a b c n≠0) :
    stagedLeftMatrix x y z w a b c * sourceMatrix x y z w a b c=outputMatrix x y z w a b c := by
  have action (v : Fin 607 → ℂ) :
      stagedLeftMatrix x y z w a b c *ᵥ (sourceMatrix x y z w a b c *ᵥ v)=
        outputMatrix x y z w a b c *ᵥ v := by
    funext i
    have he := outputs_recover x y z w a b c (extend v) hx hy hz hw hp i
    simp_rw [eval_extend_eq_sum] at he
    exact he
  apply Matrix.ext
  intro i j
  have he := congrFun (action (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec] at he
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using he
end Parameters
#print axioms stage_relation
#print axioms stages_recover
#print axioms staged_matrix_identity
end QuantitativeArithmeticSmallLevelTwentySevenPlusGenericStages
