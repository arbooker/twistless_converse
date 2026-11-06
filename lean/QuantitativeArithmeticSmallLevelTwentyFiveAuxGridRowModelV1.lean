module

public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridTaylorCertificateV1
public import QuantitativeArithmeticSmallLevelTwentyFiveFiniteGridTheoryV4
public import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Set Filter Matrix SmallLevelTaylor
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData
open QuantitativeArithmeticSmallLevelTwentyFiveKnownWords

inductive Row where
  | word (r : QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.WordCertificate 1050)
  | taylor (r : TaylorCertificate)
  | entire (q : ℕ) (positive : 0<q) (divides : q∣1050)
  | hecke (p : ℕ) (prime : p.Prime) (divides : p∣1050) (j : ℤ)
  | infinity (w : Word) (j : ℤ) (nonaffine : integerRaw w 1 0≠0)
      (denominator : QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.integerDen 1050 w j=0)

def leading (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 1050 → ℂ) : ℂ :=
  match r with
  | .word r => v (gridIndex 1050 (by decide) r.source)-
      coefficient r m (ε*I^(2*m)) 0 s*v (gridIndex 1050 (by decide) r.target)
  | .taylor r => sampleSum 1050 (by decide) r.q r.source v-
      taylorCoefficient 1050 (2*m) f ε r.q r.source 0 s*
        sampleSum 1050 (by decide) r.q r.target v
  | .entire q _ _ => sampleSum 1050 (by decide) q 0 v
  | .hecke p _ _ j => fullHeckeRow 1050 (by decide) m f p j s v
  | .infinity _ j _ _ => v (gridIndex 1050 (by decide) j)

def shifted (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v : Fin 1050 → ℂ) : ℂ :=
  match r with
  | .word r => coefficient r m (ε*I^(2*m)) (n+1) s*v (gridIndex 1050 (by decide) r.target)
  | .taylor r => taylorCoefficient 1050 (2*m) f ε r.q r.source (n+1) s*
      sampleSum 1050 (by decide) r.q r.target v
  | _ => 0

private theorem complete_add (p : ℕ) (j : ℤ) (v w : Fin 1050 → ℂ) :
    completeSum 1050 (by decide) p j (v+w)=completeSum 1050 (by decide) p j v+
      completeSum 1050 (by decide) p j w := by
  simp only [completeSum,Pi.add_apply,Finset.sum_add_distrib]

private theorem complete_smul (p : ℕ) (j : ℤ) (c : ℂ) (v : Fin 1050 → ℂ) :
    completeSum 1050 (by decide) p j (c • v)=c*completeSum 1050 (by decide) p j v := by
  simp only [completeSum,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]

theorem leading_add (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v w : Fin 1050 → ℂ) :
    leading r m f ε s (v+w)=leading r m f ε s v+leading r m f ε s w := by
  cases r <;> simp only [leading,fullHeckeRow,sampleSum_add,complete_add,Pi.add_apply]
  all_goals try split_ifs
  all_goals ring

theorem leading_smul (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε s c : ℂ) (v : Fin 1050 → ℂ) :
    leading r m f ε s (c • v)=c*leading r m f ε s v := by
  cases r <;> simp only [leading,fullHeckeRow,sampleSum_smul,complete_smul,Pi.smul_apply,smul_eq_mul]
  all_goals try split_ifs
  all_goals ring

theorem shifted_add (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (v w : Fin 1050 → ℂ) :
    shifted r m f ε n s (v+w)=shifted r m f ε n s v+shifted r m f ε n s w := by
  cases r <;> simp only [shifted,sampleSum_add,Pi.add_apply,mul_add,add_zero]

theorem shifted_smul (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s c : ℂ)
    (v : Fin 1050 → ℂ) : shifted r m f ε n s (c • v)=c*shifted r m f ε n s v := by
  cases r <;> simp only [shifted,sampleSum_smul,Pi.smul_apply,smul_eq_mul] <;> ring

theorem leading_analytic (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (v : Fin 1050 → ℂ) (s : ℂ) : AnalyticAt ℂ (fun z => leading r m f ε z v) s := by
  cases r with
  | word r =>
      exact analyticAt_const.sub ((coefficient_analytic (by decide) r m _ 0 s).mul analyticAt_const)
  | taylor r =>
      exact analyticAt_const.sub ((taylor_coefficient_analytic r (2*m) f ε 0 s).mul analyticAt_const)
  | hecke p hp _ j =>
      have h := hecke_parameter_analytic hp.pos m s
      dsimp [leading,fullHeckeRow]
      split_ifs <;> fun_prop
  | _ => exact analyticAt_const

theorem shifted_analytic (r : Row) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (n : ℕ) (v : Fin 1050 → ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun z => shifted r m f ε n z v) s := by
  cases r with
  | word r => exact (coefficient_analytic (by decide) r m _ (n+1) s).mul analyticAt_const
  | taylor r => exact (taylor_coefficient_analytic r (2*m) f ε (n+1) s).mul analyticAt_const
  | _ => exact analyticAt_const

#print axioms leading_add
#print axioms leading_analytic
#print axioms shifted_analytic
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
