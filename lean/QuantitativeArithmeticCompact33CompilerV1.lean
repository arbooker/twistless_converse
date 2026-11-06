module

public import QuantitativeArithmeticSmallLevelThirtyThreeLaurentRowsV1
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticCompact33

open QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeKnownWords

abbrev zeroExponent : Exponent := (0,0,0,0,0,0,0)

def point (r : ℚ) (e : Exponent) (j : Fin 66) : Poly := [(r,j.val,e)]

/-- A short computable sum. No Finset.toList choice and no expansion of a
particular row is used by its correctness proof. -/
def rangeTerms (r : ℚ) (e : Exponent) (index : ℕ → Fin 66)
    (keep : ℕ → Bool) : ℕ → Poly
  | 0 => []
  | n+1 => rangeTerms r e index keep n ++
      if keep n then point r e (index n) else []

def sample (q : ℕ) (t : ℤ) (r : ℚ) (e : Exponent) : Poly :=
  rangeTerms r e (fun j => gridIndex (t+(j:ℤ)*(66/q:ℕ)))
    (fun j => decide (Nat.Coprime j q)) q

def wordRow (i : Fin 588) : Poly :=
  point 1 zeroExponent (groupIndex i) ++
    point (-((-1:ℚ)^(threeCount (sourceWord (groupSource i))%2)))
      ((groupPowers i).1,(groupPowers i).2.1,(groupPowers i).2.2,
       (frickeCount (sourceWord (groupSource i))%2:ℕ),0,
       threeCount (sourceWord (groupSource i))%2,0)
      (gridIndex (groupTarget i))

def taylorRow (i : Fin 72) : Poly :=
  sample (gridTaylorQ i) (gridTaylorT i) 1 zeroExponent ++
    sample (gridTaylorQ i) (gridTaylorPartner i)
      (-(if 3∣gridTaylorQ i then -1 else 1)*(if 11∣gridTaylorQ i then -1 else 1))
      ((taylorPowers i).1,(taylorPowers i).2.1,(taylorPowers i).2.2,1,0,
       (if 3∣gridTaylorQ i then 1 else 0),(if 11∣gridTaylorQ i then 1 else 0))

def inverseExponent (p : ℕ) (n : ℕ) : Exponent :=
  (if p=2 then -(n:ℤ) else 0,
   if p=3 then -(n:ℤ) else 0,
   if p=2 ∨ p=3 then 0 else -(n:ℤ),0,0,0,0)

def eigenInverseExponent (p : ℕ) : Exponent :=
  (if p=2 then -1 else 0,
   if p=3 then -1 else 0,
   if p=2 ∨ p=3 then 0 else -1,0,
   if p=2 then 1 else 0,
   if p=3 then 1 else 0,
   if p=2 ∨ p=3 then 0 else 1)

def heckeRow (i : Fin 61) : Poly :=
  rangeTerms 1 zeroExponent
    (fun j => gridIndex (gridHeckeT i+(j:ℤ)*(66/gridHeckeP i:ℕ)))
    (fun _ => true) (gridHeckeP i) ++
  point (-1) (eigenInverseExponent (gridHeckeP i))
    (gridIndex ((gridHeckeP i:ℤ)*gridHeckeT i)) ++
  if gridHeckeP i∣33 then [] else
    point 1 (inverseExponent (gridHeckeP i) 2)
      (gridIndex ((gridHeckeP i:ℤ)^2*gridHeckeT i))

/-- Symbolic row compiler; its only branches are the five original source
constructors. It deliberately does not use Laurent exponent addition,
whose evaluation law would require additional nonzero hypotheses. -/
def compile : GridSource → Poly
  | .word i => wordRow i
  | .taylor i => taylorRow i
  | .entire i => sample (gridEntireQ i) 0 1 zeroExponent
  | .hecke i => heckeRow i
  | .infinity i => point 1 zeroExponent (gridInfinityIndex i)

theorem gridIndex_val (j : Fin 66) : gridIndex (j.val:ℤ)=j := by
  apply Fin.ext
  change ((j.val:ℤ)%66).toNat=j.val
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast j.isLt),
    Int.toNat_natCast]

theorem eval_point (x y z η a u v : ℂ) (w : Fin 66 → ℂ)
    (r : ℚ) (e : Exponent) (j : Fin 66) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ))) (point r e j)=
      (r:ℂ)*monomial x y z η a u v e*w j := by
  simp only [point,eval_cons,eval_nil,add_zero,gridIndex_val]

theorem eval_rangeTerms (x y z η a u v : ℂ) (w : Fin 66 → ℂ)
    (r : ℚ) (e : Exponent) (index : ℕ → Fin 66) (keep : ℕ → Bool) (n : ℕ) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ)))
        (rangeTerms r e index keep n)=
      (r:ℂ)*monomial x y z η a u v e*
        ∑ j ∈ Finset.range n, if keep j then w (index j) else 0 := by
  induction n with
  | zero => simp [rangeTerms]
  | succ n ih =>
    cases hk : keep n <;>
      simp [rangeTerms,hk,eval_append,eval_point,ih,Finset.sum_range_succ,mul_add]

theorem eval_sample (x y z η a u v : ℂ) (w : Fin 66 → ℂ)
    (q : ℕ) (t : ℤ) (r : ℚ) (e : Exponent) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ))) (sample q t r e)=
      (r:ℂ)*monomial x y z η a u v e*gridSample q t w := by
  simp only [sample,eval_rangeTerms,gridSample,FinitenessRamanujanSum.residues,
    Finset.sum_filter,decide_eq_true_eq]

theorem monomial_zero (x y z η a u v : ℂ) :
    monomial x y z η a u v zeroExponent=1 := by
  simp [monomial]

theorem word_coefficient (x y z η a u v : ℂ) (e : ℤ×ℤ×ℤ) (f b : ℕ) :
    ((-((-1:ℚ)^b):ℚ):ℂ)*monomial x y z η a u v
      (e.1,e.2.1,e.2.2,(f:ℤ),0,b,0)=
    -(η^f*(-u)^b)*SmallLevelPrimeRates.monomial e x y z := by
  have hn : (-u)^b=(-1:ℂ)^b*u^b := by rw [neg_eq_neg_one_mul,mul_pow]
  simp only [monomial,SmallLevelPrimeRates.monomial,zpow_natCast,pow_zero,
    mul_one,Rat.cast_neg,Rat.cast_pow,Rat.cast_one,hn]
  ring

theorem taylor_coefficient (x y z η a u v : ℂ) (e : ℤ×ℤ×ℤ) (q : ℕ) :
    ((-(if 3∣q then -1 else 1)*(if 11∣q then -1 else 1):ℚ):ℂ)*
      monomial x y z η a u v (e.1,e.2.1,e.2.2,1,0,
        (if 3∣q then 1 else 0),(if 11∣q then 1 else 0))=
      -((if 3∣q then -u else 1)*(if 11∣q then -v else 1))*η*
        SmallLevelPrimeRates.monomial e x y z := by
  by_cases h3 : 3∣q <;> by_cases h11 : 11∣q <;>
    simp [h3,h11,monomial,SmallLevelPrimeRates.monomial] <;> ring

theorem monomial_eigenInverse (x y z η a u v : ℂ) (p : ℕ) :
    monomial x y z η a u v (eigenInverseExponent p)=
      primeEigenvalue p a u v*(primeParameter p x y z)⁻¹ := by
  by_cases h2 : p=2 <;> by_cases h3 : p=3 <;>
    simp [eigenInverseExponent,monomial,primeEigenvalue,primeParameter,h2,h3] <;> ring

theorem monomial_inverseSquare (x y z η a u v : ℂ) (p : ℕ) :
    monomial x y z η a u v (inverseExponent p 2)=
      ((primeParameter p x y z)⁻¹)^2 := by
  by_cases h2 : p=2 <;> by_cases h3 : p=3 <;>
    simp [inverseExponent,monomial,primeParameter,h2,h3,zpow_neg,inv_pow]

theorem eval_word (x y z η a u v : ℂ) (w : Fin 66 → ℂ) (i : Fin 588) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ))) (wordRow i)=
      laurentRows x y z η a u v w (.word i) := by
  simp only [wordRow,eval_append,eval_point,word_coefficient,monomial_zero,
    Rat.cast_one,one_mul,laurentRows]
  ring

theorem eval_taylor (x y z η a u v : ℂ) (w : Fin 66 → ℂ) (i : Fin 72) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ))) (taylorRow i)=
      laurentRows x y z η a u v w (.taylor i) := by
  simp only [taylorRow,eval_append,eval_sample,taylor_coefficient,monomial_zero,
    Rat.cast_one,one_mul,laurentRows]
  ring

theorem eval_hecke (x y z η a u v : ℂ) (w : Fin 66 → ℂ) (i : Fin 61) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ))) (heckeRow i)=
      laurentRows x y z η a u v w (.hecke i) := by
  by_cases h : gridHeckeP i∣33 <;>
    simp [heckeRow,h,eval_append,eval_rangeTerms,eval_point,monomial_zero,
      monomial_eigenInverse,monomial_inverseSquare,laurentRows,laurentHecke] <;> ring

/-- One proof per constructor, valid also when any formal parameter is zero. -/
theorem compile_correct (x y z η a u v : ℂ) (w : Fin 66 → ℂ) (i : GridSource) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ))) (compile i)=
      laurentRows x y z η a u v w i := by
  cases i with
  | word i => exact eval_word x y z η a u v w i
  | taylor i => exact eval_taylor x y z η a u v w i
  | hecke i => exact eval_hecke x y z η a u v w i
  | entire i => simp [compile,eval_sample,monomial_zero,laurentRows]
  | infinity i => simp [compile,eval_point,monomial_zero,laurentRows]

theorem normalized_compile_correct (x y z η a u v : ℂ) (w : Fin 66 → ℂ)
    (i : GridSource) :
    eval x y z η a u v (fun j => w (gridIndex (j:ℤ)))
      (normalizeLaurent (compile i))=laurentRows x y z η a u v w i := by
  rw [eval_normalizeLaurent,compile_correct]

#print axioms compile_correct
#print axioms normalized_compile_correct

end QuantitativeArithmeticCompact33
