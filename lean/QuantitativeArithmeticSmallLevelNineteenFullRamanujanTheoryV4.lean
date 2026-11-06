module

public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenFullGroupTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGridAnalyticTheoryV4
public import SmallLevelTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelNineteenFullRamanujan. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelNineteenFullRamanujanRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullRamanujan
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelNineteenGridAnalytic (gridVector gridIndex gridVector_index)

def rowQ : Fin 96 → ℕ := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,6,6,6,6,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,19,38,38,38,38,38,38,57,57,57,57,57,57,114,114]
def rowT : Fin 96 → ℤ := ![1,-1,2,-2,3,-3,4,-4,6,-6,9,-9,12,-12,18,-18,19,-19,36,-36,38,-38,57,-57,76,-76,114,-114,171,-171,228,-228,342,-342,684,-684,1,-1,3,-3,9,-9,19,-19,57,-57,171,-171,1,-1,2,-2,4,-4,19,-19,38,-38,76,-76,1,-1,19,-19,1,-1,2,-2,3,-3,4,-4,6,-6,9,-9,12,-12,18,-18,36,-36,1,-1,3,-3,9,-9,1,-1,2,-2,4,-4,1,-1]
def rowL (i : Fin 96) : ℕ := Nat.lcm 19 ((rowQ i)^2)
def rowD : Fin 96 → ℤ := ![684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,684,171,171,171,171,171,171,171,171,171,171,171,171,76,76,76,76,76,76,76,76,76,76,76,76,19,19,19,19,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,36,9,9,9,9,9,9,4,4,4,4,4,4,1,1]
def rowPartner (i : Fin 96) : ℤ := -(rowD i/rowT i)
def entireSpecs : Fin 8 → ℕ := ![1,2,3,6,19,38,57,114]

theorem specs_valid (i : Fin 96) : 0<rowQ i ∧ rowQ i∣114 ∧ rowT i≠0 ∧
    (rowL i:ℤ)*rowD i=(114:ℤ)^2 ∧ rowT i∣rowD i := by revert i; decide

theorem entireSpecs_valid (i : Fin 8) : 0<entireSpecs i ∧ entireSpecs i∣114 := by
  revert i
  decide

def sumRow (q : ℕ) (t : ℤ) (v : Fin 114 → ℂ) : ℂ :=
  ∑ a∈residues q, v (gridIndex (t+(a:ℤ)*(114/q:ℕ)))
def plusRows (v : Fin 114 → ℂ) (i : Fin 96) : ℂ := sumRow (rowQ i) (rowT i) v
def minusRows (v : Fin 114 → ℂ) (i : Fin 96) : ℂ := sumRow (rowQ i) (rowPartner i) v
def entireRows (v : Fin 114 → ℂ) (i : Fin 8) : ℂ := sumRow (entireSpecs i) 0 v

theorem sumRow_grid (q : ℕ) (t : ℤ) (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    sumRow q t (gridVector k f s)=gridSum k f 114 q t s := by
  simp only [sumRow,gridSum,gridVector_index]

theorem plusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 96) :
    plusRows (gridVector k f s) i=gridSum k f 114 (rowQ i) (rowT i) s :=
  sumRow_grid _ _ _ _ _
theorem minusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 96) :
    minusRows (gridVector k f s) i=gridSum k f 114 (rowQ i) (rowPartner i) s :=
  sumRow_grid _ _ _ _ _
theorem entireRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 8) :
    entireRows (gridVector k f s) i=gridSum k f 114 (entireSpecs i) 0 s :=
  sumRow_grid _ _ _ _ _

def rowCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 96) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (rowL i) ((rowT i:ℝ)/114) (root 19 f (rowQ i)*ε*I^k) n s

def rowError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 96) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f (rowQ i)) k)
    (rowL i) ((rowT i:ℝ)/114) (root 19 f (rowQ i)*ε*I^k) (M+1)) s

theorem original_taylor_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 19 (2*m) f ε) (i : Fin 96) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (rowError (2*m) f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        plusRows (gridVector (2*m) f s) i-
          rowCoefficient (2*m) f ε i 0 s*minusRows (gridVector (2*m) f s) i=
        rowError (2*m) f ε i M s+∑ n∈Finset.range M,
          rowCoefficient (2*m) f ε i (n+1) s*
            minusRows (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
    (by decide : 0<19) (even_two_mul m) hf ε hlaw 114 (rowQ i) (by decide)
    (specs_valid i).1 (specs_valid i).2.1 (rowT i) (rowD i)
    (specs_valid i).2.2.1 (specs_valid i).2.2.2.1 (specs_valid i).2.2.2.2
  refine ⟨B,?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro s hs
  simpa only [plusRows_grid,minusRows_grid,rowCoefficient,rowError,rowPartner,rowL,Nat.cast_ofNat] using (hB M).2 s hs

theorem original_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 k f) :
    (∀ i : Fin 8, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 19 k f (entireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 8, ∀ s : ℂ, B<s.re →
        ramanujanEntire 19 k f (entireSpecs i) s=entireRows (gridVector k f s) i := by
  have hh (i : Fin 8) := original_ramanujan_entire (by decide : 0<19) hk hf (entireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
    rw [entireRows_grid,hb i s (lt_of_le_of_lt hbi hs)]
    have hg := ramanujanAdditive_grid k f (by decide : 0<114)
      (entireSpecs_valid i).1 (entireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

#print axioms original_taylor_rows
#print axioms original_entire_rows
end QuantitativeArithmeticSmallLevelNineteenFullRamanujan
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenFullRamanujanLaurentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenFullRamanujan
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelNineteenGridSystem
  (threePrimeMonomial primeParameter phaseRoot badNineteen real_three_prime_power)
open QuantitativeArithmeticSmallLevelNineteenFullGroup (primeParameter_shift)

def powers : Fin 96 → ℤ×ℤ×ℤ :=
  ![(-2,-2,-1),(-2,-2,-1),(0,-2,-1),(0,-2,-1),(-2,0,-1),(-2,0,-1),(2,-2,-1),(2,-2,-1),(0,0,-1),(0,0,-1),(-2,2,-1),(-2,2,-1),(2,0,-1),(2,0,-1),(0,2,-1),(0,2,-1),(-2,-2,1),(-2,-2,1),(2,2,-1),(2,2,-1),(0,-2,1),(0,-2,1),(-2,0,1),(-2,0,1),(2,-2,1),(2,-2,1),(0,0,1),(0,0,1),(-2,2,1),(-2,2,1),(2,0,1),(2,0,1),(0,2,1),(0,2,1),(2,2,1),(2,2,1),(0,-2,-1),(0,-2,-1),(0,0,-1),(0,0,-1),(0,2,-1),(0,2,-1),(0,-2,1),(0,-2,1),(0,0,1),(0,0,1),(0,2,1),(0,2,1),(-2,0,-1),(-2,0,-1),(0,0,-1),(0,0,-1),(2,0,-1),(2,0,-1),(-2,0,1),(-2,0,1),(0,0,1),(0,0,1),(2,0,1),(2,0,1),(0,0,-1),(0,0,-1),(0,0,1),(0,0,1),(-2,-2,0),(-2,-2,0),(0,-2,0),(0,-2,0),(-2,0,0),(-2,0,0),(2,-2,0),(2,-2,0),(0,0,0),(0,0,0),(-2,2,0),(-2,2,0),(2,0,0),(2,0,0),(0,2,0),(0,2,0),(2,2,0),(2,2,0),(0,-2,0),(0,-2,0),(0,0,0),(0,0,0),(0,2,0),(0,2,0),(-2,0,0),(-2,0,0),(0,0,0),(0,0,0),(2,0,0),(2,0,0),(0,0,0),(0,0,0)]
def taylorSign (χ δ : ℂ) (i : Fin 96) : ℂ := if 19∣rowQ i then -χ*δ else χ
def symbolic (χ δ X Y Z : ℂ) (i : Fin 96) : ℂ :=
  taylorSign χ δ i*threePrimeMonomial (powers i) X Y Z

theorem rate_certificate (i : Fin 96) :
    (rowL i:ℝ)*((rowT i:ℝ)/114)^2=
      (2:ℝ)^(powers i).1*(3:ℝ)^(powers i).2.1*(19:ℝ)^(powers i).2.2 := by
  fin_cases i <;> norm_num [rowL,rowQ,rowT,powers]

/-- At prime level19 the root factor depends only on whether19 divides q;
this applies to every positive modulus, not just the selected grid rows. -/
theorem root_any_modulus (f : ℕ→ℂ) {q : ℕ} (hq : 0<q) :
    root 19 f q=if 19∣q then -badNineteen f else 1 := by
  have hp19 : Nat.Prime 19 := by decide
  have other (p : ℕ) (hp : p∈q.primeFactors) (hne : p≠19) :
      FinitenessNormalizedTwistLocal.sign 19 f p (q.factorization p)=1 := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hnd : ¬p∣19 := by
      rw [Nat.dvd_prime hp19]
      simp only [hprime.ne_one,hne,or_self,not_false_eq_true]
    simp [FinitenessNormalizedTwistLocal.sign,hnd]
  unfold root
  split_ifs with hd
  · have hmem : 19∈q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp19,hd,hq.ne'⟩
    rw [Finset.prod_eq_single 19 (fun p hp hne => other p hp hne)
      (fun hn => False.elim (hn hmem))]
    have hfac : q.factorization 19≠0 := (hp19.factorization_pos_of_dvd hq.ne' hd).ne'
    norm_num [FinitenessNormalizedTwistLocal.sign,hfac,badNineteen,hq.ne',hd]
    ring
  · apply Finset.prod_eq_one
    intro p hp
    apply other p hp
    intro he
    apply hd
    subst p
    exact Nat.dvd_of_mem_primeFactors hp

theorem root_scalar (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 96) :
    root 19 f (rowQ i)*ε*I^(2*m)=taylorSign (phaseRoot m ε) (badNineteen f) i := by
  rw [root_any_modulus f (specs_valid i).1]
  unfold taylorSign phaseRoot
  split_ifs <;> ring

theorem coefficient_laurent (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 96) :
    rowCoefficient (2*m) f ε i 0 s=symbolic (phaseRoot m ε) (badNineteen f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 19 m s) i := by
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  simp only [rowCoefficient,taylorRowScalar,pow_zero,Ring.choose_zero_right,mul_one,hex,root_scalar]
  rw [real_three_prime_power _ _ (rate_certificate i)]
  rfl

#print axioms root_any_modulus
#print axioms coefficient_laurent
end QuantitativeArithmeticSmallLevelNineteenFullRamanujan
end
end
