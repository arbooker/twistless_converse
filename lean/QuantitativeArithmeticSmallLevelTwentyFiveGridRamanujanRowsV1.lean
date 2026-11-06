module
public import QuantitativeArithmeticSmallLevelTwentyFiveSelectedWordsTheoryV4
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import SmallLevelTaylorTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.GridRamanujan
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords (gridVector gridIndex gridVector_index)

def rowQ : Fin 47 → ℕ := ![1,1,1,1,1,1,1,1,1,3,30,3,3,3,3,3,3,3,5,5,3,5,5,5,5,5,5,6,6,5,5,5,5,10,10,15,5,15,15,5,5,5,15,25,5,5,25]
def rowT : Fin 47 → ℤ := ![-1,5,9,-9,10,20,-20,25,-25,10,5,1,-1,2,-2,4,-4,5,-10,10,-5,-5,5,6,-6,12,-12,1,-1,3,-3,9,-9,1,-1,-2,-2,1,2,-4,-1,4,-1,1,2,1,-1]
def rowL (i : Fin 47) : ℕ := Nat.lcm 25 ((rowQ i)^2)
def rowD : Fin 47 → ℤ := ![900,900,900,900,900,900,900,900,900,100,25,100,100,100,100,100,100,100,900,900,100,900,900,900,900,900,900,25,25,900,900,900,900,225,225,100,900,100,100,900,900,900,100,36,900,900,36]
def rowPartner (i : Fin 47) : ℤ := -(rowD i/rowT i)
def entireSpecs : Fin 4 → ℕ := ![1,3,6,5]

theorem specs_valid (i : Fin 47) : 0<rowQ i ∧ rowQ i∣150 ∧ rowT i≠0 ∧
    (rowL i:ℤ)*rowD i=(150:ℤ)^2 ∧ rowT i∣rowD i := by fin_cases i <;> decide

theorem entireSpecs_valid (i : Fin 4) : 0<entireSpecs i ∧ entireSpecs i∣150 := by
  fin_cases i <;> decide

def sumRow (q : ℕ) (t : ℤ) (v : Fin 150 → ℂ) : ℂ :=
  ∑ a∈residues q, v (gridIndex (t+(a:ℤ)*(150/q:ℕ)))
def plusRows (v : Fin 150 → ℂ) (i : Fin 47) : ℂ := sumRow (rowQ i) (rowT i) v
def minusRows (v : Fin 150 → ℂ) (i : Fin 47) : ℂ := sumRow (rowQ i) (rowPartner i) v
def entireRows (v : Fin 150 → ℂ) (i : Fin 4) : ℂ := sumRow (entireSpecs i) 0 v

theorem sumRow_grid (q : ℕ) (t : ℤ) (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    sumRow q t (gridVector k f s)=gridSum k f 150 q t s := by
  simp only [sumRow,gridSum,gridVector_index]

theorem plusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 47) :
    plusRows (gridVector k f s) i=gridSum k f 150 (rowQ i) (rowT i) s :=
  sumRow_grid _ _ _ _ _
theorem minusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 47) :
    minusRows (gridVector k f s) i=gridSum k f 150 (rowQ i) (rowPartner i) s :=
  sumRow_grid _ _ _ _ _
theorem entireRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 4) :
    entireRows (gridVector k f s) i=gridSum k f 150 (entireSpecs i) 0 s :=
  sumRow_grid _ _ _ _ _

def rowCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 47) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (rowL i) ((rowT i:ℝ)/150) (root 25 f (rowQ i)*ε*I^k) n s

def rowError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 47) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f (rowQ i)) k)
    (rowL i) ((rowT i:ℝ)/150) (root 25 f (rowQ i)*ε*I^k) (M+1)) s

theorem original_taylor_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε) (i : Fin 47) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (rowError (2*m) f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        plusRows (gridVector (2*m) f s) i-
          rowCoefficient (2*m) f ε i 0 s*minusRows (gridVector (2*m) f s) i=
        rowError (2*m) f ε i M s+∑ n∈Finset.range M,
          rowCoefficient (2*m) f ε i (n+1) s*
            minusRows (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
    (by decide : 0<25) (even_two_mul m) hf ε hlaw 150 (rowQ i) (by decide)
    (specs_valid i).1 (specs_valid i).2.1 (rowT i) (rowD i)
    (specs_valid i).2.2.1 (specs_valid i).2.2.2.1 (specs_valid i).2.2.2.2
  refine ⟨B,?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro s hs
  simpa only [plusRows_grid,minusRows_grid,rowCoefficient,rowError,rowPartner,rowL,Nat.cast_ofNat] using (hB M).2 s hs

theorem original_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 k f) :
    (∀ i : Fin 4, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 25 k f (entireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 4, ∀ s : ℂ, B<s.re →
        ramanujanEntire 25 k f (entireSpecs i) s=entireRows (gridVector k f s) i := by
  have hh (i : Fin 4) := original_ramanujan_entire (by decide : 0<25) hk hf (entireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
    rw [entireRows_grid,hb i s (lt_of_le_of_lt hbi hs)]
    have hg := ramanujanAdditive_grid k f (by decide : 0<150)
      (entireSpecs_valid i).1 (entireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

/-- All coefficients of the selected Ramanujan Taylor rows are entire. -/
theorem rowCoefficient_analytic (k : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (i : Fin 47) (n : ℕ) (z : ℂ) : AnalyticAt ℂ (rowCoefficient k f ε i n) z := by
  have hL : 0<(rowL i:ℝ) := by
    exact_mod_cast Nat.lcm_pos (by decide : 0<25) (pow_pos (specs_valid i).1 2)
  have ht : ((rowT i:ℝ)/150)≠0 :=
    div_ne_zero (by exact_mod_cast (specs_valid i).2.2.1) (by norm_num)
  exact taylorRowScalar_analytic k hL ht (root 25 f (rowQ i)*ε*I^k) n z

#print axioms rowCoefficient_analytic

#print axioms original_taylor_rows
#print axioms original_entire_rows
end QuantitativeArithmeticSmallLevelTwentyFive.GridRamanujan
