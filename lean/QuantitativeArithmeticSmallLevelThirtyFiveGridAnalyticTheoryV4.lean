module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveFullGridCaseIndexDataSeriesV4
public import QuantitativeArithmeticSmallLevelThirtyFiveFullGridTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRowsTheoryV4
public import QuantitativeArithmeticTwoSequenceTaylorTheoryV4
public import SmallLevelAdditiveTheoryV4
public import SmallLevelContinuationTheoryV4
public import SmallLevelTaylorRowCoefficientsV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticGroupV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Set SmallLevelAdditive FinitenessOriginalFourier
open QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open QuantitativeArithmeticTwoSequenceTaylor

def gridIndex (t : ℤ) : Fin 210 :=
  ⟨(t%210).toNat,by have h := Int.emod_lt_of_pos t (by decide : (0:ℤ)<210); omega⟩

def gridVector (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : Fin 210 → ℂ :=
  fun j => grid k f 210 (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ → ℂ) (t : ℤ) (s : ℂ) :
    gridVector k f s (gridIndex t)=grid k f 210 t s := by
  have he : ((gridIndex t).val:ℤ)=t%210 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  unfold gridVector
  rw [he]
  exact grid_mod k f (by decide : 0<210) t s

def gA (i : Fin 7) : ℝ := (row i).val 0 0
def gB (i : Fin 7) : ℝ := (row i).val 0 1
def gC (i : Fin 7) : ℝ := (row i).val 1 0
def gD (i : Fin 7) : ℝ := (row i).val 1 1

theorem gC_ne_zero (i : Fin 7) : gC i≠0 := by
  fin_cases i <;> norm_num [gC,row]

theorem gdet (i : Fin 7) : gA i*gD i-gB i*gC i=1 := by
  fin_cases i <;> norm_num [gA,gB,gC,gD,row]

/-- Actual all-order Taylor rows for each selected integral group matrix.
No continuation assumption is made about any additive coordinate. -/
theorem original_group_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (i : Fin 7) (j : ℝ) (hj : gC i*j+gD i≠0) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform (fullCoefficients f (2*m)) j s-
          (((gC i*j+gD i)^2:ℝ):ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (I*((gC i*(gC i*j+gD i):ℝ):ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              transform (fullCoefficients f (2*m))
                ((gA i*j+gB i)/(gC i*j+gD i)) (s+(n:ℂ))) = error M s := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF : ∀ z : ℂ, 0<z.im →
      FinitenessFourierConstruction.fourier (fullCoefficients f (2*m)) z=
        (1*((gA i*gD i-gB i*gC i:ℝ):ℂ)^m)/
          (((gC i:ℂ)*z+(gD i:ℂ))^(2*m))*
          FinitenessFourierConstruction.fourier (fullCoefficients f (2*m))
            (((gA i:ℂ)*z+(gB i:ℂ))/((gC i:ℂ)*z+(gD i:ℂ))) := by
    intro z hz
    rw [gdet]
    simpa only [Complex.ofReal_one,one_pow,mul_one,gA,gB,gC,gD,
      Complex.ofReal_intCast] using original_rows_fourier (by omega : 0<2*m) hf i z hz
  have h := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (gA i) (gB i) (gC i) (gD i) j (gC_ne_zero i)
    (by rw [gdet]; norm_num) hj 1 hF
  simpa only [gdet,div_one,one_mul] using h

#print axioms gridVector_index
#print axioms original_group_rows
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticSelectedV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Set SmallLevelAdditive FinitenessOriginalFourier

/-- The 44 selected SL2 group rows, in their relative order in the full
210-row input certificate: matrix index, source grid index, exact partner. -/
def groupSpecs : Fin 44 → (Fin 7 × ℤ × ℤ) :=
  ![(0,186,8),(0,202,24),(1,102,-2),(1,105,0),(1,106,-6),(1,108,-3),(2,104,-2),(2,107,-8),(2,110,-5),(3,72,-11),(3,90,-10),(3,96,-9),(3,99,-8),(3,109,-48),(3,111,-24),(3,112,-21),(3,114,-18),(3,117,-16),(3,120,-15),(3,144,-13),(4,66,13),(4,93,16),(4,98,21),(4,100,30),(4,101,48),(4,103,-24),(4,138,11),(5,168,-7),(5,174,-6),(5,175,0),(5,176,-9),(5,177,-8),(6,138,37),(6,156,38),(6,162,39),(6,165,40),(6,170,45),(6,171,48),(6,172,54),(6,173,72),(6,178,27),(6,183,32),(6,186,33),(6,192,34)]

def groupMatrix (i : Fin 44) : Fin 7 := (groupSpecs i).1
def groupSource (i : Fin 44) : ℤ := (groupSpecs i).2.1
def groupPartner (i : Fin 44) : ℤ := (groupSpecs i).2.2
def groupCenter (i : Fin 44) : ℝ := (groupSource i:ℝ)/210

theorem group_denominator (i : Fin 44) :
    gC (groupMatrix i)*groupCenter i+gD (groupMatrix i)≠0 := by
  fin_cases i <;> norm_num [groupMatrix,groupCenter,groupSource,groupSpecs,
    gC,gD,QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row]

theorem group_partner (i : Fin 44) :
    (gA (groupMatrix i)*groupCenter i+gB (groupMatrix i))/
      (gC (groupMatrix i)*groupCenter i+gD (groupMatrix i))=
        (groupPartner i:ℝ)/210 := by
  fin_cases i <;> norm_num [groupMatrix,groupCenter,groupSource,groupPartner,groupSpecs,
    gA,gB,gC,gD,QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row]

def groupRate (i : Fin 44) : ℝ :=
  (gC (groupMatrix i)*groupCenter i+gD (groupMatrix i))^2

def groupDerivativeRate (i : Fin 44) : ℝ :=
  gC (groupMatrix i)*(gC (groupMatrix i)*groupCenter i+gD (groupMatrix i))

theorem groupRate_pos (i : Fin 44) : 0<groupRate i :=
  sq_pos_of_ne_zero (group_denominator i)

/-- Every selected SL2 row on the actual 210-grid, at every Taylor order,
with its own entire-to-the-left remainder supplied by the original input. -/
theorem original_selected_group_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (i : Fin 44) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        gridVector (2*m) f s (gridIndex (groupSource i))-
          (groupRate i:ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (I*(groupDerivativeRate i:ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              gridVector (2*m) f (s+(n:ℂ)) (gridIndex (groupPartner i))) = error M s := by
  obtain ⟨bound,error,h⟩ := original_group_rows hm hf (groupMatrix i)
    (groupCenter i) (group_denominator i)
  refine ⟨bound,error,fun M => ⟨(h M).1,?_⟩⟩
  intro s hs
  have he := (h M).2 s hs
  rw [group_partner] at he
  simpa only [groupRate,groupDerivativeRate,gridVector_index,
    grid,original,groupCenter,Nat.cast_ofNat] using he

#print axioms group_partner
#print axioms original_selected_group_rows
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Set SmallLevelAdditive

def groupCoefficient (m : ℕ) (i : Fin 44) (n : ℕ) (s : ℂ) : ℂ :=
  (groupRate i:ℂ)^(s-(m:ℂ))*(I*(groupDerivativeRate i:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

theorem groupCoefficient_analytic (m : ℕ) (i : Fin 44) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (groupCoefficient m i n) z := by
  have hc : (groupRate i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (groupRate_pos i).ne'
  have hp : AnalyticAt ℂ (fun s : ℂ => (groupRate i:ℂ)^(s-(m:ℂ))) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact (hp.mul analyticAt_const).mul (SmallLevelTaylor.binomial_shift_analytic (2*m) n z)

/-- The complete selected group system on a common initial half-plane.
The shift index is n+1; hence every remainder extends M+1 units left. -/
theorem original_group_system {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (B : ℝ) (error : Fin 44 → ℕ → ℂ → ℂ), ∀ i : Fin 44, ∀ M : ℕ,
      AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector (2*m) f s (gridIndex (groupSource i))-
          groupCoefficient m i 0 s*gridVector (2*m) f s (gridIndex (groupPartner i))=
        error i M s+
          ∑ n∈Finset.range M, groupCoefficient m i (n+1) s*
            gridVector (2*m) f (s+((n:ℂ)+1)) (gridIndex (groupPartner i)) := by
  choose b err h using original_selected_group_rows hm hf
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 44) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,fun i M => err i (M+1),?_⟩
  intro i M
  constructor
  · intro s hs
    apply (h i (M+1)).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M+1:ℕ):ℝ)<s.re
    push_cast
    linarith [hbB i]
  · intro s hs
    have he := (h i (M+1)).2 s (lt_of_le_of_lt (hbB i) hs)
    rw [Finset.sum_range_succ'] at he
    simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,
      Nat.cast_add,Nat.cast_one] at he
    simp only [groupCoefficient,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,
      mul_one,Nat.cast_add,Nat.cast_one]
    rw [mul_add,Finset.mul_sum] at he
    simp only [mul_assoc,one_mul] at he ⊢
    linear_combination he

#print axioms groupCoefficient_analytic
#print axioms original_group_system
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticMatrixV1 -/
section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix SmallLevelTaylor SmallLevelAdditive FinitenessRamanujanSum

inductive RowKind where
  | group : Fin 44 → RowKind
  | taylor : Fin 89 → RowKind
  | entire : Fin 11 → RowKind
  | hecke : Fin 66 → RowKind
  deriving DecidableEq

/-- Exact row order of the selected 210-row certificate. -/
def rowKind : Fin 210 → RowKind :=
  ![.taylor 53,.taylor 54,.taylor 55,.taylor 56,.entire 0,.taylor 57,.taylor 58,.taylor 59,.taylor 60,.taylor 61,.taylor 62,.taylor 63,.taylor 64,.taylor 65,.taylor 66,.taylor 67,.taylor 68,.taylor 69,.taylor 70,.taylor 71,.taylor 72,.taylor 73,.taylor 74,.taylor 75,.taylor 76,.taylor 77,.taylor 78,.taylor 79,.taylor 80,.taylor 81,.taylor 82,.taylor 83,.taylor 84,.taylor 85,.taylor 86,.taylor 87,.taylor 88,.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.group 24,.group 25,.group 26,.group 27,.group 28,.group 29,.group 30,.group 31,.group 32,.group 33,.group 34,.group 35,.group 36,.group 37,.group 38,.group 39,.group 40,.group 41,.group 42,.group 43,.entire 1,.taylor 0,.taylor 1,.taylor 2,.taylor 3,.taylor 4,.taylor 5,.taylor 6,.taylor 7,.taylor 8,.taylor 9,.taylor 10,.taylor 11,.entire 2,.taylor 12,.taylor 13,.taylor 14,.taylor 15,.taylor 16,.taylor 17,.taylor 18,.taylor 19,.taylor 20,.taylor 21,.taylor 22,.taylor 23,.taylor 24,.taylor 25,.taylor 26,.taylor 27,.entire 3,.taylor 28,.taylor 29,.taylor 30,.taylor 31,.taylor 32,.taylor 33,.taylor 34,.taylor 35,.taylor 36,.taylor 37,.taylor 38,.taylor 39,.entire 4,.taylor 40,.taylor 41,.entire 5,.entire 6,.taylor 42,.taylor 43,.taylor 44,.taylor 45,.taylor 46,.taylor 47,.entire 7,.taylor 48,.taylor 49,.entire 8,.taylor 50,.taylor 51,.taylor 52,.entire 9,.entire 10,.hecke 0,.hecke 1,.hecke 2,.hecke 3,.hecke 4,.hecke 5,.hecke 6,.hecke 7,.hecke 8,.hecke 9,.hecke 10,.hecke 11,.hecke 12,.hecke 13,.hecke 14,.hecke 15,.hecke 16,.hecke 17,.hecke 18,.hecke 19,.hecke 20,.hecke 21,.hecke 22,.hecke 23,.hecke 24,.hecke 25,.hecke 26,.hecke 27,.hecke 28,.hecke 29,.hecke 30,.hecke 31,.hecke 32,.hecke 33,.hecke 34,.hecke 35,.hecke 36,.hecke 37,.hecke 38,.hecke 39,.hecke 40,.hecke 41,.hecke 42,.hecke 43,.hecke 44,.hecke 45,.hecke 46,.hecke 47,.hecke 48,.hecke 49,.hecke 50,.hecke 51,.hecke 52,.hecke 53,.hecke 54,.hecke 55,.hecke 56,.hecke 57,.hecke 58,.hecke 59,.hecke 60,.hecke 61,.hecke 62,.hecke 63,.hecke 64,.hecke 65]

def assemble (G : Fin 44 → ℂ) (T : Fin 89 → ℂ) (Rr : Fin 11 → ℂ)
    (H : Fin 66 → ℂ) (i : Fin 210) : ℂ :=
  match rowKind i with
  | .group j => G j
  | .taylor j => T j
  | .entire j => Rr j
  | .hecke j => H j

def sampleSum (q : ℕ) (t : ℤ) (w : Fin 210 → ℂ) : ℂ :=
  ∑ j∈residues q, w (gridIndex (t+(j:ℤ)*(210/q:ℕ)))

def completeSum (p : ℕ) (t : ℤ) (w : Fin 210 → ℂ) : ℂ :=
  ∑ j∈Finset.range p, w (gridIndex (t+(j:ℤ)*(210/p:ℕ)))

theorem sampleSum_grid (k : ℕ) (f : ℕ → ℂ) (q : ℕ) (t : ℤ) (s : ℂ) :
    sampleSum q t (gridVector k f s)=gridSum k f 210 q t s := by
  simp only [sampleSum,gridSum,gridVector_index]

theorem sampleSum_add (q : ℕ) (t : ℤ) (w z : Fin 210 → ℂ) :
    sampleSum q t (w+z)=sampleSum q t w+sampleSum q t z := by
  simp [sampleSum,Finset.sum_add_distrib]

theorem sampleSum_smul (q : ℕ) (t : ℤ) (c : ℂ) (w : Fin 210 → ℂ) :
    sampleSum q t (c • w)=c*sampleSum q t w := by
  simp [sampleSum,Finset.mul_sum]

def groupLeading (m : ℕ) (s : ℂ) (w : Fin 210 → ℂ) (i : Fin 44) : ℂ :=
  w (gridIndex (groupSource i))-groupCoefficient m i 0 s*w (gridIndex (groupPartner i))

def taylorLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 210 → ℂ) (i : Fin 89) : ℂ :=
  sampleSum (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowQ i) (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowT i) w-
    QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowCoefficient (2*m) f ε i 0 s*sampleSum (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowQ i) (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowPartner i) w

def heckeLeading (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (w : Fin 210 → ℂ) (i : Fin 66) : ℂ :=
  let p := (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeSpecs i).1
  let j := (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeSpecs i).2
  completeSum p j w-((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*w (gridIndex ((p:ℤ)*j))+
    if p∣35 then 0 else ((p:ℂ)^((m:ℂ)-s))^2*w (gridIndex ((p:ℤ)^2*j))

theorem heckeLeading_grid (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (i : Fin 66) :
    heckeLeading m f s (gridVector (2*m) f s) i=
      QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeLeading m f (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeSpecs i).1 (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeSpecs i).2 s := by
  simp only [heckeLeading,completeSum,gridVector_index,QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeLeading]

def leadingRows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 210 → ℂ) : Fin 210 → ℂ :=
  assemble (groupLeading m s w) (taylorLeading m f ε s w)
    (fun i => sampleSum (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.entireSpecs i) 0 w) (heckeLeading m f s w)

def shiftRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 210 → ℂ) : Fin 210 → ℂ :=
  assemble (fun i => groupCoefficient m i (n+1) s*w (gridIndex (groupPartner i)))
    (fun i => QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowCoefficient (2*m) f ε i (n+1) s*sampleSum (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowQ i) (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowPartner i) w) 0 0

def leadingLinear (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : (Fin 210 → ℂ) →ₗ[ℂ] (Fin 210 → ℂ) where
  toFun := leadingRows m f ε s
  map_add' := by
    intro w z
    funext i
    cases h : rowKind i <;>
      simp only [leadingRows,assemble,h,groupLeading,taylorLeading,heckeLeading,
        sampleSum_add,completeSum,Pi.add_apply,Finset.sum_add_distrib]
    all_goals (try split_ifs) <;> ring
  map_smul' := by
    intro c w
    funext i
    cases h : rowKind i <;>
      simp only [leadingRows,assemble,h,groupLeading,taylorLeading,heckeLeading,
        sampleSum_smul,completeSum,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,
        ← Finset.mul_sum]
    all_goals (try split_ifs) <;> ring

def shiftLinear (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    (Fin 210 → ℂ) →ₗ[ℂ] (Fin 210 → ℂ) where
  toFun := shiftRows m f ε n s
  map_add' := by
    intro w z
    funext i
    cases h : rowKind i <;> simp [shiftRows,assemble,h,sampleSum_add,mul_add]
  map_smul' := by
    intro c w
    funext i
    cases h : rowKind i <;> simp [shiftRows,assemble,h,sampleSum_smul,smul_eq_mul] <;> ring

def leadingMatrix (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  (leadingLinear m f ε s).toMatrix'
def shiftMatrix (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 210) (Fin 210) ℂ :=
  (shiftLinear m f ε n s).toMatrix'

theorem leadingMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 210 → ℂ) :
    leadingMatrix m f ε s *ᵥ w=leadingRows m f ε s w := LinearMap.toMatrix'_mulVec _ _
theorem shiftMatrix_mulVec (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (w : Fin 210 → ℂ) :
    shiftMatrix m f ε n s *ᵥ w=shiftRows m f ε n s w := LinearMap.toMatrix'_mulVec _ _

#print axioms sampleSum_grid
#print axioms heckeLeading_grid
#print axioms leadingMatrix_mulVec
#print axioms shiftMatrix_mulVec
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticEntriesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix

theorem leadingMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i j : Fin 210) :
    leadingMatrix m f ε s i j=leadingRows m f ε s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _
theorem shiftMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i j : Fin 210) :
    shiftMatrix m f ε n s i j=shiftRows m f ε n s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i j : Fin 210) :
    AnalyticAt ℂ (fun s => leadingMatrix m f ε s i j) x := by
  simp only [leadingMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [leadingRows,assemble,hi,groupLeading]
    exact analyticAt_const.sub ((groupCoefficient_analytic m a 0 x).mul analyticAt_const)
  | taylor a =>
    simp only [leadingRows,assemble,hi,taylorLeading]
    exact analyticAt_const.sub
      ((QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowCoefficient_analytic
        (2*m) f ε a 0 x).mul analyticAt_const)
  | entire a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const
  | hecke a =>
    have hX := SmallLevelTaylor.hecke_parameter_analytic
      (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeSpecs_valid a).1.pos m x
    simp only [leadingRows,assemble,hi,heckeLeading]
    split_ifs <;> fun_prop

theorem shiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i j : Fin 210) :
    AnalyticAt ℂ (fun s => shiftMatrix m f ε n s i j) x := by
  simp only [shiftMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [shiftRows,assemble,hi]
    exact (groupCoefficient_analytic m a (n+1) x).mul analyticAt_const
  | taylor a =>
    simp only [shiftRows,assemble,hi]
    exact (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowCoefficient_analytic
      (2*m) f ε a (n+1) x).mul analyticAt_const
  | entire a =>
    simp only [shiftRows,assemble,hi,Pi.zero_apply]
    exact analyticAt_const
  | hecke a =>
    simp only [shiftRows,assemble,hi,Pi.zero_apply]
    exact analyticAt_const

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex

def groupRatePowers : Fin 44 → ℤ×ℤ×ℤ×ℤ :=
  ![(0,2,0,0),(0,-2,0,0),(0,2,0,0),(-2,0,0,0),(0,-2,0,0),(2,0,0,0),(0,0,0,0),(-2,0,0,0),(2,0,0,0),(2,2,0,0),(0,2,0,0),(2,0,0,0),(-2,2,0,0),(-2,-2,0,0),(-2,0,0,0),(2,-2,0,0),(0,0,0,0),(-2,2,0,0),(2,0,0,0),(2,2,0,0),(2,2,0,0),(-2,2,0,0),(2,-2,0,0),(0,-2,0,0),(-2,-2,0,0),(-2,-2,0,0),(2,2,0,0),(2,2,0,0),(0,0,0,0),(-2,-2,0,0),(2,-2,0,0),(-2,2,0,0),(2,2,0,0),(0,2,0,0),(2,0,0,0),(-2,2,0,0),(2,-2,0,0),(-2,0,0,0),(0,-2,0,0),(-2,-2,0,0),(2,-2,0,0),(-2,2,0,0),(2,0,0,0),(0,2,0,0)]

theorem group_rate_certificate (i : Fin 44) :
    groupRate i=(2:ℝ)^(groupRatePowers i).1*(3:ℝ)^(groupRatePowers i).2.1*
      (5:ℝ)^(groupRatePowers i).2.2.1*(7:ℝ)^(groupRatePowers i).2.2.2 := by
  fin_cases i <;> norm_num [groupRate,groupRatePowers,groupMatrix,groupCenter,
    groupSource,groupSpecs,gC,gD,QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row]

def groupRateMonomial (i : Fin 44) (X Y Z W : ℂ) : ℂ :=
  X^(groupRatePowers i).1*Y^(groupRatePowers i).2.1*
    Z^(groupRatePowers i).2.2.1*W^(groupRatePowers i).2.2.2

theorem positive_zpow_cpow {p : ℝ} (hp : 0<p) (a : ℤ) (s : ℂ) :
    ((p:ℂ)^a)^s=((p:ℂ)^s)^a := by
  have harg : (p:ℂ).arg=0 := arg_ofReal_of_nonneg hp.le
  rw [← Complex.cpow_int_mul' (by simp [harg,Real.pi_pos])
    (by simp [harg,Real.pi_pos.le]),← Complex.cpow_int_mul]

theorem group_rate_complex_power (i : Fin 44) (s : ℂ) :
    (groupRate i:ℂ)^s=groupRateMonomial i
      ((2:ℂ)^s) ((3:ℂ)^s) ((5:ℂ)^s) ((7:ℂ)^s) := by
  rw [group_rate_certificate,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [positive_zpow_cpow (by norm_num : (0:ℝ)<2),
    positive_zpow_cpow (by norm_num : (0:ℝ)<3),
    positive_zpow_cpow (by norm_num : (0:ℝ)<5),
    positive_zpow_cpow (by norm_num : (0:ℝ)<7)]
  simp only [Complex.ofReal_ofNat,groupRateMonomial]

theorem groupCoefficient_complex (m : ℕ) (i : Fin 44) (s : ℂ) :
    groupCoefficient m i 0 s=groupRateMonomial i
      ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
      ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ))) := by
  simp only [groupCoefficient,pow_zero,Ring.choose_zero_right,mul_one]
  exact group_rate_complex_power i (s-(m:ℂ))

#print axioms group_rate_certificate
#print axioms groupCoefficient_complex
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticSignParityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

/-- The square in the translation contributes no parity. -/
theorem ratePower_mod_two (p : ℕ) (i : Fin 89) :
    ratePower p i%2=((rowL i).factorization p:ℤ)%2 := by
  unfold ratePower
  omega

theorem ratePower_five_parity (i : Fin 89) :
    (ratePowers i).2.2.1%2=if 5∣rowQ i then 0 else 1 := by
  rw [ratePowers_values]
  fin_cases i <;> norm_num [rowQ,taylorSpecs]

theorem ratePower_seven_parity (i : Fin 89) :
    (ratePowers i).2.2.2%2=if 7∣rowQ i then 0 else 1 := by
  rw [ratePowers_values]
  fin_cases i <;> norm_num [rowQ,taylorSpecs]

theorem neg_zpow_of_parity (z : ℂ) (n : ℤ) (P : Prop) [Decidable P]
    (hn : n%2=if P then 0 else 1) :
    (-z)^n=(if P then 1 else -1)*z^n := by
  by_cases hP : P
  · have he : Even n := Int.not_odd_iff_even.mp
      (Int.not_odd_iff.mpr (by simpa only [ite_eq_left hP] using hn))
    simpa only [ite_eq_left hP,one_mul] using he.neg_zpow z
  · have ho : Odd n := Int.odd_iff.mpr (by simpa only [ite_eq_right hP] using hn)
    simpa only [ite_eq_right hP,neg_one_mul] using ho.neg_zpow z

theorem rateMonomial_neg_five (i : Fin 89) (X Y Z W : ℂ) :
    rateMonomial i X Y (-Z) W=
      (if 5∣rowQ i then 1 else -1)*rateMonomial i X Y Z W := by
  unfold rateMonomial
  rw [neg_zpow_of_parity Z (ratePowers i).2.2.1 (5∣rowQ i) (ratePower_five_parity i)]
  ring

theorem rateMonomial_neg_seven (i : Fin 89) (X Y Z W : ℂ) :
    rateMonomial i X Y Z (-W)=
      (if 7∣rowQ i then 1 else -1)*rateMonomial i X Y Z W := by
  unfold rateMonomial
  rw [neg_zpow_of_parity W (ratePowers i).2.2.2 (7∣rowQ i) (ratePower_seven_parity i)]
  ring

theorem groupRatePowers_unramified : ∀ i : Fin 44,
    (groupRatePowers i).2.2.1=0 ∧ (groupRatePowers i).2.2.2=0 := by decide

theorem groupRateMonomial_bad_independent (i : Fin 44) (X Y Z W Z' W' : ℂ) :
    groupRateMonomial i X Y Z W=groupRateMonomial i X Y Z' W' := by
  simp only [groupRateMonomial,(groupRatePowers_unramified i).1,
    (groupRatePowers_unramified i).2,zpow_zero,mul_one]

#print axioms ratePower_five_parity
#print axioms ratePower_seven_parity
#print axioms rateMonomial_neg_five
#print axioms rateMonomial_neg_seven
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticGroupComparisonV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

/-- The selected SL2 rows occupy the uninterrupted block 37 through 80.
This uses selected-input positions, rather than the original enumeration IDs. -/
def groupInput (i : Fin 44) : Fin 210 := ⟨37+i.val,by omega⟩

theorem groupInput_kind : ∀ i : Fin 44, rowKind (groupInput i)=RowKind.group i := by
  decide

theorem leadingRows_groupInput (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 44) :
    leadingRows m f ε s w (groupInput i)=groupLeading m s w i := by
  simp only [leadingRows,assemble,groupInput_kind]

/-- There is no scalar row-clearing factor in the selected SL2 block.
The Laurent row is literally source minus its geometric rate times partner. -/
theorem selectedRows_group_block (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (w : Fin 210 → ℂ) (i : Fin 44) :
    selectedRowsV3_0 X Y Z W a b w (groupInput i)=
      w (gridIndex (groupSource i))-
        groupRateMonomial i X Y Z W*w (gridIndex (groupPartner i)) := by
  fin_cases i <;>
    norm_num [selectedRowsV3_0,selectedPart0_3,selectedPart0_4,selectedPart0_5,
      selectedPart0_6,selectedPart0_7,selectedPart0_8,groupInput,
      groupRateMonomial,groupRatePowers,groupSource,groupPartner,groupSpecs,gridIndex,
      zpow_neg,zpow_natCast] <;>
    field_simp [hX,hY] <;> ring

/-- Exact complex-rate comparison for all 44 integral group rows. -/
theorem leadingRows_group_complex (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 44) :
    leadingRows m f ε s w (groupInput i)=
      selectedRowsV3_0 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w (groupInput i) := by
  rw [leadingRows_groupInput,selectedRows_group_block]
  · simp only [groupLeading,groupCoefficient_complex]
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

#print axioms selectedRows_group_block
#print axioms leadingRows_group_complex
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticHeckeComparisonV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

/-- All selected Hecke rows are the last 66 selected inputs. -/
def heckeInput (i : Fin 66) : Fin 210 := ⟨144+i.val,by omega⟩

theorem heckeInput_kind : ∀ i : Fin 66, rowKind (heckeInput i)=RowKind.hecke i := by
  decide

theorem leadingRows_heckeInput (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 66) :
    leadingRows m f ε s w (heckeInput i)=heckeLeading m f s w i := by
  simp only [leadingRows,assemble,heckeInput_kind]

theorem hecke_inverse_parameter (p m : ℕ) (s : ℂ) :
    (p:ℂ)^((m:ℂ)-s)=1/(p:ℂ)^(s-(m:ℂ)) := by
  rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg,one_div]

/-- The actual Hecke rows match the case-zero Laurent rows without any row
scaling. Only the selected bad-prime sign at 5 is relevant to this block. -/
theorem leadingRows_hecke_complex_case0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (h5 : (Real.sqrt 5:ℂ)*f 5= -1) (w : Fin 210 → ℂ) (i : Fin 66) :
    leadingRows m f ε s w (heckeInput i)=
      selectedRowsV3_0 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w (heckeInput i) := by
  have hX : (2:ℂ)^(s-(m:ℂ))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hY : (3:ℂ)^(s-(m:ℂ))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hZ : (5:ℂ)^(s-(m:ℂ))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [leadingRows_heckeInput]
  unfold heckeLeading
  simp_rw [hecke_inverse_parameter]
  fin_cases i <;>
    norm_num [selectedRowsV3_0,selectedPart0_14,selectedPart0_15,selectedPart0_16,
      selectedPart0_17,selectedPart0_18,selectedPart0_19,selectedPart0_20,
      heckeInput,QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeSpecs,
      completeSum,gridIndex,Finset.sum_range_succ,h5] <;>
    field_simp [hX,hY,hZ] <;> ring

#print axioms heckeInput_kind
#print axioms leadingRows_hecke_complex_case0
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticEntireComparisonV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex FinitenessRamanujanSum QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

/-- Positions of the eleven entire rows, including the cusp-zero row. -/
def entireInput : Fin 11 → Fin 210 := ![4,81,94,111,124,127,128,135,138,142,143]

theorem entireInput_kind : ∀ i : Fin 11, rowKind (entireInput i)=RowKind.entire i := by
  decide

theorem leadingRows_entireInput (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 11) :
    leadingRows m f ε s w (entireInput i)=
      sampleSum (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.entireSpecs i) 0 w := by
  simp only [leadingRows,assemble,entireInput_kind]

/-- The entire rows have no parameters or row-clearing factors. -/
theorem selectedRows_entire_block (X Y Z W a b : ℂ) (w : Fin 210 → ℂ) (i : Fin 11) :
    selectedRowsV3_0 X Y Z W a b w (entireInput i)=
      sampleSum (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.entireSpecs i) 0 w := by
  fin_cases i <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_8,selectedPart0_9,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      entireInput,QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.entireSpecs,
      sampleSum,residues,gridIndex,Finset.sum_filter,Finset.sum_range_succ]

theorem leadingRows_entire_complex (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 11) :
    leadingRows m f ε s w (entireInput i)=
      selectedRowsV3_0 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w (entireInput i) := by
  rw [leadingRows_entireInput,selectedRows_entire_block]

#print axioms entireInput_kind
#print axioms selectedRows_entire_block
#print axioms leadingRows_entire_complex
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTaylorIndicesV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex
/-- The 53 ordinary Taylor rows followed by the 36 shifted Fricke rows,
in the order of the coherent analytic Taylor family. -/
def taylorInput : Fin 89 → Fin 210 :=
  ![82,83,84,85,86,87,88,89,90,91,92,93,
    95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,
    112,113,114,115,116,117,118,119,120,121,122,123,
    125,126,129,130,131,132,133,134,136,137,139,140,141,
    0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,
    25,26,27,28,29,30,31,32,33,34,35,36]

theorem taylorInput_kind : ∀ i : Fin 89, rowKind (taylorInput i)=RowKind.taylor i := by
  intro i
  fin_cases i <;> rfl

theorem leadingRows_taylorInput (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 89) :
    leadingRows m f ε s w (taylorInput i)=taylorLeading m f ε s w i := by
  simp only [leadingRows,assemble,taylorInput_kind]

#print axioms taylorInput_kind
#print axioms leadingRows_taylorInput
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticInputPartitionV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex

/-- The row-kind type has exactly 210 elements, without enumerating witnesses. -/
def rowKindEquiv : RowKind ≃ (Fin 44 ⊕ Fin 89 ⊕ Fin 11 ⊕ Fin 66) where
  toFun
    | .group j => .inl j
    | .taylor j => .inr (.inl j)
    | .entire j => .inr (.inr (.inl j))
    | .hecke j => .inr (.inr (.inr j))
  invFun
    | .inl j => .group j
    | .inr (.inl j) => .taylor j
    | .inr (.inr (.inl j)) => .entire j
    | .inr (.inr (.inr j)) => .hecke j
  left_inv r := by cases r <;> rfl
  right_inv r := by rcases r with j | j | j | j <;> rfl

instance : Fintype RowKind := Fintype.ofEquiv _ rowKindEquiv.symm

def chosenInput : RowKind → Fin 210
  | .group j => groupInput j
  | .taylor j => taylorInput j
  | .entire j => entireInput j
  | .hecke j => heckeInput j

theorem chosenInput_kind (r : RowKind) : rowKind (chosenInput r)=r := by
  cases r with
  | group j => exact groupInput_kind j
  | taylor j => exact taylorInput_kind j
  | entire j => exact entireInput_kind j
  | hecke j => exact heckeInput_kind j

theorem chosenInput_surjective : Function.Surjective chosenInput := by
  apply (Fintype.bijective_iff_injective_and_card chosenInput).mpr _ |>.2
  refine ⟨Function.LeftInverse.injective chosenInput_kind, ?_⟩
  simpa using Fintype.card_congr rowKindEquiv

/-- Injectivity and equal finite cardinalities give the inverse identity. -/
theorem input_inverse (i : Fin 210) :
    (match rowKind i with
      | .group j => groupInput j
      | .taylor j => taylorInput j
      | .entire j => entireInput j
      | .hecke j => heckeInput j) = i := by
  change chosenInput (rowKind i)=i
  obtain ⟨r,rfl⟩ := chosenInput_surjective i
  rw [chosenInput_kind]

theorem input_coverage : ∀ i : Fin 210,
    (∃ j : Fin 44, groupInput j=i) ∨ (∃ j : Fin 89, taylorInput j=i) ∨
      (∃ j : Fin 11, entireInput j=i) ∨ (∃ j : Fin 66, heckeInput j=i) := by
  intro i
  have h := input_inverse i
  cases hi : rowKind i with
  | group j => exact Or.inl ⟨j, by simpa only [hi] using h⟩
  | taylor j => exact Or.inr (Or.inl ⟨j, by simpa only [hi] using h⟩)
  | entire j => exact Or.inr (Or.inr (Or.inl ⟨j, by simpa only [hi] using h⟩))
  | hecke j => exact Or.inr (Or.inr (Or.inr ⟨j, by simpa only [hi] using h⟩))

/-- Four independently verified row blocks suffice for equality of the
full selected row map. This is only the finite indexing partition. -/
theorem rows_ext {u v : Fin 210 → ℂ}
    (hG : ∀ j : Fin 44, u (groupInput j)=v (groupInput j))
    (hT : ∀ j : Fin 89, u (taylorInput j)=v (taylorInput j))
    (hR : ∀ j : Fin 11, u (entireInput j)=v (entireInput j))
    (hH : ∀ j : Fin 66, u (heckeInput j)=v (heckeInput j)) : u=v := by
  funext i
  rcases input_coverage i with ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
  · exact hG j
  · exact hT j
  · exact hR j
  · exact hH j

#print axioms taylorInput_kind
#print axioms input_coverage
#print axioms rows_ext
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTaylorCase1SignV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex FinitenessRamanujanSum QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

def caseOneTaylorSign (i : Fin 89) : ℂ := if 7∣rowQ i then -1 else 1

end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTaylorCaseIndexBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex FinitenessRamanujanSum QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

theorem taylor_case0_part0 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨0+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨0+j.val,by omega⟩ : Fin 89)) (rowT (⟨0+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨0+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨0+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨0+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> ring

#print axioms taylor_case0_part0

theorem taylor_case0_part1 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨10+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨10+j.val,by omega⟩ : Fin 89)) (rowT (⟨10+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨10+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨10+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨10+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> ring

#print axioms taylor_case0_part1

theorem taylor_case0_part2 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨20+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨20+j.val,by omega⟩ : Fin 89)) (rowT (⟨20+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨20+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨20+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨20+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> ring

#print axioms taylor_case0_part2

theorem taylor_case0_part3 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨30+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨30+j.val,by omega⟩ : Fin 89)) (rowT (⟨30+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨30+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨30+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨30+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> ring

#print axioms taylor_case0_part3

theorem taylor_case0_part4 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨40+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨40+j.val,by omega⟩ : Fin 89)) (rowT (⟨40+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨40+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨40+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨40+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> ring

#print axioms taylor_case0_part4

theorem taylor_case0_part5 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨50+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨50+j.val,by omega⟩ : Fin 89)) (rowT (⟨50+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨50+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨50+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨50+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case0_part5

theorem taylor_case0_part6 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨60+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨60+j.val,by omega⟩ : Fin 89)) (rowT (⟨60+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨60+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨60+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨60+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case0_part6

theorem taylor_case0_part7 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨70+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨70+j.val,by omega⟩ : Fin 89)) (rowT (⟨70+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨70+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨70+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨70+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> exact Or.inl True.intro

#print axioms taylor_case0_part7

theorem taylor_case0_part8 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 9) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput (⟨80+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨80+j.val,by omega⟩ : Fin 89)) (rowT (⟨80+j.val,by omega⟩ : Fin 89)) w+
        rateMonomial (⟨80+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨80+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨80+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_0,selectedPart0_0,selectedPart0_1,selectedPart0_2,
      selectedPart0_3,selectedPart0_8,selectedPart0_9,selectedPart0_10,
      selectedPart0_11,selectedPart0_12,selectedPart0_13,selectedPart0_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case0_part8

end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex FinitenessRamanujanSum QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

theorem taylor_case1_part0 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨0+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨0+j.val,by omega⟩ : Fin 89)) (rowT (⟨0+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨0+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨0+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨0+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨0+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part0

theorem taylor_case1_part1 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨10+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨10+j.val,by omega⟩ : Fin 89)) (rowT (⟨10+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨10+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨10+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨10+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨10+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part1

theorem taylor_case1_part2 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨20+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨20+j.val,by omega⟩ : Fin 89)) (rowT (⟨20+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨20+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨20+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨20+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨20+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part2

theorem taylor_case1_part3 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨30+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨30+j.val,by omega⟩ : Fin 89)) (rowT (⟨30+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨30+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨30+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨30+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨30+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part3

theorem taylor_case1_part4 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨40+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨40+j.val,by omega⟩ : Fin 89)) (rowT (⟨40+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨40+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨40+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨40+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨40+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part4

theorem taylor_case1_part5 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨50+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨50+j.val,by omega⟩ : Fin 89)) (rowT (⟨50+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨50+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨50+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨50+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨50+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part5

theorem taylor_case1_part6 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨60+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨60+j.val,by omega⟩ : Fin 89)) (rowT (⟨60+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨60+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨60+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨60+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨60+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part6

theorem taylor_case1_part7 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 10) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨70+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨70+j.val,by omega⟩ : Fin 89)) (rowT (⟨70+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨70+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨70+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨70+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨70+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> exact Or.inl True.intro

#print axioms taylor_case1_part7

theorem taylor_case1_part8 (X Y Z W a b : ℂ)
    (_hX : X≠0) (_hY : Y≠0) (_hZ : Z≠0) (_hW : W≠0)
    (w : Fin 210 → ℂ) (j : Fin 9) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput (⟨80+j.val,by omega⟩ : Fin 89))=
      sampleSum (rowQ (⟨80+j.val,by omega⟩ : Fin 89)) (rowT (⟨80+j.val,by omega⟩ : Fin 89)) w+
        caseOneTaylorSign (⟨80+j.val,by omega⟩ : Fin 89)*rateMonomial (⟨80+j.val,by omega⟩ : Fin 89) X Y Z W*sampleSum (rowQ (⟨80+j.val,by omega⟩ : Fin 89)) (rowPartner (⟨80+j.val,by omega⟩ : Fin 89)) w := by
  fin_cases j <;>
    norm_num [selectedRowsV3_1,selectedPart1_0,selectedPart1_1,selectedPart1_2,
      selectedPart1_3,selectedPart1_8,selectedPart1_9,selectedPart1_10,
      selectedPart1_11,selectedPart1_12,selectedPart1_13,selectedPart1_14,
      taylorInput,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,caseOneTaylorSign,
      rateMonomial,ratePowers_values,sampleSum,residues,gridIndex,
      Finset.sum_filter,Finset.sum_range_succ,zpow_neg,zpow_natCast] <;>
    field_simp [_hX,_hY,_hZ,_hW] <;> first | exact Or.inl True.intro | ring

#print axioms taylor_case1_part8

end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTaylorComparisonV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex FinitenessRamanujanSum QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

/-- Literal comparison of all89 Taylor rows, assembled from bounded checks. -/
theorem selectedRows_taylor_block_case0 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (w : Fin 210 → ℂ) (i : Fin 89) :
    selectedRowsV3_0 X Y Z W a b w (taylorInput i)=
      sampleSum (rowQ i) (rowT i) w+
        rateMonomial i X Y Z W*sampleSum (rowQ i) (rowPartner i) w := by
  by_cases h0 : i.val < 10
  · have h := taylor_case0_part0 X Y Z W a b hX hY hZ hW w ⟨i.val-0,by omega⟩
    have he : (⟨0+(i.val-0),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h1 : i.val < 20
  · have h := taylor_case0_part1 X Y Z W a b hX hY hZ hW w ⟨i.val-10,by omega⟩
    have he : (⟨10+(i.val-10),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h2 : i.val < 30
  · have h := taylor_case0_part2 X Y Z W a b hX hY hZ hW w ⟨i.val-20,by omega⟩
    have he : (⟨20+(i.val-20),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h3 : i.val < 40
  · have h := taylor_case0_part3 X Y Z W a b hX hY hZ hW w ⟨i.val-30,by omega⟩
    have he : (⟨30+(i.val-30),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h4 : i.val < 50
  · have h := taylor_case0_part4 X Y Z W a b hX hY hZ hW w ⟨i.val-40,by omega⟩
    have he : (⟨40+(i.val-40),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h5 : i.val < 60
  · have h := taylor_case0_part5 X Y Z W a b hX hY hZ hW w ⟨i.val-50,by omega⟩
    have he : (⟨50+(i.val-50),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h6 : i.val < 70
  · have h := taylor_case0_part6 X Y Z W a b hX hY hZ hW w ⟨i.val-60,by omega⟩
    have he : (⟨60+(i.val-60),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h7 : i.val < 80
  · have h := taylor_case0_part7 X Y Z W a b hX hY hZ hW w ⟨i.val-70,by omega⟩
    have he : (⟨70+(i.val-70),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  have h := taylor_case0_part8 X Y Z W a b hX hY hZ hW w ⟨i.val-80,by omega⟩
  have he : (⟨80+(i.val-80),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
  simpa only [he] using h

theorem leadingRows_taylor_complex_case0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (w : Fin 210 → ℂ) (i : Fin 89) :
    leadingRows m f ε s w (taylorInput i)=
      selectedRowsV3_0 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w (taylorInput i) := by
  rw [leadingRows_taylorInput,selectedRows_taylor_block_case0]
  · unfold taylorLeading
    rw [rowCoefficient_case0 m f ε s hη h5 h7 i]
    ring
  all_goals exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

#print axioms selectedRows_taylor_block_case0
#print axioms leadingRows_taylor_complex_case0
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticComparisonCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open Complex Matrix FinitenessRamanujanSum QuantitativeArithmeticSmallLevelThirtyFiveFullGrid

/-- The whole original leading row map, with no row factors, equals the
case-zero certificate at the geometric specialization. -/
theorem leadingRows_complex_case0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (w : Fin 210 → ℂ) :
    leadingRows m f ε s w=
      selectedRowsV3_0 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w := by
  apply rows_ext
  · exact leadingRows_group_complex m f ε s w
  · exact leadingRows_taylor_complex_case0 m f ε s hη h5 h7 w
  · exact leadingRows_entire_complex m f ε s w
  · exact leadingRows_hecke_complex_case0 m f ε s h5 w

theorem leadingMatrix_complex_case0 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1) :
    leadingMatrix m f ε s=
      selectedMatrixV3_0 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) := by
  ext i j
  rw [leadingMatrix_apply,selectedMatrixV3_0,LinearMap.toMatrix'_apply,
    selectedLinearV3_0_apply]
  exact congrFun (leadingRows_complex_case0 m f ε s hη h5 h7 (Pi.single j 1)) i

/-- An actual determinant witness for this original root-sign sector.
No nonsingularity or additive-continuation hypothesis is assumed. -/
theorem leadingMatrix_nonsingular_case0 (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1) :
    ∃ s : ℂ, (leadingMatrix m f ε s).det≠0 := by
  obtain ⟨t,ht⟩ := selectedMatrixV3_0_exists_nonsingular
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
  refine ⟨t+(m:ℂ),?_⟩
  rw [leadingMatrix_complex_case0 m f ε _ hη h5 h7]
  simpa only [add_sub_cancel_right] using ht

#print axioms leadingMatrix_complex_case0
#print axioms leadingMatrix_nonsingular_case0

theorem selectedRows_group_same_case1 (X Y Z W a b : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 44) :
    selectedRowsV3_1 X Y Z W a b w (groupInput i)=
      selectedRowsV3_0 X Y Z W a b w (groupInput i) := by
  fin_cases i <;> rfl

theorem selectedRows_entire_same_case1 (X Y Z W a b : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 11) :
    selectedRowsV3_1 X Y Z W a b w (entireInput i)=
      selectedRowsV3_0 X Y Z W a b w (entireInput i) := by
  fin_cases i <;> rfl

theorem selectedRows_hecke_same_case1 (X Y Z W a b : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 66) :
    selectedRowsV3_1 X Y Z W a b w (heckeInput i)=
      selectedRowsV3_0 X Y Z W a b w (heckeInput i) := by
  fin_cases i <;> rfl

/-- Literal comparison of all89 Taylor rows, assembled from bounded checks. -/
theorem selectedRows_taylor_block_case1 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (w : Fin 210 → ℂ) (i : Fin 89) :
    selectedRowsV3_1 X Y Z W a b w (taylorInput i)=
      sampleSum (rowQ i) (rowT i) w+
        caseOneTaylorSign i*rateMonomial i X Y Z W*sampleSum (rowQ i) (rowPartner i) w := by
  by_cases h0 : i.val < 10
  · have h := taylor_case1_part0 X Y Z W a b hX hY hZ hW w ⟨i.val-0,by omega⟩
    have he : (⟨0+(i.val-0),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h1 : i.val < 20
  · have h := taylor_case1_part1 X Y Z W a b hX hY hZ hW w ⟨i.val-10,by omega⟩
    have he : (⟨10+(i.val-10),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h2 : i.val < 30
  · have h := taylor_case1_part2 X Y Z W a b hX hY hZ hW w ⟨i.val-20,by omega⟩
    have he : (⟨20+(i.val-20),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h3 : i.val < 40
  · have h := taylor_case1_part3 X Y Z W a b hX hY hZ hW w ⟨i.val-30,by omega⟩
    have he : (⟨30+(i.val-30),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h4 : i.val < 50
  · have h := taylor_case1_part4 X Y Z W a b hX hY hZ hW w ⟨i.val-40,by omega⟩
    have he : (⟨40+(i.val-40),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h5 : i.val < 60
  · have h := taylor_case1_part5 X Y Z W a b hX hY hZ hW w ⟨i.val-50,by omega⟩
    have he : (⟨50+(i.val-50),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h6 : i.val < 70
  · have h := taylor_case1_part6 X Y Z W a b hX hY hZ hW w ⟨i.val-60,by omega⟩
    have he : (⟨60+(i.val-60),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  by_cases h7 : i.val < 80
  · have h := taylor_case1_part7 X Y Z W a b hX hY hZ hW w ⟨i.val-70,by omega⟩
    have he : (⟨70+(i.val-70),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
    simpa only [he] using h
  have h := taylor_case1_part8 X Y Z W a b hX hY hZ hW w ⟨i.val-80,by omega⟩
  have he : (⟨80+(i.val-80),by omega⟩ : Fin 89)=i := Fin.ext (by dsimp only; omega)
  simpa only [he] using h

theorem rowCoefficient_case1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f=1)
    (i : Fin 89) :
    rowCoefficient (2*m) f ε i 0 s=
      -caseOneTaylorSign i*rateMonomial i
        ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ))) := by
  rw [rowCoefficient_complex,hη,h5,h7]
  by_cases hi : 7∣rowQ i <;> simp [localRoot,caseOneTaylorSign,hi]

theorem leadingRows_taylor_complex_case1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f=1)
    (w : Fin 210 → ℂ) (i : Fin 89) :
    leadingRows m f ε s w (taylorInput i)=
      selectedRowsV3_1 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w (taylorInput i) := by
  rw [leadingRows_taylorInput,selectedRows_taylor_block_case1]
  · unfold taylorLeading
    rw [rowCoefficient_case1 m f ε s hη h5 h7 i]
    ring
  all_goals exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem leadingRows_complex_case1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f=1)
    (w : Fin 210 → ℂ) :
    leadingRows m f ε s w=
      selectedRowsV3_1 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w := by
  apply rows_ext
  · intro i
    rw [selectedRows_group_same_case1]
    exact leadingRows_group_complex m f ε s w i
  · exact leadingRows_taylor_complex_case1 m f ε s hη h5 h7 w
  · intro i
    rw [selectedRows_entire_same_case1]
    exact leadingRows_entire_complex m f ε s w i
  · intro i
    rw [selectedRows_hecke_same_case1]
    exact leadingRows_hecke_complex_case0 m f ε s h5 w i

theorem leadingMatrix_complex_case1 (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f=1) :
    leadingMatrix m f ε s=
      selectedMatrixV3_1 ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) := by
  ext i j
  rw [leadingMatrix_apply,selectedMatrixV3_1,LinearMap.toMatrix'_apply,
    selectedLinearV3_1_apply]
  exact congrFun (leadingRows_complex_case1 m f ε s hη h5 h7 (Pi.single j 1)) i

theorem leadingMatrix_nonsingular_case1 (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phaseRoot m ε= -1) (h5 : badFive f= -1) (h7 : badSeven f=1) :
    ∃ s : ℂ, (leadingMatrix m f ε s).det≠0 := by
  obtain ⟨t,ht⟩ := selectedMatrixV3_1_exists_nonsingular
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
  refine ⟨t+(m:ℂ),?_⟩
  rw [leadingMatrix_complex_case1 m f ε _ hη h5 h7]
  simpa only [add_sub_cancel_right] using ht

#print axioms selectedRows_taylor_block_case1
#print axioms leadingMatrix_complex_case1
#print axioms leadingMatrix_nonsingular_case1

end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTheoryV4 -/
section
/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticSymbolicV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

theorem selected_hecke_primes : ∀ i : Fin 66,
    (heckeSpecs i).1=2 ∨ (heckeSpecs i).1=3 ∨ (heckeSpecs i).1=5 := by decide

def symbolicHecke (u X Y Z a b : ℂ) (w : Fin 210 → ℂ) (i : Fin 66) : ℂ :=
  let p := (heckeSpecs i).1
  let j := (heckeSpecs i).2
  let e := if p=2 then a else if p=3 then b else u
  let x := if p=2 then X else if p=3 then Y else Z
  completeSum p j w-(e/x)*w (gridIndex ((p:ℤ)*j))+
    if p∣35 then 0 else (1/x)^2*w (gridIndex ((p:ℤ)^2*j))

/-- The original leading rows with the geometric parameters made explicit.
The three root parameters are independent scalars in this algebraic definition. -/
def symbolicRows (η u v X Y Z W a b : ℂ) (w : Fin 210 → ℂ) : Fin 210 → ℂ :=
  assemble
    (fun i => w (gridIndex (groupSource i))-
      groupRateMonomial i X Y Z W*w (gridIndex (groupPartner i)))
    (fun i => sampleSum (rowQ i) (rowT i) w-
      (η*localRoot u v (rowQ i)*rateMonomial i X Y Z W)*
        sampleSum (rowQ i) (rowPartner i) w)
    (fun i => sampleSum (entireSpecs i) 0 w)
    (symbolicHecke u X Y Z a b w)

theorem original_hecke_symbolic (m : ℕ) (f : ℕ→ℂ) (s : ℂ)
    (w : Fin 210 → ℂ) (i : Fin 66) :
    heckeLeading m f s w i=
      symbolicHecke (badFive f)
        ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ))) ((5:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w i := by
  have hinv (p : ℂ) : p^((m:ℂ)-s)=1/p^(s-(m:ℂ)) := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg,one_div]
  rcases selected_hecke_primes i with hp|hp|hp <;>
    simp [heckeLeading,symbolicHecke,hp,hinv,badFive,div_eq_mul_inv,mul_assoc]

theorem leadingRows_symbolic (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 210 → ℂ) :
    leadingRows m f ε s w=
      symbolicRows (phaseRoot m ε) (badFive f) (badSeven f)
        ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) w := by
  funext i
  cases hi : rowKind i with
  | group j =>
    simp only [leadingRows,symbolicRows,assemble,hi,groupLeading,groupCoefficient_complex]
  | taylor j =>
    simp only [leadingRows,symbolicRows,assemble,hi,taylorLeading,rowCoefficient_complex]
  | entire j => simp only [leadingRows,symbolicRows,assemble,hi]
  | hecke j =>
    simpa only [leadingRows,symbolicRows,assemble,hi] using original_hecke_symbolic m f s w j

/-- Flipping Z simultaneously flips the global phase and the local sign at5. -/
theorem symbolicRows_neg_five (η u v X Y Z W a b : ℂ) (w : Fin 210 → ℂ) :
    symbolicRows η u v X Y (-Z) W a b w=
      symbolicRows (-η) (-u) v X Y Z W a b w := by
  funext i
  cases hi : rowKind i with
  | group j =>
    simp only [symbolicRows,assemble,hi]
    rw [groupRateMonomial_bad_independent j X Y (-Z) W Z W]
  | taylor j =>
    simp only [symbolicRows,assemble,hi,rateMonomial_neg_five]
    by_cases h5 : 5∣rowQ j <;> by_cases h7 : 7∣rowQ j <;>
      simp [localRoot,h5,h7]
  | entire j => simp only [symbolicRows,assemble,hi]
  | hecke j =>
    simp only [symbolicRows,assemble,hi]
    rcases selected_hecke_primes j with hp|hp|hp <;>
      simp [symbolicHecke,hp,div_neg,neg_div]

/-- Flipping W simultaneously flips the global phase and the local sign at7. -/
theorem symbolicRows_neg_seven (η u v X Y Z W a b : ℂ) (w : Fin 210 → ℂ) :
    symbolicRows η u v X Y Z (-W) a b w=
      symbolicRows (-η) u (-v) X Y Z W a b w := by
  funext i
  cases hi : rowKind i with
  | group j =>
    simp only [symbolicRows,assemble,hi]
    rw [groupRateMonomial_bad_independent j X Y Z (-W) Z W]
  | taylor j =>
    simp only [symbolicRows,assemble,hi,rateMonomial_neg_seven]
    by_cases h5 : 5∣rowQ j <;> by_cases h7 : 7∣rowQ j <;>
      simp [localRoot,h5,h7]
  | entire j => simp only [symbolicRows,assemble,hi]
  | hecke j => simp only [symbolicRows,assemble,hi]

#print axioms leadingRows_symbolic
#print axioms symbolicRows_neg_five
#print axioms symbolicRows_neg_seven
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticSymbolicComparisonV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

theorem symbolicHecke_case0 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 210 → ℂ) (i : Fin 66) :
    symbolicHecke (-1) X Y Z a b w i=
      selectedRowsV3_0 X Y Z W a b w (heckeInput i) := by
  fin_cases i <;>
    norm_num [symbolicHecke,selectedRowsV3_0,selectedPart0_14,selectedPart0_15,
      selectedPart0_16,selectedPart0_17,selectedPart0_18,selectedPart0_19,
      selectedPart0_20,heckeInput,heckeSpecs,completeSum,gridIndex,
      Finset.sum_range_succ] <;> field_simp [hX,hY,hZ] <;> ring

theorem symbolicRows_case0 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (w : Fin 210 → ℂ) :
    symbolicRows (-1) (-1) (-1) X Y Z W a b w=selectedRowsV3_0 X Y Z W a b w := by
  apply rows_ext
  · intro i
    simp only [symbolicRows,assemble,groupInput_kind]
    exact (selectedRows_group_block X Y Z W a b hX hY w i).symm
  · intro i
    rw [selectedRows_taylor_block_case0 X Y Z W a b hX hY hZ hW]
    simp [symbolicRows,assemble,taylorInput_kind,localRoot]
  · intro i
    simp only [symbolicRows,assemble,entireInput_kind]
    exact (selectedRows_entire_block X Y Z W a b w i).symm
  · intro i
    simpa only [symbolicRows,assemble,heckeInput_kind] using
      symbolicHecke_case0 X Y Z W a b hX hY hZ w i

theorem symbolicRows_case1 (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (w : Fin 210 → ℂ) :
    symbolicRows (-1) (-1) 1 X Y Z W a b w=selectedRowsV3_1 X Y Z W a b w := by
  apply rows_ext
  · intro i
    rw [selectedRows_group_same_case1]
    simp only [symbolicRows,assemble,groupInput_kind]
    exact (selectedRows_group_block X Y Z W a b hX hY w i).symm
  · intro i
    rw [selectedRows_taylor_block_case1 X Y Z W a b hX hY hZ hW]
    by_cases hi : 7∣rowQ i <;>
      simp [symbolicRows,assemble,taylorInput_kind,localRoot,caseOneTaylorSign,hi,sub_eq_add_neg]
  · intro i
    rw [selectedRows_entire_same_case1]
    simp only [symbolicRows,assemble,entireInput_kind]
    exact (selectedRows_entire_block X Y Z W a b w i).symm
  · intro i
    rw [selectedRows_hecke_same_case1]
    simpa only [symbolicRows,assemble,heckeInput_kind] using
      symbolicHecke_case0 X Y Z W a b hX hY hZ w i

def caseSigns : Fin 8 → ℂ × ℂ × ℂ :=
  ![(-1,-1,-1),(-1,-1,1),(-1,1,-1),(-1,1,1),
    (1,-1,-1),(1,-1,1),(1,1,-1),(1,1,1)]

/-- The six additional sectors follow from the two base sectors and the
actual rate-parity identities; there is no repeated 210-row expansion. -/
theorem symbolicRows_allCases (c : Fin 8) (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (w : Fin 210 → ℂ) :
    symbolicRows (caseSigns c).1 (caseSigns c).2.1 (caseSigns c).2.2
      X Y Z W a b w=selectedRowsCase c X Y Z W a b w := by
  fin_cases c
  · exact symbolicRows_case0 X Y Z W a b hX hY hZ hW w
  · exact symbolicRows_case1 X Y Z W a b hX hY hZ hW w
  · change symbolicRows (-1) 1 (-1) X Y Z W a b w=selectedRowsV3_2 X Y Z W a b w
    rw [rows2_sign_change X Y Z W a b hX hY hZ hW w]
    have hh := symbolicRows_case1 X Y (-Z) (-W) a b hX hY
      (neg_ne_zero.mpr hZ) (neg_ne_zero.mpr hW) w
    rw [symbolicRows_neg_seven,symbolicRows_neg_five] at hh
    simpa only [neg_neg] using hh
  · change symbolicRows (-1) 1 1 X Y Z W a b w=selectedRowsV3_3 X Y Z W a b w
    rw [rows3_sign_change X Y Z W a b hX hY hZ hW w]
    have hh := symbolicRows_case0 X Y (-Z) (-W) a b hX hY
      (neg_ne_zero.mpr hZ) (neg_ne_zero.mpr hW) w
    rw [symbolicRows_neg_seven,symbolicRows_neg_five] at hh
    simpa only [neg_neg] using hh
  · change symbolicRows 1 (-1) (-1) X Y Z W a b w=selectedRowsV3_4 X Y Z W a b w
    rw [rows4_sign_change X Y Z W a b hX hY hZ hW w]
    have hh := symbolicRows_case1 X Y Z (-W) a b hX hY hZ (neg_ne_zero.mpr hW) w
    rw [symbolicRows_neg_seven] at hh
    simpa only [neg_neg] using hh
  · change symbolicRows 1 (-1) 1 X Y Z W a b w=selectedRowsV3_5 X Y Z W a b w
    rw [rows5_sign_change X Y Z W a b hX hY hZ hW w]
    have hh := symbolicRows_case0 X Y Z (-W) a b hX hY hZ (neg_ne_zero.mpr hW) w
    rw [symbolicRows_neg_seven] at hh
    simpa only [neg_neg] using hh
  · change symbolicRows 1 1 (-1) X Y Z W a b w=selectedRowsV3_6 X Y Z W a b w
    rw [rows6_sign_change X Y Z W a b hX hY hZ hW w]
    have hh := symbolicRows_case0 X Y (-Z) W a b hX hY (neg_ne_zero.mpr hZ) hW w
    rw [symbolicRows_neg_five] at hh
    simpa only [neg_neg] using hh
  · change symbolicRows 1 1 1 X Y Z W a b w=selectedRowsV3_7 X Y Z W a b w
    rw [rows7_sign_change X Y Z W a b hX hY hZ hW w]
    have hh := symbolicRows_case1 X Y (-Z) W a b hX hY (neg_ne_zero.mpr hZ) hW w
    rw [symbolicRows_neg_five] at hh
    simpa only [neg_neg] using hh

#print axioms symbolicRows_case0
#print axioms symbolicRows_case1
#print axioms symbolicRows_allCases
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticOriginalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Set Matrix SmallLevelTaylor SmallLevelAdditive

/-- The actual closed 210-grid Taylor system. Every coordinate is the original
additive Mellin transform; no continuation assumption is used. -/
theorem original_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ, ∃ error : ℕ → ℂ → Fin 210 → ℂ,
      (∀ i : Fin 210, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 210, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => error M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        leadingMatrix m f ε s *ᵥ gridVector (2*m) f s=
          error M s+∑ n∈Finset.range M,
            shiftMatrix m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  obtain ⟨BG,errG,hG⟩ := original_group_system hm hf
  obtain ⟨ε,hε,BT,hT⟩ :=
    QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.original_taylor_system
      (by exact even_two_mul m) hf
  obtain ⟨hRE,BR,hR⟩ :=
    QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.original_entire_rows
      (by omega : 0<2*m) hf
  obtain ⟨BH,hH⟩ :=
    QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.original_selected_hecke_rows hm hf
  obtain ⟨BF,hF⟩ := SmallLevelAdditive.original_common_halfplane hf
  let B : ℝ := max BG (max BT (max BR (max BH BF)))
  have hBG : BG≤B := le_max_left _ _
  have hBT : BT≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hBR : BR≤B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBH : BH≤B := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hBF : BF≤B := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  let error : ℕ → ℂ → Fin 210 → ℂ := fun M s =>
    assemble (fun i => errG i M s)
      (fun i => QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowError (2*m) f ε i M s)
      (fun i => ramanujanEntire 35 (2*m) f
        (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.entireSpecs i) s) 0
  refine ⟨ε,hε,B,error,?_,?_,?_⟩
  · intro i s hs
    exact (hF (((i:ℕ):ℝ)/210) s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have hg (j : Fin 44) : AnalyticAt ℂ (errG j M) s := by
      apply (hG j M).1 s
      change BG-((M:ℝ)+1)<s.re
      linarith
    have ht (j : Fin 89) : AnalyticAt ℂ
        (QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.rowError (2*m) f ε j M) s := by
      apply (hT j M).1 s
      change BT-((M:ℝ)+1)<s.re
      linarith
    cases hi : rowKind i with
    | group j => simpa only [error,assemble,hi] using hg j
    | taylor j => simpa only [error,assemble,hi] using ht j
    | entire j => simpa only [error,assemble,hi] using hRE j s
    | hecke j => simpa only [error,assemble,hi,Pi.zero_apply] using (analyticAt_const (v := (0:ℂ)) : AnalyticAt ℂ (fun _ : ℂ => (0:ℂ)) s)
  · intro M s hs
    rw [leadingMatrix_mulVec]
    simp_rw [shiftMatrix_mulVec]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    cases hi : rowKind i with
    | group j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,groupLeading] using
        (hG j M).2 s (lt_of_le_of_lt hBG hs)
    | taylor j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,taylorLeading,sampleSum_grid] using
        (hT j M).2 s (lt_of_le_of_lt hBT hs)
    | entire j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,Finset.sum_const_zero,
        add_zero,sampleSum_grid] using (hR j s (lt_of_le_of_lt hBR hs)).symm
    | hecke j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,Finset.sum_const_zero,
        add_zero,heckeLeading_grid] using hH j s (lt_of_le_of_lt hBH hs)

#print axioms original_matrix_system
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticAllCasesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix QuantitativeArithmeticSmallLevelThirtyFiveFullGrid
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

theorem caseSigns_cover {η u v : ℂ}
    (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ∃ c : Fin 8, η=(caseSigns c).1 ∧ u=(caseSigns c).2.1 ∧ v=(caseSigns c).2.2 := by
  rcases hη with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · exact ⟨7,by simp [caseSigns]⟩
  · exact ⟨6,by simp [caseSigns]⟩
  · exact ⟨5,by simp [caseSigns]⟩
  · exact ⟨4,by simp [caseSigns]⟩
  · exact ⟨3,by simp [caseSigns]⟩
  · exact ⟨2,by simp [caseSigns]⟩
  · exact ⟨1,by simp [caseSigns]⟩
  · exact ⟨0,by simp [caseSigns]⟩

/-- Exact equality with the matching algebraic case, at every complex point. -/
theorem leadingMatrix_complex_case (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (c : Fin 8)
    (hη : phaseRoot m ε=(caseSigns c).1)
    (h5 : badFive f=(caseSigns c).2.1) (h7 : badSeven f=(caseSigns c).2.2) :
    leadingMatrix m f ε s=
      selectedMatrixCase c ((2:ℂ)^(s-(m:ℂ))) ((3:ℂ)^(s-(m:ℂ)))
        ((5:ℂ)^(s-(m:ℂ))) ((7:ℂ)^(s-(m:ℂ)))
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) := by
  have hp (p : ℂ) (hp : p≠0) : p^(s-(m:ℂ))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp)
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  rw [leadingMatrix_mulVec,selectedMatrixCase_mulVec c _ _ _ _ _ _
    (hp 2 (by norm_num)) (hp 3 (by norm_num)) (hp 5 (by norm_num)) (hp 7 (by norm_num)),
    leadingRows_symbolic,hη,h5,h7]
  exact symbolicRows_allCases c _ _ _ _ _ _
    (hp 2 (by norm_num)) (hp 3 (by norm_num)) (hp 5 (by norm_num)) (hp 7 (by norm_num)) w

/-- The determinant witness for the actual 210-grid leading matrix follows
from original Euler data and the checked algebraic sign cases. -/
theorem original_leadingMatrix_nonsingular {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) :
    ∃ s : ℂ, (leadingMatrix m f ε s).det≠0 := by
  obtain ⟨c,hη,h5,h7⟩ := caseSigns_cover
    (phaseRoot_sign m hε) (badFive_sign hf.toEulerData) (badSeven_sign hf.toEulerData)
  obtain ⟨s,hs⟩ := selectedMatrixCase_shifted_exists_nonsingular c
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (m:ℂ)
  refine ⟨s,?_⟩
  rw [leadingMatrix_complex_case m f ε s c hη h5 h7]
  exact hs

#print axioms caseSigns_cover
#print axioms leadingMatrix_complex_case
#print axioms original_leadingMatrix_nonsingular
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix

/-- Meromorphic continuation of all 210 original additive transforms.
Every source row and determinant premise comes from the original solution. -/
theorem original_grid_continuation {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ B : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=gridVector (2*m) f z := by
  obtain ⟨ε,hε,B,error,hF,hE,hrow⟩ := original_matrix_system hm hf
  refine ⟨B,?_⟩
  apply SmallLevelContinuation.closed_system_continuation B
    (gridVector (2*m) f) (leadingMatrix m f ε)
    (shiftMatrix m f ε) error hF
    (leadingMatrix_analytic m f ε)
    (original_leadingMatrix_nonsingular hf ε hε)
    (shiftMatrix_analytic m f ε) hE
  intro n z hz i
  simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using
    congrFun (hrow n z hz) i

#print axioms original_grid_continuation
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullTaylorGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix Filter Set SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct
open scoped Topology

def fullTaylorCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t : ℤ) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (Nat.lcm 35 (q^2)) ((t:ℝ)/210)
    (root 35 f q*ε*I^k) n s

def fullTaylorError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t : ℤ) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f q) k)
    (Nat.lcm 35 (q^2)) ((t:ℝ)/210) (root 35 f q*ε*I^k) (M+1)) s

theorem fullTaylorCoefficient_analytic (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    {q : ℕ} (hq : 0<q) {t : ℤ} (ht : t≠0) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fullTaylorCoefficient k f ε q t n) s := by
  apply taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<35) (pow_pos hq 2)
  · exact div_ne_zero (by exact_mod_cast ht) (by norm_num)

theorem sampleSum_meromorphic (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicAt (fun w => G w i) z)
    (q : ℕ) (t : ℤ) (s : ℂ) :
    MeromorphicAt (fun z => sampleSum q t (G z)) s := by
  apply MeromorphicAt.fun_sum
  intro j _
  exact hG (gridIndex (t+(j:ℤ)*(210/q:ℕ))) s

/-- Every closed Ramanujan Taylor row continues on the actual 210-grid,
not just the 89 rows selected to prove continuation. One original Fricke
sign works simultaneously for the whole family. -/
theorem original_full_taylor_germs {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ q : ℕ, 0<q → q∣210 →
      ∀ t d : ℤ, t≠0 → (Nat.lcm 35 (q^2):ℤ)*d=(210:ℤ)^2 → t∣d →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ (fullTaylorError (2*m) f ε q t M)
          {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ x : ℂ, B-((M:ℝ)+1)<x.re →
          (fun z => sampleSum q t (G z)-
            fullTaylorCoefficient (2*m) f ε q t 0 z*sampleSum q (-(d/t)) (G z))
            =ᶠ[𝓝[≠] x]
          (fun z => fullTaylorError (2*m) f ε q t M z+
            ∑ n∈Finset.range M, fullTaylorCoefficient (2*m) f ε q t (n+1) z*
              sampleSum q (-(d/t)) (G (z+((n:ℂ)+1)))) := by
  obtain ⟨ε,hε,hrows⟩ := original_closed_grid_taylor_rows
    (by decide : 0<35) (even_two_mul m) hf
  refine ⟨ε,hε,?_⟩
  intro q hq hqQ t d ht hd htd
  obtain ⟨B,hB⟩ := hrows 210 q (by decide) hq hqQ t d ht hd htd
  refine ⟨B,?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro x hx
  have hS (q : ℕ) (t : ℤ) (s : ℂ) :=
    sampleSum_meromorphic G (fun i z => (hG i z).meromorphicAt) q t s
  have hFG (q : ℕ) (t : ℤ) (z : ℂ) (hz : BG<z.re) :
      sampleSum q t (G z)=gridSum (2*m) f 210 q t z := by
    rw [hGF z hz,sampleSum_grid]
  apply SmallLevelContinuation.halfplane_germ_identity
    (B-((M:ℝ)+1)) (max B BG) _ _ _ x hx
  · intro z _
    exact (hS q t z).sub ((fullTaylorCoefficient_analytic (2*m) f ε hq ht 0 z).meromorphicAt.mul
      (hS q (-(d/t)) z))
  · intro z hz
    apply ((hB M).1 z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro n _
    exact (fullTaylorCoefficient_analytic (2*m) f ε hq ht (n+1) z).meromorphicAt.mul
      ((hS q (-(d/t)) (z+((n:ℂ)+1))).comp_analyticAt
        (g:=fun w : ℂ => w+((n:ℂ)+1)) (by fun_prop))
  · intro z hz
    have hzB : B<z.re := lt_of_le_of_lt (le_max_left B BG) hz
    have hzG : BG<z.re := lt_of_le_of_lt (le_max_right B BG) hz
    dsimp only
    rw [hFG q t z hzG,hFG q (-(d/t)) z hzG]
    have he := (hB M).2 z hzB
    change gridSum (2*m) f 210 q t z-
      fullTaylorCoefficient (2*m) f ε q t 0 z*gridSum (2*m) f 210 q (-(d/t)) z=
      fullTaylorError (2*m) f ε q t M z+
        ∑ n∈Finset.range M, fullTaylorCoefficient (2*m) f ε q t (n+1) z*
          gridSum (2*m) f 210 q (-(d/t)) (z+((n:ℂ)+1)) at he
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have hs : BG<(z+((n:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [hFG q (-(d/t)) _ hs]

#print axioms fullTaylorCoefficient_analytic
#print axioms sampleSum_meromorphic
#print axioms original_full_taylor_germs
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveCoherentTaylorGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix Filter Set SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct
open scoped Topology

/-- Every closed Ramanujan Taylor row continues on the actual 210-grid,
not just the 89 rows selected to prove continuation. One original Fricke
sign works simultaneously for the whole family. -/
theorem full_taylor_germs_of_law {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) :
    ∀ q : ℕ, 0<q → q∣210 →
      ∀ t d : ℤ, t≠0 → (Nat.lcm 35 (q^2):ℤ)*d=(210:ℤ)^2 → t∣d →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ (fullTaylorError (2*m) f ε q t M)
          {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ x : ℂ, B-((M:ℝ)+1)<x.re →
          (fun z => sampleSum q t (G z)-
            fullTaylorCoefficient (2*m) f ε q t 0 z*sampleSum q (-(d/t)) (G z))
            =ᶠ[𝓝[≠] x]
          (fun z => fullTaylorError (2*m) f ε q t M z+
            ∑ n∈Finset.range M, fullTaylorCoefficient (2*m) f ε q t (n+1) z*
              sampleSum q (-(d/t)) (G (z+((n:ℂ)+1)))) := by
  have hrows := QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
    (by decide : 0<35) (even_two_mul m) hf ε hlaw
  intro q hq hqQ t d ht hd htd
  obtain ⟨B,hB⟩ := hrows 210 q (by decide) hq hqQ t d ht hd htd
  refine ⟨B,?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro x hx
  have hS (q : ℕ) (t : ℤ) (s : ℂ) :=
    sampleSum_meromorphic G (fun i z => (hG i z).meromorphicAt) q t s
  have hFG (q : ℕ) (t : ℤ) (z : ℂ) (hz : BG<z.re) :
      sampleSum q t (G z)=gridSum (2*m) f 210 q t z := by
    rw [hGF z hz,sampleSum_grid]
  apply SmallLevelContinuation.halfplane_germ_identity
    (B-((M:ℝ)+1)) (max B BG) _ _ _ x hx
  · intro z _
    exact (hS q t z).sub ((fullTaylorCoefficient_analytic (2*m) f ε hq ht 0 z).meromorphicAt.mul
      (hS q (-(d/t)) z))
  · intro z hz
    apply ((hB M).1 z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro n _
    exact (fullTaylorCoefficient_analytic (2*m) f ε hq ht (n+1) z).meromorphicAt.mul
      ((hS q (-(d/t)) (z+((n:ℂ)+1))).comp_analyticAt
        (g:=fun w : ℂ => w+((n:ℂ)+1)) (by fun_prop))
  · intro z hz
    have hzB : B<z.re := lt_of_le_of_lt (le_max_left B BG) hz
    have hzG : BG<z.re := lt_of_le_of_lt (le_max_right B BG) hz
    dsimp only
    rw [hFG q t z hzG,hFG q (-(d/t)) z hzG]
    have he := (hB M).2 z hzB
    change gridSum (2*m) f 210 q t z-
      fullTaylorCoefficient (2*m) f ε q t 0 z*gridSum (2*m) f 210 q (-(d/t)) z=
      fullTaylorError (2*m) f ε q t M z+
        ∑ n∈Finset.range M, fullTaylorCoefficient (2*m) f ε q t (n+1) z*
          gridSum (2*m) f 210 q (-(d/t)) (z+((n:ℂ)+1)) at he
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have hs : BG<(z+((n:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [hFG q (-(d/t)) _ hs]

#print axioms full_taylor_germs_of_law
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveFullHeckeGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open Complex Matrix Filter Set SmallLevelTaylor SmallLevelAdditive
open scoped Topology

def fullHeckeRow (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (j : ℤ)
    (s : ℂ) (v : Fin 210 → ℂ) : ℂ :=
  completeSum p j v-((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*v (gridIndex ((p:ℤ)*j))+
    if p∣35 then 0 else ((p:ℂ)^((m:ℂ)-s))^2*v (gridIndex ((p:ℤ)^2*j))

theorem fullHeckeRow_grid (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (j : ℤ) (s : ℂ) :
    fullHeckeRow m f p j s (gridVector (2*m) f s)=
      QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeLeading m f p j s := by
  simp only [fullHeckeRow,completeSum,gridVector_index,
    QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.heckeLeading]

theorem fullHeckeRow_meromorphic (m : ℕ) (f : ℕ → ℂ)
    {p : ℕ} (hp : 0<p) (j : ℤ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicAt (fun w => G w i) z) (s : ℂ) :
    MeromorphicAt (fun z => fullHeckeRow m f p j z (G z)) s := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  have hP : AnalyticAt ℂ (fun z : ℂ => (p:ℂ)^((m:ℂ)-z)) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hp0]
    fun_prop
  have hsum : MeromorphicAt (fun z => completeSum p j (G z)) s := by
    apply MeromorphicAt.fun_sum
    intro a _
    exact hG _ s
  unfold fullHeckeRow
  apply (hsum.sub ((analyticAt_const.mul hP).meromorphicAt.mul (hG _ s))).add
  by_cases hb : p∣35
  · simpa only [ite_eq_left hb] using (analyticAt_const (v := (0:ℂ))).meromorphicAt
  · simpa only [ite_eq_right hb] using (hP.fun_pow 2).meromorphicAt.fun_mul (hG _ s)

/-- Every good or bad prime row on the closed grid holds after continuation,
for every numerator. No prime eigenvalue is assumed nonzero. -/
theorem original_full_hecke_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    {p : ℕ} (hp : p.Prime) (hpQ : p∣210) (j : ℤ) (x : ℂ) :
    (fun z => fullHeckeRow m f p j z (G z))=ᶠ[𝓝[≠] x] (fun _ => 0) := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.original_hecke_grid
    hm hf hp hpQ
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact fullHeckeRow_meromorphic m f hp.pos j G (fun i w => (hG i w).meromorphicAt) z
  · intro z _
    exact analyticAt_const.meromorphicAt
  · intro z hz
    dsimp only
    rw [hGF z (lt_of_le_of_lt (le_max_right B BG) hz),fullHeckeRow_grid]
    exact hB j z (lt_of_le_of_lt (le_max_left B BG) hz)

/-- Every primitive Ramanujan sum on the grid is an actual entire Mellin
transform as a germ, not merely the eleven rows used in the selected matrix. -/
theorem original_full_entire_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    {q : ℕ} (hq : 0<q) (hqQ : q∣210) :
    (∀ x : ℂ, AnalyticAt ℂ (ramanujanEntire 35 (2*m) f q) x) ∧
      ∀ x : ℂ, (fun z => sampleSum q 0 (G z))=ᶠ[𝓝[≠] x]
        ramanujanEntire 35 (2*m) f q := by
  obtain ⟨hE,B,hB⟩ := original_ramanujan_entire (by decide : 0<35) (by omega : 0<2*m) hf hq
  refine ⟨hE,?_⟩
  intro x
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact sampleSum_meromorphic G (fun i w => (hG i w).meromorphicAt) q 0 z
  · intro z _
    exact (hE z).meromorphicAt
  · intro z hz
    dsimp only
    rw [hGF z (lt_of_le_of_lt (le_max_right B BG) hz),sampleSum_grid,
      hB z (lt_of_le_of_lt (le_max_left B BG) hz)]
    have he := ramanujanAdditive_grid (2*m) f (by decide : 0<210) hq hqQ 0 z
    simpa only [Int.cast_zero,zero_div,gridSum] using he.symm

#print axioms fullHeckeRow_grid
#print axioms fullHeckeRow_meromorphic
#print axioms original_full_hecke_germs
#print axioms original_full_entire_germs
end QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
end
end
end
