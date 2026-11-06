module

public import QuantitativeArithmeticSmallLevelNineteenGridGroupRowsV1
public import SmallLevelAdditiveTheoryV4
public import SmallLevelTaylorRowCoefficientsV1
public import SmallLevelTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelNineteenGridAnalytic. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelNineteenGridSelectedGroupV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open Complex Set SmallLevelAdditive FinitenessOriginalFourier
def gridIndex (t : ℤ) : Fin 114 :=
  ⟨(t%114).toNat,by have h := Int.emod_lt_of_pos t (by decide : (0:ℤ)<114); omega⟩

def gridVector (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : Fin 114 → ℂ :=
  fun j => grid k f 114 (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ → ℂ) (t : ℤ) (s : ℂ) :
    gridVector k f s (gridIndex t)=grid k f 114 t s := by
  have he : ((gridIndex t).val:ℤ)=t%114 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  unfold gridVector
  rw [he]
  exact grid_mod k f (by decide : 0<114) t s

def gA (i : Fin 13) : ℝ := (QuantitativeArithmeticSmallLevelNineteen.continuationMatrix i).val 0 0
def gB (i : Fin 13) : ℝ := (QuantitativeArithmeticSmallLevelNineteen.continuationMatrix i).val 0 1
def gC (i : Fin 13) : ℝ := (QuantitativeArithmeticSmallLevelNineteen.continuationMatrix i).val 1 0
def gD (i : Fin 13) : ℝ := (QuantitativeArithmeticSmallLevelNineteen.continuationMatrix i).val 1 1

theorem original_group_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f)
    (i : Fin 13) (j : ℝ) (hj : gC i*j+gD i≠0) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform (fullCoefficients f (2*m)) j s-
          (((gC i*j+gD i)^2:ℝ):ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (I*((gC i*(gC i*j+gD i):ℝ):ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              transform (fullCoefficients f (2*m))
                ((gA i*j+gB i)/(gC i*j+gD i)) (s+(n:ℂ))) = error M s := by
  exact QuantitativeArithmeticSmallLevelNineteen.original_continuation_matrix_rows m hf i j hj

def groupSpecs : Fin 45 → (Fin 13 × ℤ × ℤ) :=
  ![(4,0,-57),(4,6,-56),(4,24,-55),(0,108,-2),(11,6,60),(9,18,127),(9,36,128),(9,42,129),(9,45,130),(9,48,132),(9,50,135),(9,51,138),(9,52,144),(9,53,162),(9,55,90),(9,56,108),(9,58,117),(9,63,122),(9,66,123),(9,72,124),(9,90,125),(12,59,-125),(12,60,-126),(10,2,58),(10,5,52),(10,6,54),(10,8,55),(6,7,-15),(6,9,-13),(5,102,-6),(5,103,-8),(5,104,-7),(8,4,-102),(8,7,-156),(8,9,-132),(8,15,-124),(8,18,-123),(1,110,12),(3,61,-48),(3,62,-30),(3,64,-21),(3,69,-16),(3,78,-14),(2,2,1),(7,84,-119)]

def groupMatrix (i : Fin 45) : Fin 13 := (groupSpecs i).1
def groupSource (i : Fin 45) : ℤ := (groupSpecs i).2.1
def groupPartner (i : Fin 45) : ℤ := (groupSpecs i).2.2
def groupCenter (i : Fin 45) : ℝ := (groupSource i:ℝ)/114

theorem group_denominator (i : Fin 45) :
    gC (groupMatrix i)*groupCenter i+gD (groupMatrix i)≠0 := by
  fin_cases i <;> norm_num [groupMatrix,groupCenter,groupSource,groupSpecs,
    gC,gD,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix0,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix1,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix2,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix3,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix4,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix5,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix6,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix7,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix8,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix9,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix10,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix11,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix12]

theorem group_partner (i : Fin 45) :
    (gA (groupMatrix i)*groupCenter i+gB (groupMatrix i))/
      (gC (groupMatrix i)*groupCenter i+gD (groupMatrix i))=
        (groupPartner i:ℝ)/114 := by
  fin_cases i <;> norm_num [groupMatrix,groupCenter,groupSource,groupPartner,groupSpecs,
    gA,gB,gC,gD,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix0,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix1,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix2,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix3,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix4,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix5,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix6,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix7,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix8,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix9,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix10,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix11,QuantitativeArithmeticSmallLevelNineteen.continuationMatrix12]

def groupRate (i : Fin 45) : ℝ :=
  (gC (groupMatrix i)*groupCenter i+gD (groupMatrix i))^2

def groupDerivativeRate (i : Fin 45) : ℝ :=
  gC (groupMatrix i)*(gC (groupMatrix i)*groupCenter i+gD (groupMatrix i))

theorem groupRate_pos (i : Fin 45) : 0<groupRate i :=
  sq_pos_of_ne_zero (group_denominator i)

/-- Every selected SL2 row on the actual 114-grid, at every Taylor order,
with its own entire-to-the-left remainder supplied by the original input. -/
theorem original_selected_group_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) (i : Fin 45) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        gridVector (2*m) f s (gridIndex (groupSource i))-
          (groupRate i:ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (I*(groupDerivativeRate i:ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              gridVector (2*m) f (s+(n:ℂ)) (gridIndex (groupPartner i))) = error M s := by
  obtain ⟨bound,error,h⟩ := original_group_rows hf (groupMatrix i)
    (groupCenter i) (group_denominator i)
  refine ⟨bound,error,fun M => ⟨(h M).1,?_⟩⟩
  intro s hs
  have he := (h M).2 s hs
  rw [group_partner] at he
  simpa only [groupRate,groupDerivativeRate,gridVector_index,
    grid,original,groupCenter,Nat.cast_ofNat] using he


#print axioms group_partner
#print axioms original_selected_group_rows
end QuantitativeArithmeticSmallLevelNineteenGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenGridGoodRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open Complex Set SmallLevelAdditive SmallLevelTaylor

def heckeRow (p t m : ℕ) (f : ℕ → ℂ) (s : ℂ) (v : Fin 114 → ℂ) : ℂ :=
  (∑ j∈Finset.range p, v (gridIndex ((t+j*(114/p):ℕ):ℤ)))-
    ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*v (gridIndex ((p*t:ℕ):ℤ))+
    ((p:ℂ)^((m:ℂ)-s))^2*v (gridIndex ((p^2*t:ℕ):ℤ))

theorem grid_hecke_coordinate {p : ℕ} (hp : 0<p) (hpQ : p∣114) (t j : ℕ) :
    (t:ℝ)/114+(j:ℝ)/p=((t+j*(114/p):ℕ):ℝ)/114 := by
  have hprod : (p:ℝ)*((114/p:ℕ):ℝ)=114 := by
    exact_mod_cast Nat.mul_div_cancel' hpQ
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp
  nlinarith

/-- All exact good-prime rows used in the level19 continuation certificate
come from the original Euler input, including a zero Hecke eigenvalue. -/
theorem original_grid_hecke {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬p∣19) (hpQ : p∣114) :
    ∃ B : ℝ, ∀ t : ℕ, ∀ s : ℂ, B<s.re →
      heckeRow p t m f s (gridVector (2*m) f s)=0 := by
  obtain ⟨B,hB⟩ := normalized_additive_hecke hf hp hgood
  refine ⟨B,?_⟩
  intro t s hs
  have he := hB ((t:ℝ)/114) s hs
  simp_rw [grid_hecke_coordinate hp.pos hpQ] at he
  have h1 : (p:ℝ)*((t:ℝ)/114)=((p*t:ℕ):ℝ)/114 := by push_cast; ring
  have h2 : (p:ℝ)^2*((t:ℝ)/114)=((p^2*t:ℕ):ℝ)/114 := by push_cast; ring
  rw [h1,h2] at he
  simpa only [heckeRow,gridVector_index,grid,Nat.cast_ofNat,Int.cast_natCast] using he

#print axioms original_grid_hecke
end QuantitativeArithmeticSmallLevelNineteenGridAnalytic
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenGridGroupSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteenGridAnalytic
open Complex Set SmallLevelAdditive

def groupCoefficient (m : ℕ) (i : Fin 45) (n : ℕ) (s : ℂ) : ℂ :=
  (groupRate i:ℂ)^(s-(m:ℂ))*(I*(groupDerivativeRate i:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

theorem groupCoefficient_analytic (m : ℕ) (i : Fin 45) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (groupCoefficient m i n) z := by
  have hc : (groupRate i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (groupRate_pos i).ne'
  have hp : AnalyticAt ℂ (fun s : ℂ => (groupRate i:ℂ)^(s-(m:ℂ))) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact (hp.mul analyticAt_const).mul (SmallLevelTaylor.binomial_shift_analytic (2*m) n z)

/-- The complete selected group system on a common initial half-plane.
The shift index is n+1; hence every remainder extends M+1 units left. -/
theorem original_group_system {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ (B : ℝ) (error : Fin 45 → ℕ → ℂ → ℂ), ∀ i : Fin 45, ∀ M : ℕ,
      AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector (2*m) f s (gridIndex (groupSource i))-
          groupCoefficient m i 0 s*gridVector (2*m) f s (gridIndex (groupPartner i))=
        error i M s+
          ∑ n∈Finset.range M, groupCoefficient m i (n+1) s*
            gridVector (2*m) f (s+((n:ℂ)+1)) (gridIndex (groupPartner i)) := by
  choose b err h using original_selected_group_rows hf
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 45) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
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
end QuantitativeArithmeticSmallLevelNineteenGridAnalytic
end
end
