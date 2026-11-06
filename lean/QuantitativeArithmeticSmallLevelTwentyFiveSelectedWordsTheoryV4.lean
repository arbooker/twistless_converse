module

public import QuantitativeArithmeticSmallLevelTwentyFiveTheoryV4
public import SmallLevelAdditiveTheoryV4
public import SmallLevelTaylorRowCoefficientsV1
public import SmallLevelTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveSelectedWordsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open Matrix SmallLevelGenerators
open scoped MatrixGroups ModularForm

def words : Fin 11 → List (Fin 7) :=
  ![[3,3,1],
    [3,1],
    [2,1],
    [2,2,1],
    [3,3,3],
    [3],
    [3,3,6],
    [3,6],
    [6],
    [2,6],
    [4,1,5,1]]

def matrices : Fin 11 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![1,-1;-50,51],
    !![1,-1;-25,26],
    !![1,-1;25,-24],
    !![1,-1;50,-49],
    !![1,0;-75,1],
    !![1,0;-25,1],
    !![2,-1;-125,63],
    !![2,-1;-75,38],
    !![2,-1;-25,13],
    !![2,-1;25,-12],
    !![12,-11;-25,23]]

theorem words_exact (i : Fin 11) :
    (oddWord 25 13 (by decide) (words i)).val=matrices i := by
  fin_cases i <;> decide +kernel

theorem matrices_det (i : Fin 11) : (matrices i).det=1 := by
  rw [← words_exact]
  exact (oddWord 25 13 (by decide) (words i)).property

theorem original_invariant {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (i : Fin 11) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      oddWord 25 13 (by decide) (words i)=SmallLevelOriginal.fourierFunction (2*m) f := by
  exact QuantitativeArithmeticSmallLevelTwentyFive.original_word hf (words i)

#print axioms words_exact
#print axioms original_invariant
end QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveSelectedWordSpecsV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
@[expose] public section
namespace QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords

def groupWord : Fin 45 → Fin 11 :=
  ![0,1,3,4,4,6,6,6,7,1,2,3,6,1,2,2,2,2,2,2,2,2,5,7,7,8,8,8,8,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9]
def groupSource : Fin 45 → ℤ :=
  ![144,144,144,1,3,72,76,78,74,138,138,138,75,120,108,126,132,135,140,141,142,143,5,77,80,42,60,66,69,79,81,82,84,87,90,96,114,36,54,63,68,70,71,73,108]
def groupPartner : Fin 45 → ℤ :=
  ![-2,-3,6,2,-6,-2,-6,-3,-2,-4,12,4,0,-5,7,8,9,10,15,18,24,42,30,-8,-5,-11,-10,-9,-8,-48,-24,-21,-18,-16,-15,-14,-13,13,14,16,21,30,48,-24,11]
def infinityWord : Fin 3 → Fin 11 :=
  ![2,4,10]
def infinitySource : Fin 3 → ℤ :=
  ![144,2,138]

theorem group_valid : ∀ i : Fin 45,
    let g := matrices (groupWord i)
    g 1 0≠0 ∧ g 1 0*groupSource i+150*g 1 1≠0 ∧
      150*(g 0 0*groupSource i+150*g 0 1)=
        groupPartner i*(g 1 0*groupSource i+150*g 1 1) := by decide +kernel

theorem infinity_valid : ∀ i : Fin 3,
    let g := matrices (infinityWord i)
    g 1 0≠0 ∧ g 1 0*infinitySource i+150*g 1 1=0 := by decide +kernel

#print axioms group_valid
#print axioms infinity_valid
end QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveSelectedWordAnalyticV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open SmallLevelGenerators SmallLevelTaylor SmallLevelAdditive
open FinitenessFourierConstruction FinitenessOriginalFourier

theorem group_conditions (i : Fin 45) :
    let g := oddWord 25 13 (by decide) (words (groupWord i))
    (g.val 1 0:ℝ)≠0 ∧
      (g.val 1 0:ℝ)*((groupSource i:ℝ)/150)+(g.val 1 1:ℝ)≠0 := by
  dsimp only
  rw [words_exact]
  constructor
  · exact_mod_cast (group_valid i).1
  · have hn : (matrices (groupWord i) 1 0:ℝ)*(groupSource i:ℝ)+
        150*(matrices (groupWord i) 1 1:ℝ)≠0 := by
      exact_mod_cast (group_valid i).2.1
    intro hz
    apply hn
    linear_combination 150*hz

theorem infinity_conditions (i : Fin 3) :
    let g := oddWord 25 13 (by decide) (words (infinityWord i))
    (g.val 1 0:ℝ)≠0 ∧
      (g.val 1 0:ℝ)*((infinitySource i:ℝ)/150)+(g.val 1 1:ℝ)=0 := by
  dsimp only
  rw [words_exact]
  constructor
  · exact_mod_cast (infinity_valid i).1
  · have hz : (matrices (infinityWord i) 1 0:ℝ)*(infinitySource i:ℝ)+
        150*(matrices (infinityWord i) 1 1:ℝ)=0 := by
      exact_mod_cast (infinity_valid i).2
    linear_combination hz/150

theorem original_selected_taylor {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (i : Fin 45) :
    let g := oddWord 25 13 (by decide) (words (groupWord i))
    let A : ℝ := g.val 0 0
    let B : ℝ := g.val 0 1
    let C : ℝ := g.val 1 0
    let D : ℝ := g.val 1 1
    let r : ℝ := (groupSource i:ℝ)/150
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        transform (fullCoefficients f (2*m)) r s-
          (((C*r+D)^2:ℝ):ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*((C*(C*r+D):ℝ):ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            transform (fullCoefficients f (2*m)) ((A*r+B)/(C*r+D))
              (s+(n:ℂ)))=error M s := by
  exact original_word_taylor hf (words (groupWord i)) (group_conditions i).1
    ((groupSource i:ℝ)/150) (group_conditions i).2

theorem original_selected_entire {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (i : Fin 3) :
    ∃ G : ℂ→ℂ, Differentiable ℂ G ∧ ∃ B : ℝ,
      ∀ s : ℂ, B<s.re →
        G s=original (2*m) f ((infinitySource i:ℝ)/150) s := by
  exact original_word_infinity hm hf (words (infinityWord i))
    (infinity_conditions i).1 ((infinitySource i:ℝ)/150) (infinity_conditions i).2

#print axioms group_conditions
#print axioms original_selected_taylor
#print axioms original_selected_entire
end QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveSelectedGridGroupV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open Complex Set SmallLevelAdditive FinitenessOriginalFourier
def gridIndex (t : ℤ) : Fin 150 :=
  ⟨(t%150).toNat,by have h := Int.emod_lt_of_pos t (by decide : (0:ℤ)<150); omega⟩

def gridVector (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : Fin 150 → ℂ :=
  fun j => grid k f 150 (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ → ℂ) (t : ℤ) (s : ℂ) :
    gridVector k f s (gridIndex t)=grid k f 150 t s := by
  have he : ((gridIndex t).val:ℤ)=t%150 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  unfold gridVector
  rw [he]
  exact grid_mod k f (by decide : 0<150) t s

def gA (i : Fin 45) : ℝ := matrices (groupWord i) 0 0
def gB (i : Fin 45) : ℝ := matrices (groupWord i) 0 1
def gC (i : Fin 45) : ℝ := matrices (groupWord i) 1 0
def gD (i : Fin 45) : ℝ := matrices (groupWord i) 1 1

def groupCenter (i : Fin 45) : ℝ := (groupSource i:ℝ)/150

theorem group_denominator (i : Fin 45) : gC i*groupCenter i+gD i≠0 := by
  simpa only [gC,gD,groupCenter,words_exact] using (group_conditions i).2

theorem group_partner (i : Fin 45) :
    (gA i*groupCenter i+gB i)/(gC i*groupCenter i+gD i)=(groupPartner i:ℝ)/150 := by
  fin_cases i <;> norm_num [gA,gB,gC,gD,groupCenter,groupSource,groupPartner,groupWord,matrices]

def groupRate (i : Fin 45) : ℝ :=
  (gC i*groupCenter i+gD i)^2

def groupDerivativeRate (i : Fin 45) : ℝ :=
  gC i*(gC i*groupCenter i+gD i)

theorem groupRate_pos (i : Fin 45) : 0<groupRate i :=
  sq_pos_of_ne_zero (group_denominator i)

/-- Every selected SL2 row on the actual 150-grid, at every Taylor order,
with its own entire-to-the-left remainder supplied by the original input. -/
theorem original_selected_group_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) (i : Fin 45) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        gridVector (2*m) f s (gridIndex (groupSource i))-
          (groupRate i:ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (I*(groupDerivativeRate i:ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              gridVector (2*m) f (s+(n:ℂ)) (gridIndex (groupPartner i))) = error M s := by
  obtain ⟨bound,error,h⟩ := original_selected_taylor hf i
  refine ⟨bound,error,fun M => ⟨(h M).1,?_⟩⟩
  intro s hs
  have he := (h M).2 s hs
  simp only [words_exact] at he
  change transform (fullCoefficients f (2*m)) (groupCenter i) s-
    (groupRate i:ℂ)^(s-(m:ℂ))*
      (∑ n∈Finset.range M, (I*(groupDerivativeRate i:ℂ))^n*
        Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
        transform (fullCoefficients f (2*m))
          ((gA i*groupCenter i+gB i)/(gC i*groupCenter i+gD i))
          (s+(n:ℂ)))=error M s at he
  rw [group_partner] at he
  simpa only [groupRate,groupDerivativeRate,gridVector_index,
    grid,original,groupCenter,Nat.cast_ofNat] using he

#print axioms group_partner
#print axioms original_selected_group_rows
end QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveGridGoodRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open Complex Set SmallLevelAdditive SmallLevelTaylor

def heckeRow (p t m : ℕ) (f : ℕ → ℂ) (s : ℂ) (v : Fin 150 → ℂ) : ℂ :=
  (∑ j∈Finset.range p, v (gridIndex ((t+j*(150/p):ℕ):ℤ)))-
    ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*v (gridIndex ((p*t:ℕ):ℤ))+
    ((p:ℂ)^((m:ℂ)-s))^2*v (gridIndex ((p^2*t:ℕ):ℤ))

theorem grid_hecke_coordinate {p : ℕ} (hp : 0<p) (hpQ : p∣150) (t j : ℕ) :
    (t:ℝ)/150+(j:ℝ)/p=((t+j*(150/p):ℕ):ℝ)/150 := by
  have hprod : (p:ℝ)*((150/p:ℕ):ℝ)=150 := by
    exact_mod_cast Nat.mul_div_cancel' hpQ
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp
  nlinarith

/-- All exact good-prime rows used in the level25 continuation certificate
come from the original Euler input, including a zero Hecke eigenvalue. -/
theorem original_grid_hecke {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    {p : ℕ} (hp : p.Prime) (hgood : ¬p∣25) (hpQ : p∣150) :
    ∃ B : ℝ, ∀ t : ℕ, ∀ s : ℂ, B<s.re →
      heckeRow p t m f s (gridVector (2*m) f s)=0 := by
  obtain ⟨B,hB⟩ := normalized_additive_hecke hf hp hgood
  refine ⟨B,?_⟩
  intro t s hs
  have he := hB ((t:ℝ)/150) s hs
  simp_rw [grid_hecke_coordinate hp.pos hpQ] at he
  have h1 : (p:ℝ)*((t:ℝ)/150)=((p*t:ℕ):ℝ)/150 := by push_cast; ring
  have h2 : (p:ℝ)^2*((t:ℝ)/150)=((p^2*t:ℕ):ℝ)/150 := by push_cast; ring
  rw [h1,h2] at he
  simpa only [heckeRow,gridVector_index,grid,Nat.cast_ofNat,Int.cast_natCast] using he

#print axioms original_grid_hecke
end QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveGridGroupSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
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
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) :
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
end QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveSelectedHeckeRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
open SmallLevelAdditive

def heckeSpecs : Fin 51 → ℕ×ℕ :=
  ![(2,9),(2,18),(2,36),(2,39),(2,57),(2,15),(2,5),(2,10),(2,35),(2,2),(2,33),(2,37),(2,38),(2,42),(2,4),(2,12),(2,11),(2,13),(2,19),(2,21),(2,24),(2,7),(2,56),(2,62),(2,64),(2,68),(3,6),(3,8),(3,11),(3,12),(3,13),(3,14),(3,28),(3,22),(2,14),(2,22),(2,28),(2,29),(2,31),(2,43),(2,44),(2,52),(2,53),(2,58),(2,61),(2,47),(3,7),(2,32),(2,8),(2,16),(2,17)]
theorem heckeSpecs_valid (i : Fin 51) :
    (heckeSpecs i).1=2 ∨ (heckeSpecs i).1=3 ∨ (heckeSpecs i).1=5 := by
  fin_cases i <;> decide

def fiveRow (t : ℕ) (v : Fin 150→ℂ) : ℂ :=
  ∑ j∈Finset.range 5, v (gridIndex ((t:ℤ)+30*(j:ℤ)))

def selectedHeckeRows (m : ℕ) (f : ℕ→ℂ) (s : ℂ)
    (v : Fin 150→ℂ) (i : Fin 51) : ℂ :=
  if (heckeSpecs i).1=5 then fiveRow (heckeSpecs i).2 v
  else heckeRow (heckeSpecs i).1 (heckeSpecs i).2 m f s v

theorem original_grid_five {k : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 k f) :
    ∃ B : ℝ, ∀ t : ℕ, ∀ s : ℂ, B<s.re →
      fiveRow t (gridVector k f s)=0 := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticSmallLevelTwentyFive.original_five_grid hf
  refine ⟨B,fun t s hs => ?_⟩
  simpa only [fiveRow,gridVector_index] using hB (t:ℤ) s hs

/-- The selected51 good and highly ramified Hecke rows share a single
initial half-plane and follow from the original Euler product. -/
theorem original_selected_hecke {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f) :
    ∃ B : ℝ, ∀ i : Fin 51, ∀ s : ℂ, B<s.re →
      selectedHeckeRows m f s (gridVector (2*m) f s) i=0 := by
  obtain ⟨B2,h2⟩ := original_grid_hecke hf (by decide : Nat.Prime 2)
    (by decide) (by decide)
  obtain ⟨B3,h3⟩ := original_grid_hecke hf (by decide : Nat.Prime 3)
    (by decide) (by decide)
  obtain ⟨B5,h5⟩ := original_grid_five hf
  refine ⟨max B2 (max B3 B5),?_⟩
  intro i s hs
  have hs2 : B2<s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs3 : B3<s.re := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs5 : B5<s.re := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  rcases heckeSpecs_valid i with hi|hi|hi
  · simpa only [selectedHeckeRows,hi,show ¬(2:ℕ)=5 by decide,ite_false]
      using h2 (heckeSpecs i).2 s hs2
  · simpa only [selectedHeckeRows,hi,show ¬(3:ℕ)=5 by decide,ite_false]
      using h3 (heckeSpecs i).2 s hs3
  · simpa only [selectedHeckeRows,hi,ite_true]
      using h5 (heckeSpecs i).2 s hs5

#print axioms heckeSpecs_valid
#print axioms original_grid_five
#print axioms original_selected_hecke
end QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords
end
end
