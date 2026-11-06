module

public import QuantitativeArithmeticPrimitiveResiduePairV4
public import QuantitativeArithmeticSmallLevelThirteenHyperbolicV1
public import QuantitativeArithmeticSmallLevelThirteenPoleV1
public import SmallLevelModularCriterionV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirteen. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirteenRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

def axisB : GL (Fin 2) ℝ :=
  matrix (-1/2) ((5*Real.sqrt 13-26)/117) ((5*Real.sqrt 13+26)/4) (-1/2) (by
    have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
    nlinarith)

def axisD : GL (Fin 2) ℝ :=
  matrix (-1/2) ((26-5*Real.sqrt 13)/117) ((-26-5*Real.sqrt 13)/4) (-1/2) (by
    have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
    nlinarith)

theorem A_axis : SpecialLinearGroup.mapGL ℝ A*axisP=axisP*axisB := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt 13)^3=13*Real.sqrt 13 := by nlinarith [congrArg (fun x : ℝ => x*Real.sqrt 13) hs]
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,axisP,axisB,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem axisB_square : axisB*axisB=axisD := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisB,axisD,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> nlinarith

theorem A_square_axis : SpecialLinearGroup.mapGL ℝ (A*A)*axisP=axisP*axisD := by
  rw [map_mul,mul_assoc,A_axis,← mul_assoc,A_axis,mul_assoc,axisB_square]

theorem axisB_nonzero : branchQuadratic axisB 0≠0 := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hb : 5*Real.sqrt 13-26≠0 := by intro hh; nlinarith
  change (((-1/2:ℝ):ℂ)*0+(((5*Real.sqrt 13-26)/117:ℝ):ℂ))*
    ((((5*Real.sqrt 13+26)/4:ℝ):ℂ)*0+((-1/2:ℝ):ℂ))≠0
  push_cast
  simp only [mul_zero,zero_add,mul_ne_zero_iff]
  constructor
  · exact div_ne_zero (by simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat] using Complex.ofReal_ne_zero.mpr hb) (by norm_num)
  · norm_num

theorem axisD_nonzero : branchQuadratic axisD 0≠0 := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hb : 26-5*Real.sqrt 13≠0 := by intro hh; nlinarith
  change (((-1/2:ℝ):ℂ)*0+(((26-5*Real.sqrt 13)/117:ℝ):ℂ))*
    ((((-26-5*Real.sqrt 13)/4:ℝ):ℂ)*0+((-1/2:ℝ):ℂ))≠0
  push_cast
  simp only [mul_zero,zero_add,mul_ne_zero_iff]
  constructor
  · exact div_ne_zero (by simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat] using Complex.ofReal_ne_zero.mpr hb) (by norm_num)
  · norm_num

/-- The common-axis classification and finite-order defect relation kill
the original level-13 defect for every positive even weight. -/
theorem original_A (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 13 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] A=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let k : ℤ := ((2*m:ℕ):ℤ)
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let g:=F-F ∣[k] A
  let H:=g ∣[k] axisP
  obtain ⟨C,hC⟩ := original_defect_classification m hf
  change ∀ z : ℍ, (z:ℂ)^m*H z=C at hC
  have hcyc : H+(H ∣[k] axisB)+(H ∣[k] axisD)=0 := by
    have hh := congrArg (fun J : ℍ→ℂ => J ∣[k] axisP) (defect_cyclic k F)
    simp only [SlashAction.add_slash,SlashAction.zero_slash] at hh
    change (g ∣[k] axisP)+((g ∣[k] SpecialLinearGroup.mapGL ℝ A) ∣[k] axisP)+
      ((g ∣[k] SpecialLinearGroup.mapGL ℝ (A*A)) ∣[k] axisP)=0 at hh
    rw [← SlashAction.slash_mul,← SlashAction.slash_mul,A_axis,A_square_axis,
      SlashAction.slash_mul,SlashAction.slash_mul] at hh
    exact hh
  have hH : H=0 := classified_cyclic_zero m hm H C hC axisB axisD
    (matrix_det _ _ _ _ _) (matrix_det _ _ _ _ _) axisB_nonzero axisD_nonzero hcyc
  have hg := congrArg (fun J : ℍ→ℂ => J ∣[k] axisP⁻¹) hH
  change (g ∣[k] axisP) ∣[k] axisP⁻¹=0 ∣[k] axisP⁻¹ at hg
  rw [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one,SlashAction.zero_slash] at hg
  exact (sub_eq_zero.mp hg).symm

#print axioms original_A
end QuantitativeArithmeticSmallLevelThirteen
end
end

/-! ## QuantitativeArithmeticSmallLevelThirteenMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm Manifold

def Astar : SL(2,ℤ) := ⟨!![3,1;-13,-4],by decide⟩

theorem A_fricke_Astar : SpecialLinearGroup.mapGL ℝ A*fricke 13 (by decide)*
    SpecialLinearGroup.mapGL ℝ Astar=fricke 13 (by decide) := by
  have hs : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,Astar,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem original_Astar (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 13 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Astar=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hH⟩ := original_fricke_sign (by decide : 0<13) m hf
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  have hd : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ Astar):ℝ)=1 := by
    simp
  have hh := congrArg (fun M : GL (Fin 2) ℝ => F ∣[k] M) A_fricke_Astar
  have ha : F ∣[k] SpecialLinearGroup.mapGL ℝ A=F := original_A m hm hf
  change F ∣[k] fricke 13 (by decide)=χ • F at hH
  rw [SlashAction.slash_mul,SlashAction.slash_mul,ha,hH,
    det_one_smul _ hd] at hh
  change χ • (F ∣[k] Astar)=χ • F at hh
  rcases hχ with rfl|rfl
  · simpa only [one_smul] using hh
  · simpa only [neg_one_smul,neg_inj] using hh

def kernel : Fin 5→SL(2,ℤ)
  | 0 => T
  | 1 => lower 13
  | 2 => G₂
  | 3 => A
  | _ => Astar

theorem original_kernel (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 13 (2*m) f) (i : Fin 5) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  fin_cases i
  · exact original_T _ _
  · exact original_lower (by decide) hf
  · exact original_G₂ hf
  · exact original_A m hm hf
  · exact original_Astar m hm hf

#print axioms original_kernel
end QuantitativeArithmeticSmallLevelThirteen
end
end

/-! ## QuantitativeArithmeticSmallLevelThirteenGeneratorsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def letter : Fin 11 → SL(2,ℤ)
  | 0 => kernel 0
  | 1 => kernel 1
  | 2 => kernel 2
  | 3 => kernel 3
  | 4 => kernel 4
  | 5 => (kernel 0)⁻¹
  | 6 => (kernel 1)⁻¹
  | 7 => (kernel 2)⁻¹
  | 8 => (kernel 3)⁻¹
  | 9 => (kernel 4)⁻¹
  | _ => -1

def word (w : List (Fin 11)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 5, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 11)) : word w∈K := by
  have hl (i : Fin 11) : letter i∈K := by
    fin_cases i
    · exact hK 0
    · exact hK 1
    · exact hK 2
    · exact hK 3
    · exact hK 4
    · exact K.inv_mem (hK 0)
    · exact K.inv_mem (hK 1)
    · exact K.inv_mem (hK 2)
    · exact K.inv_mem (hK 3)
    · exact K.inv_mem (hK 4)
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 13) : SL(2,ℤ) :=
  match c.val*13+d.val with
  | 13 | 26 | 39 | 52 | 65 | 78 | 91 | 104 | 117 | 130 | 143 | 156 => ⟨!![0,-1;1,0],by decide⟩
  | 14 | 28 | 42 | 56 | 70 | 84 | 98 | 112 | 126 | 140 | 154 | 168 => ⟨!![0,-1;1,1],by decide⟩
  | 25 | 37 | 49 | 61 | 73 | 85 | 97 | 109 | 121 | 133 | 145 | 157 => ⟨!![0,-1;1,-1],by decide⟩
  | 15 | 30 | 45 | 60 | 75 | 90 | 92 | 107 | 122 | 137 | 152 | 167 => ⟨!![0,-1;1,2],by decide⟩
  | 24 | 35 | 46 | 57 | 68 | 79 | 103 | 114 | 125 | 136 | 147 | 158 => ⟨!![0,-1;1,-2],by decide⟩
  | 19 | 38 | 44 | 63 | 69 | 88 | 94 | 113 | 119 | 138 | 144 | 163 => ⟨!![-1,0;2,-1],by decide⟩
  | 16 | 32 | 48 | 64 | 67 | 83 | 99 | 115 | 118 | 134 | 150 | 166 => ⟨!![0,-1;1,3],by decide⟩
  | 20 | 27 | 47 | 54 | 74 | 81 | 101 | 108 | 128 | 135 | 155 | 162 => ⟨!![-1,0;-2,-1],by decide⟩
  | 23 | 33 | 43 | 53 | 76 | 86 | 96 | 106 | 129 | 139 | 149 | 159 => ⟨!![0,-1;1,-3],by decide⟩
  | 18 | 36 | 41 | 59 | 77 | 82 | 100 | 105 | 123 | 141 | 146 | 164 => ⟨!![-1,1;2,-3],by decide⟩
  | 17 | 34 | 51 | 55 | 72 | 89 | 93 | 110 | 127 | 131 | 148 | 165 => ⟨!![-1,0;3,-1],by decide⟩
  | 21 | 29 | 50 | 58 | 66 | 87 | 95 | 116 | 124 | 132 | 153 | 161 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 22 | 31 | 40 | 62 | 71 | 80 | 102 | 111 | 120 | 142 | 151 | 160 => ⟨!![-1,0;-3,-1],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 13) : List (Fin 11) :=
  match c.val*13+d.val with
  | 13 | 26 | 39 | 52 | 65 | 78 | 91 | 104 | 117 | 130 | 143 | 156 => [10]
  | 14 | 28 | 42 | 56 | 70 | 84 | 98 | 112 | 126 | 140 | 154 | 168 => [5]
  | 25 | 37 | 49 | 61 | 73 | 85 | 97 | 109 | 121 | 133 | 145 | 157 => [0, 10]
  | 19 | 38 | 44 | 63 | 69 | 88 | 94 | 113 | 119 | 138 | 144 | 163 => [10]
  | 20 | 27 | 47 | 54 | 74 | 81 | 101 | 108 | 128 | 135 | 155 | 162 => [10]
  | 18 | 36 | 41 | 59 | 77 | 82 | 100 | 105 | 123 | 141 | 146 | 164 => [5, 7, 1, 4]
  | 17 | 34 | 51 | 55 | 72 | 89 | 93 | 110 | 127 | 131 | 148 | 165 => [10]
  | 21 | 29 | 50 | 58 | 66 | 87 | 95 | 116 | 124 | 132 | 153 | 161 => [8, 2]
  | 22 | 31 | 40 | 62 | 71 | 80 | 102 | 111 | 120 | 142 | 151 | 160 => [10]
  | _ => []

def edgeTRow (c d : ZMod 13) : List (Fin 11) :=
  match c.val*13+d.val with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => [0]
  | 19 | 38 | 44 | 63 | 69 | 88 | 94 | 113 | 119 | 138 | 144 | 163 => [5, 10]
  | 16 | 32 | 48 | 64 | 67 | 83 | 99 | 115 | 118 | 134 | 150 | 166 => [4]
  | 17 | 34 | 51 | 55 | 72 | 89 | 93 | 110 | 127 | 131 | 148 | 165 => [9, 6, 2, 0]
  | 21 | 29 | 50 | 58 | 66 | 87 | 95 | 116 | 124 | 132 | 153 | 161 => [7, 3]
  | 22 | 31 | 40 | 62 | 71 | 80 | 102 | 111 | 120 | 142 | 151 | 160 => [8, 10]
  | _ => []

def rep (g : SL(2,ZMod 13)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 13)) :
    ∃ a b : ZMod 13, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe














theorem edgeSRow_checked : ∀ c d : ZMod 13, (∃ a b : ZMod 13, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 13,
    Nat.gcd (Nat.gcd c.val d.val) 13 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)














theorem edgeTRow_checked : ∀ c d : ZMod 13, (∃ a b : ZMod 13, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 13,
    Nat.gcd (Nat.gcd c.val d.val) 13 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 13)) :
    rep g*S*(rep (g*reduction 13 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 13 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 13 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 13)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 13)) :
    rep g*T*(rep (g*reduction 13 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 13 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 13 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 13)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 13)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 13, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 5, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 13) : γ∈K := by
  apply transversal_mem (reduction 13) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeSRow_checked
#print axioms edgeTRow_checked
#print axioms gamma0_mem

end QuantitativeArithmeticSmallLevelThirteen
end
end

/-! ## QuantitativeArithmeticSmallLevelThirteenModularV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

/-- Every Gamma0(13) transformation follows from the literal Euler input. -/
theorem gamma_zero_thirteen (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 13 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 13) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  let K := slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f)
  change γ∈K
  exact gamma0_mem K (original_kernel m hm hf)
    (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- Complete original-input level-13 modularity for every positive even weight.
Holomorphy and boundedness at all cusps come from the original input via
`modular_of_transformations`; they are not extra assumptions. -/
theorem level_thirteen {k : ℕ} (hkpos : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 13 k f) : IsModular 13 k f := by
  obtain ⟨m,hm⟩ := heven
  have hk : k=2*m := by omega
  rw [hk] at hf ⊢
  exact modular_of_transformations (by decide) hf (gamma_zero_thirteen m (by omega) hf)

#print axioms gamma_zero_thirteen
#print axioms level_thirteen
end QuantitativeArithmeticSmallLevelThirteen
end
end
