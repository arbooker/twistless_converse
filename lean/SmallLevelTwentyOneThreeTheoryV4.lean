module

public import SmallLevelTwentyOneChiFiveGroupTheoryV4

/-! Consolidated chapter: SmallLevelTwentyOneThree. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneThreeMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneThree
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup
open scoped MatrixGroups ModularForm

def matrixThree (a b c d : ℝ) (hd : a*d-b*c=3) : GL (Fin 2) ℝ :=
  matrix (a/Real.sqrt 3) (b/Real.sqrt 3) (c/Real.sqrt 3) (d/Real.sqrt 3) (by
    have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
    field_simp [hn]
    nlinarith)

def P : GL (Fin 2) ℝ := matrixThree 3 1 (-21) (-6) (by norm_num)
def Q : GL (Fin 2) ℝ := matrixThree 3 (-1) 21 (-6) (by norm_num)
def H : SL(2,ℤ) := ⟨!![8,-1;-63,8],by decide⟩

theorem P_det : (GeneralLinearGroup.det P:ℝ)=1 := by
  unfold P matrixThree
  exact matrix_det _ _ _ _ _
theorem Q_det : (GeneralLinearGroup.det Q:ℝ)=1 := by
  unfold Q matrixThree
  exact matrix_det _ _ _ _ _
theorem H_word : H=(-1)*C*E⁻¹*(lower 21)⁻¹ := by decide

theorem P_inv : P⁻¹=matrixThree (-6) (-1) 21 3 (by norm_num) := by
  apply mul_left_cancel (a:=P)
  rw [mul_inv_cancel]
  symm
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem Q_inv : Q⁻¹=matrixThree (-6) 1 (-21) 3 (by norm_num) := by
  apply mul_left_cancel (a:=Q)
  rw [mul_inv_cancel]
  symm
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem pair_relation : P*SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹*Q⁻¹=
    SpecialLinearGroup.mapGL ℝ H := by
  rw [Q_inv,show ModularGroup.T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,H,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem sqrt_conductor : Real.sqrt 63=Real.sqrt 3*Real.sqrt 21 := by
  rw [show (63:ℝ)=3*21 by norm_num,Real.sqrt_mul (by norm_num)]

theorem positive_branch : fricke 21 (by decide)*P*translation (-1/3)=
    translation (1/3)*fricke 63 (by decide) := by
  have h3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have h21 : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn3 : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn21 : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,P,matrixThree,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn3,hn21] <;> (try simp only [h3,h21]) <;> nlinarith

theorem negative_branch : fricke 21 (by decide)*Q*translation (1/3)=
    translation (-1/3)*fricke 63 (by decide) := by
  have h3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have h21 : (Real.sqrt 21)^2=21 := Real.sq_sqrt (by norm_num)
  have hn3 : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn21 : Real.sqrt 21≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Q,matrixThree,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn3,hn21] <;> (try simp only [h3,h21]) <;> nlinarith

#print axioms P_inv
#print axioms pair_relation
#print axioms positive_branch
#print axioms negative_branch
end SmallLevelTwentyOneThree
end
end

/-! ## SmallLevelTwentyOneThreePairV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneThree
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open FinitenessOriginalFourier FinitenessFourierConstruction FinitenessAnalyticReconstruction
open SmallLevelTwentyOneChiFiveGroup
open scoped MatrixGroups ModularForm

def delta (f : ℕ → ℂ) : ℂ := FinitenessNormalizedTwistProduct.root 21 f 3

theorem original_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 k f) :
    ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] P) ∣[(k:ℤ)] translation (-1/3))+
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] Q) ∣[(k:ℤ)] translation (1/3))=
    delta f • ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/3))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-1/3))) := by
  obtain ⟨ε,_hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law (by decide : 0<21) hf
  have h := pair_of_fricke 21 63 k (by decide) (by decide) (1/3)
    (fourier (fullCoefficients f k)) (ε*Complex.I^k) (delta f)
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3)
    (by
      intro z hz
      simpa [FinitenessNormalizedTwistProduct.root,twist,Finset.sum_range_succ] using
        hlaw 1 (by decide) z hz)
    (by
      intro z hz
      have ht := hlaw 3 (by decide) z hz
      rw [show Nat.lcm 21 (3^2)=63 by decide,
        SmallLevelThree.twist_three _ (periodic _),SmallLevelThree.twist_three _ (periodic _)] at ht
      simpa only [delta,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
        Nat.cast_ofNat,mul_assoc] using ht)
  have hfun : (fun z : ℍ => fourier (fullCoefficients f k) z)=SmallLevelOriginal.fourierFunction k f := by
    funext z
    rfl
  rw [hfun] at h
  have hp : (fricke 21 (by decide))⁻¹*translation (1/3)*fricke 63 (by decide)=P*translation (-1/3) := by
    rw [mul_assoc,← positive_branch]
    group
  have hn : (fricke 21 (by decide))⁻¹*translation (-1/3)*fricke 63 (by decide)=Q*translation (1/3) := by
    rw [mul_assoc,← negative_branch]
    group
  simp only [neg_div] at hn hp ⊢
  rw [hp,hn] at h
  simpa only [SlashAction.slash_mul] using h

theorem original_H {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] H=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  obtain ⟨hC,_hD⟩ := original_C_D hm hf
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  rw [H_word]
  exact K.mul_mem (K.mul_mem (K.mul_mem (SmallLevelThirtySix.slash_neg_one_even F m) hC)
    (K.inv_mem (original_E hf))) (K.inv_mem (original_lower (by decide : 0<21) hf))

theorem original_Q_action {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Q=
      (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)
        ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹ := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  have hi : F ∣[k] (SpecialLinearGroup.mapGL ℝ H)⁻¹=F := by
    rw [← map_inv]
    exact K.inv_mem (original_H hm hf)
  have hr : SpecialLinearGroup.mapGL ℝ H*Q=P*SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹ := by
    rw [← pair_relation]
    group
  have hq : Q=(SpecialLinearGroup.mapGL ℝ H)⁻¹*P*SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹ := by
    rw [mul_assoc,← hr]
    group
  change F ∣[k] Q=(F ∣[k] P) ∣[k] SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹
  rw [hq,SlashAction.slash_mul,SlashAction.slash_mul,hi]

#print axioms original_pair
#print axioms original_H
#print axioms original_Q_action
end SmallLevelTwentyOneThree
end
end

/-! ## SmallLevelTwentyOneThreeAntiPeriodV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneThree
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open scoped MatrixGroups ModularForm

theorem translation_zero : translation 0=1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]

theorem translation_T : SpecialLinearGroup.mapGL ℝ ModularGroup.T=translation 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ModularGroup.T,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]

theorem translation_Tinv : SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹=translation (-1) := by
  rw [map_inv,translation_T]
  apply inv_eq_of_mul_eq_one_right
  rw [translation_mul]
  norm_num [translation_zero]

def defect (k : ℕ) (f : ℕ → ℂ) : ℍ → ℂ :=
  (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] P)-delta f • SmallLevelOriginal.fourierFunction k f

/-- The original Ramanujan3 equation forces anti-period 1/3 without any
nonvanishing condition on the Hecke2 eigenvalue. -/
theorem original_antiperiod {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    defect (2*m) f ∣[((2*m:ℕ):ℤ)] translation (1/3)= -defect (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let h := defect (2*m) f
  have hT : F ∣[k] translation (-1)=F := by
    rw [← translation_Tinv]
    exact (slashStabilizer k F).inv_mem (original_T (2*m) f)
  have hQ : (F ∣[k] Q)-delta f • F=h ∣[k] translation (-1) := by
    dsimp only [h,defect]
    rw [SmallLevelEleven.sub_slash,det_one_smul _ (translation_det _)]
    change (F ∣[k] Q)-delta f • F=(F ∣[k] P) ∣[k] translation (-1)-delta f • (F ∣[k] translation (-1))
    rw [hT,← translation_Tinv,original_Q_action hm hf]
  have hp : h ∣[k] translation (-1/3)+(h ∣[k] translation (-1)) ∣[k] translation (1/3)=0 := by
    rw [← hQ]
    dsimp only [h,defect]
    simp only [SmallLevelEleven.sub_slash,det_one_smul _ (translation_det _)]
    have he := original_pair hf
    change (F ∣[k] P) ∣[k] translation (-1/3)+(F ∣[k] Q) ∣[k] translation (1/3)=
      delta f • ((F ∣[k] translation (1/3))+(F ∣[k] translation (-1/3))) at he
    rw [smul_add] at he
    linear_combination he
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] translation (2/3)) hp
  simp only [SlashAction.add_slash,SlashAction.zero_slash,← SlashAction.slash_mul,
    translation_mul] at hh
  norm_num only [show (-1/3:ℝ)+2/3=1/3 by ring,
    show (-1:ℝ)+(1/3+2/3)=0 by ring,translation_zero,SlashAction.slash_one] at hh
  change h ∣[k] translation (1/3)= -h
  linear_combination hh

theorem original_period_two_thirds {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    defect (2*m) f ∣[((2*m:ℕ):ℤ)] translation (2/3)=defect (2*m) f := by
  rw [show (2/3:ℝ)=1/3+1/3 by ring,← translation_mul,SlashAction.slash_mul,
    original_antiperiod hm hf,SlashAction.neg_slash,original_antiperiod hm hf,neg_neg]

theorem original_antiperiod_one {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    defect (2*m) f ∣[((2*m:ℕ):ℤ)] translation 1= -defect (2*m) f := by
  rw [show (1:ℝ)=2/3+1/3 by ring,← translation_mul,SlashAction.slash_mul,
    original_period_two_thirds hm hf,original_antiperiod hm hf]

#print axioms original_antiperiod
#print axioms original_period_two_thirds
#print axioms original_antiperiod_one
end SmallLevelTwentyOneThree
end
end

/-! ## SmallLevelTwentyOneThreeHeckeMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneThree
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

def pLeft : SL(2,ℤ) := ⟨!![-5,-1;21,4],by decide⟩
def pMiddle : SL(2,ℤ) := ⟨!![8,1;-105,-13],by decide⟩
def pRight : SL(2,ℤ) := ⟨!![-17,-2;-42,-5],by decide⟩
theorem pLeft_word : pLeft=(-1)*A := by decide
theorem pMiddle_word : pMiddle=(-1)*E*C⁻¹ := by decide
theorem pRight_word : pRight=(-1)*C⁻¹ := by decide

theorem P_branch_infinity : heckeInfinity*P=SpecialLinearGroup.mapGL ℝ pLeft*P*heckeFinite 0 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeInfinity,heckeFinite,P,matrixThree,matrix,pLeft,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem P_branch_zero : heckeFinite 0*P=SpecialLinearGroup.mapGL ℝ pMiddle*P*
    SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹*heckeFinite 1 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [show ModularGroup.T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) by decide]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,P,matrixThree,matrix,pMiddle,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem P_branch_one : heckeFinite 1*P=SpecialLinearGroup.mapGL ℝ pRight*P*heckeInfinity := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeInfinity,heckeFinite,P,matrixThree,matrix,pRight,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

theorem infinity_translation : heckeInfinity*translation (2/3)=translation (4/3)*heckeInfinity := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeInfinity,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem finite_translation (j : ℤ) : heckeFinite j*translation (2/3)=translation (1/3)*heckeFinite j := by
  apply Units.ext
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    norm_num [heckeFinite,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem finite_one_half : heckeFinite 1=translation (1/2)*heckeFinite 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

#print axioms P_branch_infinity
#print axioms P_branch_zero
#print axioms P_branch_one
#print axioms finite_translation
end SmallLevelTwentyOneThree
end
end

/-! ## SmallLevelTwentyOneThreeHeckeDefectV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneThree
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

theorem det_two_smul (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=2)
    (F : ℍ → ℂ) (k : ℤ) (c : ℂ) : (c • F) ∣[k] g=c • (F ∣[k] g) := by
  rw [ModularForm.smul_slash]
  have hs : σ g=ContinuousAlgEquiv.refl ℝ ℂ := by simp only [σ,hg]; norm_num
  rw [hs,ContinuousAlgEquiv.refl_apply]

/-- The anti-period and the signed Hecke relation alone force the defect to
vanish. The scalar Hecke eigenvalue may be zero in this algebraic lemma. -/
theorem signed_hecke_zero (h : ℍ → ℂ) (k : ℤ) (lam : ℂ)
    (ha : h ∣[k] translation (1/3)= -h)
    (he : (h ∣[k] heckeInfinity)+(h ∣[k] heckeFinite 0)-(h ∣[k] heckeFinite 1)=lam • h) : h=0 := by
  have h23 : h ∣[k] translation (2/3)=h := by
    rw [show (2/3:ℝ)=1/3+1/3 by ring,← translation_mul,SlashAction.slash_mul,
      ha,SlashAction.neg_slash,ha,neg_neg]
  have h43 : h ∣[k] translation (4/3)=h := by
    rw [show (4/3:ℝ)=2/3+2/3 by ring,← translation_mul,SlashAction.slash_mul,h23,h23]
  have h1 : h ∣[k] translation 1= -h := by
    rw [show (1:ℝ)=2/3+1/3 by ring,← translation_mul,SlashAction.slash_mul,h23,ha]
  have hi : (h ∣[k] heckeInfinity) ∣[k] translation (2/3)=h ∣[k] heckeInfinity := by
    rw [← SlashAction.slash_mul,infinity_translation,SlashAction.slash_mul,h43]
  have hj (j : ℤ) : (h ∣[k] heckeFinite j) ∣[k] translation (2/3)= -(h ∣[k] heckeFinite j) := by
    rw [← SlashAction.slash_mul,finite_translation,SlashAction.slash_mul,ha,SlashAction.neg_slash]
  have ht := congrArg (fun G : ℍ → ℂ => G ∣[k] translation (2/3)) he
  simp only [SmallLevelEleven.sub_slash,SlashAction.add_slash,
    det_one_smul _ (translation_det _),h23,hi,hj] at ht
  have h01 : h ∣[k] heckeFinite 0=h ∣[k] heckeFinite 1 := by
    funext z
    have hez := congrFun he z
    have htz := congrFun ht z
    simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hez htz
    linear_combination (1/2:ℂ)*(hez-htz)
  rw [finite_one_half,SlashAction.slash_mul] at h01
  have hhalf := congrArg (fun G : ℍ → ℂ => G ∣[k] (heckeFinite 0)⁻¹) h01
  simp only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] at hhalf
  have hperiod : h ∣[k] translation 1=h := by
    rw [show (1:ℝ)=1/2+1/2 by ring,← translation_mul,SlashAction.slash_mul,
      ← hhalf,← hhalf]
  funext z
  have hpz := congrFun hperiod z
  have h1z := congrFun h1 z
  simp only [Pi.neg_apply] at h1z
  change h z=0
  linear_combination (1/2:ℂ)*(h1z-hpz)

/-- For nonzero f(2), the known A,C,E transformations give the signed
Hecke relation of the P-defect. -/
theorem original_signed_hecke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2≠0) :
    (defect (2*m) f ∣[((2*m:ℕ):ℤ)] heckeInfinity)+
      (defect (2*m) f ∣[((2*m:ℕ):ℤ)] heckeFinite 0)-
      (defect (2*m) f ∣[((2*m:ℕ):ℤ)] heckeFinite 1)=
    (FinitenessAllLevelHeckePower.scale 2 m*f 2/2) • defect (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  have hneg : F ∣[k] (-1:SL(2,ℤ))=F := SmallLevelThirtySix.slash_neg_one_even F m
  obtain ⟨hC,_⟩ := original_C_D hm hf
  have hl : F ∣[k] pLeft=F := by
    rw [pLeft_word]
    exact K.mul_mem hneg (original_A hm hf hf2)
  have hm' : F ∣[k] pMiddle=F := by
    rw [pMiddle_word]
    exact K.mul_mem (K.mul_mem hneg (original_E hf)) (K.inv_mem hC)
  have hr : F ∣[k] pRight=F := by
    rw [pRight_word]
    exact K.mul_mem hneg (K.inv_mem hC)
  have he := SmallLevelGoodHeckeTwo.original_hecke_two (by decide : ¬2∣21) hf.toEulerData m
  let lam := FinitenessAllLevelHeckePower.scale 2 m*f 2/2
  change heckeTwo k F=lam • F at he
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] P) he
  simp only [heckeTwo,SlashAction.add_slash,det_one_smul _ P_det] at hh
  simp only [← SlashAction.slash_mul] at hh
  rw [P_branch_infinity,P_branch_zero,P_branch_one] at hh
  simp only [SlashAction.slash_mul] at hh
  change ((F ∣[k] pLeft) ∣[k] P) ∣[k] heckeFinite 0+
    (((F ∣[k] pMiddle) ∣[k] P) ∣[k] ModularGroup.T⁻¹) ∣[k] heckeFinite 1+
    ((F ∣[k] pRight) ∣[k] P) ∣[k] heckeInfinity=lam • (F ∣[k] P) at hh
  rw [hl,hm',hr] at hh
  have hTin : F ∣[k] translation (-1)=F := by
    rw [← translation_Tinv]
    exact K.inv_mem (original_T (2*m) f)
  have ha := original_antiperiod_one hm hf
  change defect (2*m) f ∣[k] translation 1= -defect (2*m) f at ha
  have hai := congrArg (fun G : ℍ → ℂ => G ∣[k] translation (-1)) ha
  simp only [← SlashAction.slash_mul,translation_mul,SlashAction.neg_slash] at hai
  norm_num only [show (1:ℝ)+ -1=0 by ring,translation_zero,SlashAction.slash_one] at hai
  have hback : (F ∣[k] P) ∣[k] ModularGroup.T⁻¹=(2:ℂ) • (delta f • F)-(F ∣[k] P) := by
    change (F ∣[k] P) ∣[k] SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹=_
    rw [translation_Tinv]
    dsimp only [defect] at hai
    change (F ∣[k] P)-delta f • F= -(((F ∣[k] P)-delta f • F) ∣[k] translation (-1)) at hai
    rw [SmallLevelEleven.sub_slash,det_one_smul _ (translation_det _),hTin] at hai
    funext z
    have hz := congrFun hai z
    simp only [Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hz ⊢
    linear_combination hz
  rw [hback,SmallLevelEleven.sub_slash,det_two_smul _ (heckeFinite_det _),
    det_two_smul _ (heckeFinite_det _)] at hh
  change (defect (2*m) f ∣[k] heckeInfinity)+(defect (2*m) f ∣[k] heckeFinite 0)-
    (defect (2*m) f ∣[k] heckeFinite 1)=lam • defect (2*m) f
  dsimp only [defect]
  simp only [SmallLevelEleven.sub_slash,det_two_smul _ heckeInfinity_det,
    det_two_smul _ (heckeFinite_det _),smul_sub]
  change (F ∣[k] P) ∣[k] heckeInfinity-delta f • (F ∣[k] heckeInfinity)+
    ((F ∣[k] P) ∣[k] heckeFinite 0-delta f • (F ∣[k] heckeFinite 0))-
    ((F ∣[k] P) ∣[k] heckeFinite 1-delta f • (F ∣[k] heckeFinite 1))=
    lam • (F ∣[k] P)-lam • (delta f • F)
  dsimp only [heckeTwo] at he
  funext z
  have hhz := congrFun hh z
  have hez := congrFun he z
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hhz hez ⊢
  linear_combination hhz-delta f*hez

theorem original_P_nonzero {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2≠0) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      delta f • SmallLevelOriginal.fourierFunction (2*m) f := by
  have h := signed_hecke_zero _ _ _ (original_antiperiod hm hf) (original_signed_hecke hm hf hf2)
  exact sub_eq_zero.mp h

#print axioms signed_hecke_zero
#print axioms original_signed_hecke
#print axioms original_P_nonzero
end SmallLevelTwentyOneThree
end
end

/-! ## SmallLevelTwentyOneZeroPeriodAlgebraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneThree
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

theorem translation_period_nat (h : ℍ → ℂ) (k : ℤ) (r : ℝ)
    (hp : h ∣[k] translation r=h) (n : ℕ) : h ∣[k] translation (n*r)=h := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul,translation_zero,SlashAction.slash_one]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,← translation_mul,SlashAction.slash_mul,ih,hp]

theorem finite_translation_general (j : ℤ) (r : ℝ) :
    heckeFinite j*translation (2*r)=translation r*heckeFinite j := by
  apply Units.ext
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    norm_num [heckeFinite,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  ring

theorem infinity_translation_general (r : ℝ) :
    heckeInfinity*translation r=translation (2*r)*heckeInfinity := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeInfinity,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- At zero Hecke2 value the inverse-P defect inherits period2/3 from
its signed relation with the P-defect. -/
theorem inverse_defect_period (h g : ℍ → ℂ) (k : ℤ)
    (hp : h ∣[k] translation (2/3)=h)
    (he : (g ∣[k] heckeFinite 0)+(h ∣[k] heckeInfinity)-(h ∣[k] heckeFinite 1)=0) :
    g ∣[k] translation (2/3)=g := by
  have h83 : h ∣[k] translation (8/3)=h := by
    convert translation_period_nat h k (2/3) hp 4 using 1; norm_num
  have hi : (h ∣[k] heckeInfinity) ∣[k] translation (4/3)=h ∣[k] heckeInfinity := by
    rw [← SlashAction.slash_mul,infinity_translation_general,SlashAction.slash_mul]
    norm_num only [show (2:ℝ)*(4/3)=8/3 by ring]
    rw [h83]
  have hj (j : ℤ) : (h ∣[k] heckeFinite j) ∣[k] translation (4/3)=h ∣[k] heckeFinite j := by
    rw [show (4/3:ℝ)=2*(2/3) by ring,← SlashAction.slash_mul,finite_translation_general,
      SlashAction.slash_mul,hp]
  have ht := congrArg (fun G : ℍ → ℂ => G ∣[k] translation (4/3)) he
  simp only [SmallLevelEleven.sub_slash,SlashAction.add_slash,SlashAction.zero_slash,hi,hj] at ht
  have h0 : (g ∣[k] heckeFinite 0) ∣[k] translation (4/3)=g ∣[k] heckeFinite 0 := by
    linear_combination ht-he
  rw [show (4/3:ℝ)=2*(2/3) by ring,← SlashAction.slash_mul,finite_translation_general,
    SlashAction.slash_mul] at h0
  have h := congrArg (fun G : ℍ → ℂ => G ∣[k] (heckeFinite 0)⁻¹) h0
  simpa only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] using h

def Kplus : SL(2,ℤ) := ⟨!![43,6;-294,-41],by decide⟩
def Kminus : SL(2,ℤ) := ⟨!![85,24;-294,-83],by decide⟩

theorem zero_branch_infinity : heckeInfinity*P=
    SpecialLinearGroup.mapGL ℝ (-1:SL(2,ℤ))*P⁻¹*heckeFinite 0 := by
  rw [P_inv]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeInfinity,heckeFinite,P,matrixThree,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem Kplus_relation : SpecialLinearGroup.mapGL ℝ Kplus*P=P*translation 2 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Kplus,P,matrixThree,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem Kminus_relation : SpecialLinearGroup.mapGL ℝ Kminus*P⁻¹=P⁻¹*translation 2 := by
  rw [P_inv]
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Kminus,matrixThree,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

#print axioms inverse_defect_period
#print axioms zero_branch_infinity
#print axioms Kplus_relation
#print axioms Kminus_relation
end SmallLevelTwentyOneThree
end
end

/-! ## SmallLevelTwentyOneZeroPeriodV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneThree
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

def inverseDefect (k : ℕ) (f : ℕ → ℂ) : ℍ → ℂ :=
  (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] P⁻¹)-delta f • SmallLevelOriginal.fourierFunction k f

theorem original_P_backward {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)
      ∣[((2*m:ℕ):ℤ)] ModularGroup.T⁻¹=
    (2:ℂ) • (delta f • SmallLevelOriginal.fourierFunction (2*m) f)-
      (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P) := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  have hTin : F ∣[k] translation (-1)=F := by
    rw [← translation_Tinv]
    exact (slashStabilizer k F).inv_mem (original_T (2*m) f)
  have ha := original_antiperiod_one hm hf
  change defect (2*m) f ∣[k] translation 1= -defect (2*m) f at ha
  have hai := congrArg (fun G : ℍ → ℂ => G ∣[k] translation (-1)) ha
  simp only [← SlashAction.slash_mul,translation_mul,SlashAction.neg_slash] at hai
  norm_num only [show (1:ℝ)+ -1=0 by ring,translation_zero,SlashAction.slash_one] at hai
  change (F ∣[k] P) ∣[k] SpecialLinearGroup.mapGL ℝ ModularGroup.T⁻¹=_
  rw [translation_Tinv]
  dsimp only [defect] at hai
  change (F ∣[k] P)-delta f • F= -(((F ∣[k] P)-delta f • F) ∣[k] translation (-1)) at hai
  rw [SmallLevelEleven.sub_slash,det_one_smul _ (translation_det _),hTin] at hai
  funext z
  have hz := congrFun hai z
  simp only [Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] at hz ⊢
  linear_combination hz

theorem original_zero_signed_hecke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2=0) :
    (inverseDefect (2*m) f ∣[((2*m:ℕ):ℤ)] heckeFinite 0)+
      (defect (2*m) f ∣[((2*m:ℕ):ℤ)] heckeInfinity)-
      (defect (2*m) f ∣[((2*m:ℕ):ℤ)] heckeFinite 1)=0 := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  have hneg : F ∣[k] (-1:SL(2,ℤ))=F := SmallLevelThirtySix.slash_neg_one_even F m
  obtain ⟨hC,_⟩ := original_C_D hm hf
  have hm' : F ∣[k] pMiddle=F := by
    rw [pMiddle_word]
    exact K.mul_mem (K.mul_mem hneg (original_E hf)) (K.inv_mem hC)
  have hr : F ∣[k] pRight=F := by
    rw [pRight_word]
    exact K.mul_mem hneg (K.inv_mem hC)
  have he := SmallLevelGoodHeckeTwo.original_hecke_two (by decide : ¬2∣21) hf.toEulerData m
  rw [hf2,mul_zero,zero_div,zero_smul] at he
  change heckeTwo k F=0 at he
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] P) he
  simp only [heckeTwo,SlashAction.add_slash,SlashAction.zero_slash] at hh
  simp only [← SlashAction.slash_mul] at hh
  rw [zero_branch_infinity,P_branch_zero,P_branch_one] at hh
  simp only [SlashAction.slash_mul] at hh
  change ((F ∣[k] (-1:SL(2,ℤ))) ∣[k] P⁻¹) ∣[k] heckeFinite 0+
    (((F ∣[k] pMiddle) ∣[k] P) ∣[k] ModularGroup.T⁻¹) ∣[k] heckeFinite 1+
    ((F ∣[k] pRight) ∣[k] P) ∣[k] heckeInfinity=0 at hh
  rw [hneg,hm',hr] at hh
  have hback := original_P_backward hm hf
  change (F ∣[k] P) ∣[k] ModularGroup.T⁻¹=(2:ℂ) • (delta f • F)-(F ∣[k] P) at hback
  rw [hback,SmallLevelEleven.sub_slash,det_two_smul _ (heckeFinite_det _),
    det_two_smul _ (heckeFinite_det _)] at hh
  change (inverseDefect (2*m) f ∣[k] heckeFinite 0)+(defect (2*m) f ∣[k] heckeInfinity)-
    (defect (2*m) f ∣[k] heckeFinite 1)=0
  dsimp only [defect,inverseDefect]
  simp only [SmallLevelEleven.sub_slash,det_two_smul _ heckeInfinity_det,
    det_two_smul _ (heckeFinite_det _)]
  change (F ∣[k] P⁻¹) ∣[k] heckeFinite 0-delta f • (F ∣[k] heckeFinite 0)+
    ((F ∣[k] P) ∣[k] heckeInfinity-delta f • (F ∣[k] heckeInfinity))-
    ((F ∣[k] P) ∣[k] heckeFinite 1-delta f • (F ∣[k] heckeFinite 1))=0
  dsimp only [heckeTwo] at he
  funext z
  have hhz := congrFun hh z
  have hez := congrFun he z
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at hhz hez ⊢
  linear_combination hhz-delta f*hez

theorem original_inverse_period {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2=0) :
    inverseDefect (2*m) f ∣[((2*m:ℕ):ℤ)] translation (2/3)=inverseDefect (2*m) f :=
  inverse_defect_period _ _ _ (original_period_two_thirds hm hf) (original_zero_signed_hecke hm hf hf2)

theorem original_Kplus_Kminus {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2=0) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Kplus=SmallLevelOriginal.fourierFunction (2*m) f ∧
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Kminus=SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  have hF1 : F ∣[k] translation 1=F := by
    rw [← translation_T]
    exact original_T (2*m) f
  have hF2 : F ∣[k] translation 2=F := by
    simpa using translation_period_nat F k 1 hF1 2
  have hh : defect (2*m) f ∣[k] translation 2=defect (2*m) f := by
    convert translation_period_nat _ k (2/3) (original_period_two_thirds hm hf) 3 using 1; norm_num
  have hg : inverseDefect (2*m) f ∣[k] translation 2=inverseDefect (2*m) f := by
    convert translation_period_nat _ k (2/3) (original_inverse_period hm hf hf2) 3 using 1; norm_num
  have hp : (F ∣[k] P) ∣[k] translation 2=F ∣[k] P := by
    change ((F ∣[k] P)-delta f • F) ∣[k] translation 2=(F ∣[k] P)-delta f • F at hh
    rw [SmallLevelEleven.sub_slash,det_one_smul _ (translation_det _),hF2] at hh
    linear_combination hh
  have hpi : (F ∣[k] P⁻¹) ∣[k] translation 2=F ∣[k] P⁻¹ := by
    change ((F ∣[k] P⁻¹)-delta f • F) ∣[k] translation 2=(F ∣[k] P⁻¹)-delta f • F at hg
    rw [SmallLevelEleven.sub_slash,det_one_smul _ (translation_det _),hF2] at hg
    linear_combination hg
  constructor
  · have hh : (F ∣[k] SpecialLinearGroup.mapGL ℝ Kplus) ∣[k] P=F ∣[k] P := by
      rw [← SlashAction.slash_mul,Kplus_relation,SlashAction.slash_mul,hp]
    have h := congrArg (fun G : ℍ → ℂ => G ∣[k] P⁻¹) hh
    change F ∣[k] SpecialLinearGroup.mapGL ℝ Kplus=F
    simpa only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] using h
  · have hh : (F ∣[k] SpecialLinearGroup.mapGL ℝ Kminus) ∣[k] P⁻¹=F ∣[k] P⁻¹ := by
      rw [← SlashAction.slash_mul,Kminus_relation,SlashAction.slash_mul,hpi]
    have h := congrArg (fun G : ℍ → ℂ => G ∣[k] P) hh
    change F ∣[k] SpecialLinearGroup.mapGL ℝ Kminus=F
    simpa only [← SlashAction.slash_mul,mul_assoc,inv_mul_cancel,mul_one,SlashAction.slash_one] using h

#print axioms original_zero_signed_hecke
#print axioms original_inverse_period
#print axioms original_Kplus_Kminus
end SmallLevelTwentyOneThree
end
end
