module

public import QuantitativeArithmeticSmallLevelThirteenPoleV1
public import SmallLevelDoubleCosetDefectEigenV1
public import SmallLevelMellinEndpointTheoryV4
public import SmallLevelTranslatedRayDecayV1
public import SmallLevelTwentySixEllipticV1

/-! Consolidated chapter: SmallLevelTwentySix. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixHalfTurnV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm Manifold

def halfTurn : GL (Fin 2) ℝ := matrix (-5) 1 (-26) 5 (by norm_num)

theorem P_square : P*P=halfTurn := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P,halfTurn,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne] <;> nlinarith

theorem halfTurn_square : halfTurn*halfTurn=(-1 : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfTurn,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]

theorem halfTurn_hyperM : halfTurn*hyperM=hyperY*halfTurn := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [halfTurn,hyperM,hyperY,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- The symmetric part of the defect vanishes by the infinite-order
elliptic word M*P. This is an analytic consequence of the original first
hyperbolic law and the order-four relation of P. -/
theorem defect_halfTurn (m : ℕ) (hm : 0<m) (F : ℍ → ℂ) (hhol : MDiff F)
    (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (hM : ((F ∣[((2*m:ℕ):ℤ)] P)-δ • F) ∣[((2*m:ℕ):ℤ)] hyperM=
      (F ∣[((2*m:ℕ):ℤ)] P)-δ • F) :
    ((F ∣[((2*m:ℕ):ℤ)] P)-δ • F) ∣[((2*m:ℕ):ℤ)] halfTurn=
      -((F ∣[((2*m:ℕ):ℤ)] P)-δ • F) := by
  let k : ℤ := ((2*m:ℕ):ℤ)
  let h := (F ∣[k] P)-δ • F
  let w := h+(h ∣[k] halfTurn)
  change h ∣[k] hyperM=h at hM
  have hY : h ∣[k] hyperY=h := by
    have he : hyperY=hyperM⁻¹ := (eq_inv_iff_mul_eq_one).mpr hyperY_mul_M
    rw [he]
    have hh := congrArg (fun J : ℍ → ℂ => J ∣[k] hyperM⁻¹) hM
    simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using hh.symm
  have hwM : w ∣[k] hyperM=w := by
    dsimp [w]
    rw [SlashAction.add_slash,hM,← SlashAction.slash_mul,halfTurn_hyperM,
      SlashAction.slash_mul,hY]
  have hfour : (((F ∣[k] P) ∣[k] P) ∣[k] P) ∣[k] P=F := by
    rw [← SlashAction.slash_mul k P P,P_square,
      ← SlashAction.slash_mul k P P,P_square,
      ← SlashAction.slash_mul,halfTurn_square]
    exact central_even F m
  have hwP : w ∣[k] P=(-δ) • w := by
    dsimp [w,h]
    simp only [← P_square]
    simp only [SlashAction.add_slash,SmallLevelEleven.sub_slash,
      SlashAction.slash_mul,det_one_smul _ P_det]
    rcases hδ with rfl|rfl <;>
      simp only [one_smul,neg_one_smul,neg_neg,hfour] <;> abel
  have hw : w=0 := by
    refine elliptic_word_eigen_zero (by omega : 0<2*m) w ?_ (-δ) ?_ ?_
    · have hh : MDiff h := (hhol.slash k P).sub (mdifferentiable_const.mul hhol)
      exact hh.add (hh.slash k halfTurn)
    · rcases hδ with rfl|rfl <;> simp
    · rw [SlashAction.slash_mul,hwM,hwP]
  change h ∣[k] halfTurn= -h
  change h+(h ∣[k] halfTurn)=0 at hw
  linear_combination hw

theorem original_halfTurn (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f)
      ∣[((2*m:ℕ):ℤ)] halfTurn=
      -((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f) :=
  defect_halfTurn m hm _ (fourierFunction_holomorphic hf) _ (root_unit hf.toEulerData 2)
    (original_hyperM m hf)

#print axioms original_halfTurn
end SmallLevelTwentySix
end
end

/-! ## SmallLevelTwentySixSecondHyperbolicV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm Manifold

def Wi : GL (Fin 2) ℝ := matrix 0 (1/Real.sqrt 26) (-Real.sqrt 26) 0 (by
  field_simp [sqrt_level_ne]
  norm_num)

theorem Wi_det : (GeneralLinearGroup.det Wi:ℝ)=1 := matrix_det _ _ _ _ _

theorem Wi_inverse : Wi=(fricke 26 (by decide))⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Wi,fricke,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [sqrt_level_ne]

def partnerK : GL (Fin 2) ℝ := Pi*Wi*translation (-1/2)

theorem partnerK_det : (GeneralLinearGroup.det partnerK:ℝ)=1 := by
  simp only [partnerK,map_mul,Units.val_mul,Pi_det,Wi_det,translation_det,one_mul]

theorem Q_double_coset : Q=((-1 : GL (Fin 2) ℝ)*Wi)*P⁻¹*Wi := by
  rw [← P_inverse]
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q,Pi,Wi,matrix,GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne,sqrt_level_ne] <;> norm_num [hs,ht]

theorem partnerK_branch : partnerK*translation (1/4)=P⁻¹*Wi*translation (-(1/4)) := by
  rw [partnerK,P_inverse,mul_assoc,translation_mul]
  norm_num

theorem second_hyperbolic_factor :
    (partnerK*halfTurn)*(partnerK*halfTurn)=hyperZSquare := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 26)^2=26 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partnerK,Pi,Wi,translation,halfTurn,hyperZSquare,matrix,
      GeneralLinearGroup.mkOfDetNeZero,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [sqrt_two_ne,sqrt_level_ne] <;> norm_num [hs,ht]

theorem original_partnerK (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
    ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f)
      ∣[((2*m:ℕ):ℤ)] partnerK=
      χ • ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f) := by
  let F:=fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  let δ:=root 26 f 2
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<26) m hf
  have hWi : F ∣[k] Wi=η • F := by
    rw [Wi_inverse]
    have hh:=congrArg (fun J : ℍ→ℂ => J ∣[k] (fricke 26 (by decide))⁻¹) hW
    rw [det_one_smul _ (det_one_inv _ (fricke_det _ _)),
      ← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] at hh
    rcases hη with rfl|rfl
    · simpa only [one_smul] using hh.symm
    · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm
  have hL : F ∣[k] ((-1 : GL (Fin 2) ℝ)*Wi)=η • F := by
    rw [SlashAction.slash_mul,central_even,hWi]
  have hp : ((F ∣[k] P) ∣[k] translation (1/4))+
      ((F ∣[k] Q) ∣[k] translation (-(1/4)))=
      δ • ((F ∣[k] translation (1/4))+(F ∣[k] translation (-(1/4)))) := by
    have hh:=congrArg (fun J : ℍ→ℂ => J ∣[k] translation (1/4)) (original_reduced4 hf)
    dsimp only [k] at hh ⊢
    rw [SlashAction.add_slash,det_one_smul _ (translation_det _),SlashAction.add_slash] at hh
    simp only [← SlashAction.slash_mul,mul_assoc,translation_mul,
      show (-1/2:ℝ)+1/4= -(1/4) by ring] at hh
    simpa only [SlashAction.slash_mul] using hh
  have hδ : δ=1 ∨ δ= -1:=root_unit hf.toEulerData 2
  refine ⟨η*δ,?_,?_⟩
  · rcases hη with rfl|rfl <;> rcases hδ with h|h <;> simp [h]
  · exact double_coset_defect_eigen F k P Q ((-1)*Wi) Wi partnerK
      Wi_det P_det η δ hη hδ hL hWi Q_double_coset (1/4) partnerK_branch hp

theorem original_hyperZSquare (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f)
      ∣[((2*m:ℕ):ℤ)] hyperZSquare=
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f := by
  let k : ℤ:=((2*m:ℕ):ℤ)
  let h:=(fourierFunction (2*m) f ∣[k] P)-root 26 f 2 • fourierFunction (2*m) f
  obtain ⟨χ,hχ,hK⟩:=original_partnerK m hf
  have hP:=original_halfTurn m hm hf
  change h ∣[k] partnerK=χ • h at hK
  change h ∣[k] halfTurn= -h at hP
  change h ∣[k] hyperZSquare=h
  rw [← second_hyperbolic_factor]
  simp only [SlashAction.slash_mul]
  rcases hχ with rfl|rfl <;>
    simp only [one_smul,neg_one_smul] at hK <;>
    simp only [hK,hP,SlashAction.neg_slash,neg_neg]

/-- Original-input classification, with both hyperbolic symmetries derived
from the supplied functional equations and no extra modularity premise. -/
theorem original_defect_classification (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    let h := (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f
    ∃ C : ℂ, ∀ z : ℍ, (z:ℂ)^m*(h ∣[((2*m:ℕ):ℤ)] axisP) z=C := by
  apply hyperbolic_classification
  · have hh:=fourierFunction_holomorphic hf
    exact (hh.slash ((2*m:ℕ):ℤ) P).sub (mdifferentiable_const.mul hh)
  · exact original_hyperM m hf
  · exact original_hyperZSquare m hm hf

#print axioms original_defect_classification
end SmallLevelTwentySix
end
end

/-! ## SmallLevelTwentySixDefectModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open QuantitativeArithmeticSmallLevelThirteen (branchQuadratic classified_slash)
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm Manifold

def axisInverse : GL (Fin 2) ℝ :=
  matrix 1 (-((13-Real.sqrt 13)/52)) (-26/Real.sqrt 13)
    ((13+Real.sqrt 13)/(2*Real.sqrt 13)) (by
      have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp
      ring)

theorem axis_inverse : axisP*axisInverse=1 := by
  have hn : Real.sqrt 13≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisP,axisInverse,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [hn] <;> ring

/-- The two real hyperbolic endpoints are roots of this rational quadratic. -/
def defectQuadratic (z : ℂ) : ℂ := z^2-z/2+3/52

theorem branch_quadratic (z : ℂ) :
    (-(Real.sqrt 13:ℂ)/26)*branchQuadratic axisInverse z=defectQuadratic z := by
  have hs : (Real.sqrt 13:ℂ)^2=13 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤13)
  have hn : (Real.sqrt 13:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  change (-(Real.sqrt 13:ℂ)/26)*
    ((1*z+((-((13-Real.sqrt 13)/52):ℝ):ℂ))*
      (((-26/Real.sqrt 13:ℝ):ℂ)*z+(((13+Real.sqrt 13)/(2*Real.sqrt 13):ℝ):ℂ)))=
    z^2-z/2+3/52
  push_cast
  field_simp [hn]
  ring_nf
  simp only [hs]
  ring

theorem classification_model (m : ℕ) (h : ℍ→ℂ) (C : ℂ)
    (hC : ∀ z : ℍ, (z:ℂ)^m*(h ∣[((2*m:ℕ):ℤ)] axisP) z=C) :
    ∀ z : ℍ, defectQuadratic z^m*h z=(-(Real.sqrt 13:ℂ)/26)^m*C := by
  intro z
  have hh:=classified_slash m (h ∣[((2*m:ℕ):ℤ)] axisP) C hC axisInverse
    (matrix_det _ _ _ _ _) z
  rw [← SlashAction.slash_mul,axis_inverse,SlashAction.slash_one] at hh
  rw [← branch_quadratic,mul_pow,mul_assoc,hh]

/-- The original level-26 defect is an explicit rational-quadratic model.
Its scalar still has to be killed using the additive Mellin pole restriction. -/
theorem original_defect_model (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ C : ℂ, ∀ z : ℍ, defectQuadratic z^m*
      (((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-
        root 26 f 2 • fourierFunction (2*m) f) z)=C := by
  obtain ⟨C,hC⟩:=original_defect_classification m hm hf
  exact ⟨(-(Real.sqrt 13:ℂ)/26)^m*C,classification_model m _ C hC⟩

#print axioms original_defect_model
end SmallLevelTwentySix
end
end

/-! ## SmallLevelTwentySixEvenHalfWeightV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm

theorem halfTurn_det : (GeneralLinearGroup.det halfTurn:ℝ)=1 := matrix_det _ _ _ _ _

theorem quadratic_halfTurn (z : ℍ) :
    defectQuadratic ((halfTurn • z:ℍ):ℂ)*(denom halfTurn z)^2= -defectQuadratic z := by
  have hd:=denom_ne_zero halfTurn z
  rw [coe_smul_of_det_pos (by rw [halfTurn_det]; norm_num)]
  change defectQuadratic (num halfTurn z/denom halfTurn z)*(denom halfTurn z)^2= _
  unfold defectQuadratic
  field_simp [hd]
  norm_num [num,denom,halfTurn,matrix,GeneralLinearGroup.mkOfDetNeZero]
  ring

theorem defectQuadratic_ne_zero (z : ℍ) : defectQuadratic z≠0 := by
  intro h
  have hr:=congrArg Complex.re h
  have hi:=congrArg Complex.im h
  norm_num [defectQuadratic,pow_two,Complex.mul_re,Complex.mul_im,Complex.div_re,
    Complex.div_im,Complex.normSq] at hr hi
  have hzre : z.re=1/4 := by nlinarith [z.im_pos]
  rw [hzre] at hr
  nlinarith [sq_nonneg z.im]

/-- The half-turn acts on the classified quadratic model by (-1)^m.
Its original eigenvalue is -1, forcing the scalar to vanish for even m. -/
theorem model_scalar_parity (m : ℕ) (h : ℍ→ℂ) (C : ℂ)
    (hC : ∀ z : ℍ,defectQuadratic z^m*h z=C)
    (hh : h ∣[((2*m:ℕ):ℤ)] halfTurn= -h) : C= -((-1:ℂ)^m)*C := by
  let z : ℍ:=⟨Complex.I,by norm_num⟩
  have hd:=denom_ne_zero halfTurn z
  have hs:=congrFun hh z
  rw [det_one_slash _ halfTurn_det,zpow_neg,zpow_natCast] at hs
  simp only [Pi.neg_apply] at hs
  have he : h (halfTurn • z)= -h z*(denom halfTurn z)^(2*m) := by
    have hmul:=congrArg (fun v : ℂ => v*(denom halfTurn z)^(2*m)) hs
    simpa only [mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hd),mul_one] using hmul
  have hq:=congrArg (fun v : ℂ => v^m) (quadratic_halfTurn z)
  rw [mul_pow,neg_pow,←pow_mul] at hq
  calc
    C=defectQuadratic ((halfTurn • z:ℍ):ℂ)^m*h (halfTurn • z) := (hC _).symm
    _= -(defectQuadratic ((halfTurn • z:ℍ):ℂ)^m*(denom halfTurn z)^(2*m))*h z := by
      rw [he]
      ring
    _= -((-1:ℂ)^m*defectQuadratic z^m)*h z := by rw [hq]
    _= -((-1:ℂ)^m)*C := by rw [neg_mul,mul_assoc,hC z]; ring

/-- At weights divisible by four, the P transformation already follows
from the original algebraic/holomorphic defect classification. -/
theorem original_P_even_half_weight (m : ℕ) (hm : 0<m) (heven : Even m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=root 26 f 2 • fourierFunction (2*m) f := by
  obtain ⟨C,hC⟩:=original_defect_model m hm hf
  have hp:=model_scalar_parity m _ C hC (original_halfTurn m hm hf)
  have he : (-1:ℂ)^m=1 := heven.neg_one_pow
  rw [he] at hp
  have hzero : C=0 := by linear_combination (1/2:ℂ)*hp
  apply sub_eq_zero.mp
  funext z
  have hz:=hC z
  rw [hzero] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero m (defectQuadratic_ne_zero z))

#print axioms quadratic_halfTurn
#print axioms defectQuadratic_ne_zero
#print axioms model_scalar_parity
#print axioms original_P_even_half_weight
end SmallLevelTwentySix
end
end

/-! ## SmallLevelTwentySixVerticalTransportV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm

/-- The vertical line through -d/c for P. -/
def vertical (y : ℝ) (hy : 0<y) : ℍ := ⟨(3/13:ℂ)+(y:ℂ)*Complex.I,by simpa⟩

theorem vertical_denom (y : ℝ) (hy : 0<y) :
    denom P (vertical y hy)=(26/(Real.sqrt 2:ℂ))*(y:ℂ)*Complex.I := by
  norm_num [vertical,denom,P,matrix,GeneralLinearGroup.mkOfDetNeZero]
  ring

/-- Exact vertical transport, without an asymptotic change of path. -/
theorem vertical_point (y : ℝ) (hy : 0<y) :
    ((P • vertical y hy:ℍ):ℂ)=(2/13:ℂ)+Complex.I/(338*(y:ℂ)) := by
  have hys : (y:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hy.ne'
  have hs : (Real.sqrt 2:ℂ)≠0:=Complex.ofReal_ne_zero.mpr sqrt_two_ne
  rw [coe_smul_of_det_pos (by rw [P_det]; norm_num)]
  norm_num [vertical,num,denom,P,matrix,GeneralLinearGroup.mkOfDetNeZero]
  field_simp [hys,hs]
  ring_nf; norm_num [Complex.I_sq]
  field_simp [hys]
  ring_nf; norm_num [Complex.I_sq]

/-- The quadratic model on the exact vertical transport line. -/
theorem vertical_quadratic (y : ℝ) (hy : 0<y) :
    defectQuadratic (vertical y hy)= -(y:ℂ)^2-(y:ℂ)/26*Complex.I-3/676 := by
  norm_num [defectQuadratic,vertical,pow_two]
  ring_nf; norm_num [Complex.I_sq]; ring

/-- Original input determines the transported function up to the already
classified scalar. The scalar is not assumed to vanish here. -/
theorem original_vertical_transport (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ C : ℂ, ∀ (y : ℝ) (hy : 0<y),
      fourierFunction (2*m) f (P • vertical y hy)=
        (denom P (vertical y hy))^(2*m)*
          (root 26 f 2*fourierFunction (2*m) f (vertical y hy)+
            C/(defectQuadratic (vertical y hy))^m) := by
  obtain ⟨C,hC⟩:=original_defect_model m hm hf
  refine ⟨C,fun y hy => ?_⟩
  let z:=vertical y hy
  have hd:=pow_ne_zero (2*m) (denom_ne_zero P z)
  have hq:=pow_ne_zero m (defectQuadratic_ne_zero z)
  have h:=hC z
  rw [Pi.sub_apply,det_one_slash _ P_det,zpow_neg,zpow_natCast,Pi.smul_apply,smul_eq_mul] at h
  change fourierFunction (2*m) f (P • z)=denom P z^(2*m)*
    (root 26 f 2*fourierFunction (2*m) f z+C/defectQuadratic z^m)
  field_simp [hd,hq] at h ⊢
  linear_combination h

#print axioms vertical_point
#print axioms vertical_quadratic
#print axioms original_vertical_transport
end SmallLevelTwentySix
end
end

/-! ## SmallLevelTwentySixBoundaryFormulaV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm

def boundaryDenominator (t : ℂ) : ℂ := 1+13*t*Complex.I+507*t^2

theorem boundaryDenominator_zero : boundaryDenominator 0=1 := by norm_num [boundaryDenominator]
theorem boundaryDenominator_entire : Differentiable ℂ boundaryDenominator := by
  unfold boundaryDenominator
  fun_prop

/-- The exact rational model factor on the ray approaching 2/13. -/
theorem boundary_factor (t : ℝ) (ht : 0<t) :
    (denom P (vertical (1/(338*t)) (by positivity)))^2*boundaryDenominator t=
      338*defectQuadratic (vertical (1/(338*t)) (by positivity)) := by
  have ht0 : (t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ht.ne'
  have hs0 : (Real.sqrt 2:ℂ)≠0:=Complex.ofReal_ne_zero.mpr sqrt_two_ne
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rw [vertical_denom,vertical_quadratic]
  unfold boundaryDenominator
  push_cast
  field_simp [ht0,hs0]
  ring_nf
  simp [hs,Complex.I_sq]
  ring

theorem transport_of_model (m : ℕ) (F : ℍ→ℂ) (δ C : ℂ)
    (hC : ∀ z : ℍ,defectQuadratic z^m*((F ∣[((2*m:ℕ):ℤ)] P)-δ • F) z=C)
    (z : ℍ) : F (P • z)=denom P z^(2*m)*(δ*F z+C/defectQuadratic z^m) := by
  have hd:=pow_ne_zero (2*m) (denom_ne_zero P z)
  have hq:=pow_ne_zero m (defectQuadratic_ne_zero z)
  have h:=hC z
  rw [Pi.sub_apply,det_one_slash _ P_det,zpow_neg,zpow_natCast,Pi.smul_apply,smul_eq_mul] at h
  field_simp [hd,hq] at h ⊢
  linear_combination h

/-- The classified scalar is exactly the constant term of the transported
boundary expansion, up to the nonzero factor 338^m. -/
theorem original_boundary_formula (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ C : ℂ, (∀ z : ℍ,defectQuadratic z^m*
      ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f) z=C) ∧
      ∀ (t : ℝ) (ht : 0<t),
      let z:=vertical (1/(338*t)) (by positivity)
      boundaryDenominator t^m*fourierFunction (2*m) f (P • z)=
        boundaryDenominator t^m*(denom P z)^(2*m)*
          (root 26 f 2*fourierFunction (2*m) f z)+(338:ℂ)^m*C := by
  obtain ⟨C,hC⟩:=original_defect_model m hm hf
  refine ⟨C,hC,fun t ht => ?_⟩
  let z:=vertical (1/(338*t)) (by positivity)
  have hq:=pow_ne_zero m (defectQuadratic_ne_zero z)
  have hp:=congrArg (fun v : ℂ => v^m) (boundary_factor t ht)
  rw [mul_pow,mul_pow,← pow_mul] at hp
  have he : boundaryDenominator t^m*(denom P z)^(2*m)=
      (338:ℂ)^m*defectQuadratic z^m := by
    change (denom P z)^(2*m)*boundaryDenominator t^m=
      (338:ℂ)^m*defectQuadratic z^m at hp
    exact (mul_comm _ _).trans hp
  change boundaryDenominator t^m*fourierFunction (2*m) f (P • z)=_
  rw [transport_of_model m _ _ C hC z]
  calc
    _ = boundaryDenominator t^m*(denom P z)^(2*m)*
        (root 26 f 2*fourierFunction (2*m) f z)+
        (boundaryDenominator t^m*(denom P z)^(2*m))*(C/defectQuadratic z^m) := by ring
    _ = _ := by
      rw [he]
      field_simp [hq]
      ring

#print axioms boundary_factor
#print axioms original_boundary_formula
end SmallLevelTwentySix
end
end

/-! ## SmallLevelTwentySixBoundaryDecayV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct Filter Asymptotics
open scoped MatrixGroups ModularForm Topology

theorem boundaryDenominator_real_ne_zero (t : ℝ) : boundaryDenominator t≠0 := by
  intro h
  have hi:=congrArg Complex.im h
  norm_num [boundaryDenominator,pow_two,Complex.mul_re,Complex.mul_im] at hi
  have ht : t=0:=by linarith
  simp [ht,boundaryDenominator] at h

theorem small_vertical_point (t : ℝ) (ht : 0<t) :
    ((P • vertical (1/(338*t)) (by positivity):ℍ):ℂ)=(2/13:ℂ)+(t:ℂ)*Complex.I := by
  rw [vertical_point]
  have hn : (t:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ht.ne'
  push_cast
  field_simp [hn]

/-- The rational boundary term differs from its constant term by O(t). -/
theorem rational_boundary_first_order (m : ℕ) (L : ℂ) :
    (fun t : ℝ => L/boundaryDenominator t^m-L)=O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)) := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => L/boundaryDenominator z^m) 0 :=
    (differentiableAt_const L).div (boundaryDenominator_entire.differentiableAt.pow m)
      (by simp [boundaryDenominator])
  have ht : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hh:=hd.isBigO_sub.comp_tendsto ht
  have hc : (fun t : ℝ => (t:ℂ))=O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with t
    simp
  have hsimple : (fun t : ℝ => L/boundaryDenominator t^m-L)=O[𝓝[>] 0] (fun t : ℝ => (t:ℂ)) := by
    simpa only [Function.comp_def,boundaryDenominator_zero,one_pow,div_one,sub_zero] using hh
  exact hsimple.trans hc

/-- The original model has the exact constant endpoint 338^m C at 2/13,
with a first-order remainder. This is an estimate on the original Fourier
function and does not assume its additive Mellin continuation. -/
theorem original_boundary_first_order (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ C : ℂ, (∀ z : ℍ,defectQuadratic z^m*
      ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P)-root 26 f 2 • fourierFunction (2*m) f) z=C) ∧
      (fun t : ℝ => FinitenessFourierConstruction.fourier
        (FinitenessOriginalFourier.fullCoefficients f (2*m)) ((2/13:ℂ)+(t:ℂ)*Complex.I)-
        (338:ℂ)^m*C)=O[𝓝[>] 0] (fun t : ℝ => t^(1:ℝ)) := by
  obtain ⟨C,hC,hform⟩:=original_boundary_formula m hm hf
  refine ⟨C,hC,?_⟩
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  let K : ℂ:=((26/(Real.sqrt 2:ℂ))*Complex.I)^(2*m)*root 26 f 2
  let L : ℂ:=(338:ℂ)^m*C
  have hw:=SmallLevelTranslatedRay.inverted_weighted_first_order ha ha0 (2*m) (3/13)
    (by norm_num : (0:ℝ)<338)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hw
  have hmain:=(hw.const_mul_left K).add (rational_boundary_first_order m L)
  apply hmain.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0<t:=ht
  let z:=vertical (1/(338*t)) (by positivity)
  have hq:=pow_ne_zero m (boundaryDenominator_real_ne_zero t)
  have he:=hform t ht0
  change boundaryDenominator t^m*fourierFunction (2*m) f (P • z)=
    boundaryDenominator t^m*(denom P z)^(2*m)*
      (root 26 f 2*fourierFunction (2*m) f z)+L at he
  have hfz : fourierFunction (2*m) f z=FinitenessFourierConstruction.fourier a
      ((3/13:ℂ)+((1/(338*t):ℝ):ℂ)*Complex.I) := rfl
  have hfp : fourierFunction (2*m) f (P • z)=FinitenessFourierConstruction.fourier a
      ((2/13:ℂ)+(t:ℂ)*Complex.I) := by
    change FinitenessFourierConstruction.fourier a ((P • z:ℍ):ℂ)=_
    dsimp only [z]
    rw [small_vertical_point t ht0]
  have hweight : (denom P z)^(2*m)*(root 26 f 2*fourierFunction (2*m) f z)=
      K*((((1/(338*t):ℝ):ℂ)^(2*m))*FinitenessFourierConstruction.fourier a
        ((3/13:ℂ)+((1/(338*t):ℝ):ℂ)*Complex.I)) := by
    rw [hfz]
    change (denom P (vertical (1/(338*t)) _))^(2*m)*_= _
    rw [vertical_denom]
    dsimp only [K]
    simp only [mul_pow]
    ring
  rw [hfp,show boundaryDenominator t^m*(denom P z)^(2*m)*
      (root 26 f 2*fourierFunction (2*m) f z)=boundaryDenominator t^m*
        ((denom P z)^(2*m)*(root 26 f 2*fourierFunction (2*m) f z)) by ring,hweight] at he
  change K*(_*FinitenessFourierConstruction.fourier a _)+(L/boundaryDenominator t^m-L)=
    FinitenessFourierConstruction.fourier a _-L
  push_cast at he ⊢
  apply (mul_right_cancel₀ hq)
  simp only [add_mul,sub_mul,div_mul_cancel₀ _ hq]
  linear_combination -he

#print axioms rational_boundary_first_order
#print axioms original_boundary_first_order
end SmallLevelTwentySix
end
end

/-! ## SmallLevelTwentySixRegularEndpointV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct Filter Asymptotics
open scoped MatrixGroups ModularForm Topology

/-- Conditional analytic endgame at a single point. The original model
scalar vanishes if the additive continuation at 2/13 is regular at zero.
Constructing that continuation and proving regularity remain separate. -/
theorem original_P_of_regular_endpoint (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (A : ℂ→ℂ) (B : ℝ)
    (hmer : ∀ s,MeromorphicAt A s) (hA : AnalyticAt ℂ A 0)
    (hagrees : ∀ s : ℂ,B<s.re → A s=SmallLevelAdditive.original (2*m) f (2/13) s) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=root 26 f 2 • fourierFunction (2*m) f := by
  obtain ⟨C,hC,hzero⟩:=original_boundary_first_order m hm hf
  obtain ⟨τ,_,hg⟩:=hf.growth
  have ha:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hL : (338:ℂ)^m*C=0 :=
    SmallLevelMellinEndpoint.fourier_endpoint_zero ha ha0 (2/13) ((338:ℂ)^m*C) A B
      (by simpa only [SmallLevelMellinEndpoint.ray,Complex.ofReal_div,Complex.ofReal_ofNat] using hzero)
      hmer hA.continuousAt hagrees
  have hc : C=0:=(mul_eq_zero.mp hL).resolve_left (pow_ne_zero _ (by norm_num))
  apply sub_eq_zero.mp
  funext z
  have hz:=hC z
  rw [hc] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (defectQuadratic_ne_zero z))

#print axioms original_P_of_regular_endpoint
end SmallLevelTwentySix
end
end
