module

public import AsymptoticCongruenceGeneratorsV1
public import AsymptoticCompactTranslationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceStrip

open Matrix UpperHalfPlane AsymptoticCongruenceLabels
open AsymptoticRationalBranches AsymptoticRationalFreeness AsymptoticIntegralSubgroup
open AsymptoticCompactTranslation AsymptoticMassTransport
open scoped MatrixGroups

/-- The congruence subgroup inside the actual projective orbit group.
In particular the two scalar representatives of an integral matrix are
not counted twice. -/
noncomputable def gamma (N : ℕ) : Subgroup AsymptoticRationalGroup.Group :=
  (CongruenceSubgroup.Gamma0 N).map integralLabel

theorem integralLabel_action (A : SL(2,ℤ)) (z : ℍ) : integralLabel A • z=A • z := by
  change ofMatrix (rationalGL A) (rationalGL_positive A) • z=_
  rw [ofMatrix_action,ModularGroup.sl_moeb]
  congr 1
  apply Units.ext
  ext i j
  change ((A.val i j:ℚ):ℝ)=(A.val i j:ℝ)
  simp

noncomputable def representative {N : ℕ} (g : gamma N) : SL(2,ℤ) :=
  (Subgroup.mem_map.mp g.property).choose

theorem representative_mem {N : ℕ} (g : gamma N) :
    representative g∈CongruenceSubgroup.Gamma0 N :=
  (Subgroup.mem_map.mp g.property).choose_spec.1

theorem representative_label {N : ℕ} (g : gamma N) :
    integralLabel (representative g)=g.val :=
  (Subgroup.mem_map.mp g.property).choose_spec.2

theorem translation_mem (N : ℕ) (n : ℤ) : translationLabel (n:ℚ)∈gamma N := by
  apply Subgroup.mem_map.mpr
  refine ⟨upperSL n,?_,upper_label n⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [upperSL,AsymptoticFreshCRT.upper]

theorem translation_re (n : ℤ) (z : ℍ) :
    (translationLabel (n:ℚ) • z).re=z.re+(n:ℝ) := by
  rw [label_action]
  have h := congrArg Complex.re (AsymptoticMobiusFold.translation_action (n:ℝ) z)
  simpa using h

theorem translation_eq_zero {x y : ℍ} (hx : x∈strip) (hy : y∈strip)
    (n : ℤ) (h : x=translationLabel (n:ℚ) • y) : n=0 := by
  have hx0 : Int.floor x.re=0 := Int.floor_eq_zero_iff.mpr hx
  have hy0 : Int.floor y.re=0 := Int.floor_eq_zero_iff.mpr hy
  have he := congrArg (fun z : ℍ => Int.floor z.re) h
  rw [translation_re,Int.floor_add_intCast,hx0,hy0] at he
  omega

/-- The strip picks one translation representative. Its chosen integral
matrix has a lower row that distinguishes all such representatives. -/
def Strip (N : ℕ) (z : ℍ) := {g : gamma N // g.val • z∈strip}

noncomputable def bottom {N : ℕ} {z : ℍ} (g : Strip N z) : Fin 2 → ℤ :=
  (representative g.val).val 1

set_option backward.isDefEq.respectTransparency false in
theorem bottom_injective (N : ℕ) (z : ℍ) :
    Function.Injective (bottom (N:=N) (z:=z)) := by
  intro g h he
  let A := representative g.val
  let B := representative h.val
  have h0 : A.val 1 0=B.val 1 0 := congrFun he 0
  have h1 : A.val 1 1=B.val 1 1 := congrFun he 1
  have hc : (A*B⁻¹) 1 0=0 := by
    change (A.val*(B⁻¹).val) 1 0=0
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,h0,h1]
    ring
  obtain ⟨n,hn⟩ := triangular_label (A*B⁻¹) hc
  have hg : g.val.val=translationLabel (n:ℚ)*h.val.val := by
    have he' := congrArg (fun a => a*integralLabel B) hn
    simpa only [map_mul,map_inv,inv_mul_cancel_right,
      A,B,representative_label] using he'
  have hz : g.val.val • z=translationLabel (n:ℚ) • (h.val.val • z) := by
    rw [hg,mul_smul]
  have hn0 := translation_eq_zero g.property h.property n hz
  have hzero : translationLabel (0:ℚ)=1 := by
    have hu : upperSL 0=1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperSL,AsymptoticFreshCRT.upper]
    simpa only [Int.cast_zero,hu,map_one] using (upper_label 0).symm
  exact Subtype.ext (Subtype.ext (by simpa only [hn0,Int.cast_zero,hzero,one_mul] using hg))

#print axioms integralLabel_action
#print axioms representative_mem
#print axioms representative_label
#print axioms translation_mem
#print axioms translation_re
#print axioms translation_eq_zero
#print axioms bottom_injective

end AsymptoticCongruenceStrip
