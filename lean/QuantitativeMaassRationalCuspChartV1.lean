module

public import QuantitativeSpectralExceptionalGeometryTriangularV1
public import QuantitativeMaassNormalizerActionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Matrix UpperHalfPlane AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticClassicalDiscriminant AsymptoticRegularBranchFamily
open QuantitativeSpectralExceptionalReducedRows QuantitativeSpectralExceptionalGeometry
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open scoped MatrixGroups
namespace QuantitativeMaass

/-- Rational cusp coordinates with integral numerator and denominator retained. -/
theorem branch_rational_affine_chart (b : Branch) :
    ∃ (U : SL(2,ℤ)) (a c d : ℤ) (ha : 0<a) (hd : 0<d),
      ∀ z : ℍ, label b • z = U • affine ((a:ℝ)/d)
        (div_pos (by exact_mod_cast ha) (by exact_mod_cast hd)) ((c:ℝ)/d) z := by
  obtain ⟨U,a,c,d,ha,hd,he⟩ := integral_triangular b.matrix.val.num
    (branch_numerator_positive b)
  let D : ℝ := b.matrix.val.den
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.pos_of_ne_zero b.matrix.val.den_ne_zero
  have ha' : 0 < (a:ℝ)/D := div_pos (by exact_mod_cast ha) hD
  have hd' : 0 < (d:ℝ)/D := div_pos (by exact_mod_cast hd) hD
  have hmat : realMatrix b.matrix = SpecialLinearGroup.mapGL ℝ U *
      triangularGL ((a:ℝ)/D) ((c:ℝ)/D) ((d:ℝ)/D) ha' hd' := by
    apply Units.ext
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M i j : ℝ)) he
    have hn : (b.matrix.val.num i j : ℝ) / D = (b.matrix i j : ℝ) := by
      have hq : (b.matrix.val.num i j : ℚ) / (b.matrix.val.den : ℚ) = b.matrix i j :=
        b.matrix.val.num_div_den i j
      have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
      simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hr
    change (b.matrix i j : ℝ) = _
    rw [← hn]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul] at hh
    fin_cases i <;> fin_cases j <;>
      simp [triangularGL,GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply,Fin.sum_univ_two] at hh ⊢ <;> rw [hh] <;> ring
  refine ⟨U,a,c,d,ha,hd,?_⟩
  intro z
  rw [ofMatrix_action,hmat,mul_smul,triangularGL_action]
  simp only [div_div_div_cancel_right₀ hD.ne']
  rfl

/-- Every rational normalizer has a rational affine coordinate formula
at every integral cusp; no cusp transitivity assumption is used. -/
theorem rational_cusp_affine_chart (g : AsymptoticRationalGroup.Group) (s : SL(2,ℤ)) :
    ∃ (U : SL(2,ℤ)) (a b d : ℤ) (ha : 0<a) (hd : 0<d),
      ∀ z : ℍ,g • (s • z)=U • affine ((a:ℝ)/d)
        (div_pos (by exact_mod_cast ha) (by exact_mod_cast hd)) ((b:ℝ)/d) z := by
  let h := g*integralLabel s
  let b : Branch := ⟨AsymptoticSlashGauge.representative h,
    AsymptoticRationalGroup.representative_positive h (AsymptoticSlashGauge.representative_spec h)⟩
  obtain ⟨U,a,c,d,ha,hd,he⟩ := branch_rational_affine_chart b
  refine ⟨U,a,c,d,ha,hd,?_⟩
  intro z
  have hh := he z
  change ofMatrix b.matrix b.positive • z=_ at hh
  rw [ofMatrix_action,AsymptoticSlashGauge.representative_action] at hh
  simpa only [h,mul_smul,integralLabel_action] using hh

#print axioms branch_rational_affine_chart
#print axioms rational_cusp_affine_chart
end QuantitativeMaass
