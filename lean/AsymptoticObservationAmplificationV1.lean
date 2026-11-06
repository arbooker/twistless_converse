module

public import AsymptoticObservationOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace Filter
open scoped InnerProduct Topology

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def amplified (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (n : ℕ) : H →L[ℂ] H :=
  operator R (((n+1:ℕ):ℂ) • L) hR

theorem amplified_norm_le (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (n : ℕ) : ‖amplified R L hR n‖≤1 :=
  operator_norm_le_one R _ hR

theorem amplified_energy (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (n : ℕ) (x : H) :
    (⟪amplified R L hR n x,x⟫_ℂ).re=
      ‖amplified R L hR n x‖^2+((n+1:ℕ):ℝ)^2*‖L (amplified R L hR n x)‖^2 := by
  rw [amplified,operator_re_inner]
  simp only [smul_apply,norm_smul,Complex.norm_natCast,mul_pow]

theorem amplified_adjoint_bound (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (n : ℕ) (x : J) :
    ‖amplified R L hR n (L.adjoint x)‖≤‖x‖/((n+1:ℕ):ℝ) := by
  let y := amplified R L hR n (L.adjoint x)
  let a : ℝ := (n+1:ℕ)
  have ha : 0<a := by dsimp [a]; positivity
  have he := amplified_energy R L hR n (L.adjoint x)
  have hi := congrArg Complex.re (L.adjoint_inner_right y x)
  have hc := re_inner_le_norm (𝕜:=ℂ) (L y) x
  change (⟪L y,x⟫_ℂ).re≤‖L y‖*‖x‖ at hc
  have hb : ‖y‖^2+a^2*‖L y‖^2≤‖L y‖*‖x‖ := by
    change (⟪y,L.adjoint x⟫_ℂ).re=‖y‖^2+a^2*‖L y‖^2 at he
    rw [hi] at he
    linarith
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg a)
  have hs : (a*‖y‖)^2≤‖x‖^2 := by
    nlinarith [sq_nonneg (2*a^2*‖L y‖-‖x‖)]
  have hy : a*‖y‖≤‖x‖ := by nlinarith [norm_nonneg x]
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hy)

theorem amplified_adjoint_tendsto (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (x : J) :
    Tendsto (fun n => amplified R L hR n (L.adjoint x)) atTop (𝓝 0) := by
  have hk : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_atTop.mpr (fun b => eventually_atTop.mpr ⟨b,fun n hn => by omega⟩)
  have ht := (tendsto_inv_atTop_zero.comp hk).const_mul ‖x‖
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun n => amplified_adjoint_bound R L hR n x)
  simpa only [div_eq_mul_inv,Function.comp_def] using ht

omit [CompleteSpace H] in
theorem reconstruction_range_closed (R : G →L[ℂ] H) (hR : ∀ g,‖g‖≤‖R g‖) :
    IsClosed (R.range : Set H) := by
  have ha : AntilipschitzWith 1 R := R.antilipschitz_of_bound (by simpa using hR)
  exact ha.isClosed_range R.uniformContinuous

theorem amplified_fixes (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (n : ℕ) {x : H} (hx : x∈R.range⊓L.ker) :
    amplified R L hR n x=x := by
  obtain ⟨g,hg⟩ := hx.1
  subst x
  apply operator_fixes
  have hz : L (R g)=0 := hx.2
  simp only [smul_apply,hz,smul_zero]

theorem amplified_zero_of_orthogonal (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (n : ℕ) {x : H} (hx : x∈R.rangeᗮ) :
    amplified R L hR n x=0 := by
  have hz : R.adjoint x=0 := by
    rw [ContinuousLinearMap.orthogonal_range] at hx
    exact hx
  simp only [amplified,operator_apply,hz,map_zero]

#print axioms amplified_norm_le
#print axioms amplified_energy
#print axioms amplified_adjoint_bound
#print axioms amplified_adjoint_tendsto
#print axioms reconstruction_range_closed
#print axioms amplified_fixes
#print axioms amplified_zero_of_orthogonal

end AsymptoticObservation
