module

public import QuantitativeMaassOldFilterContractionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
open scoped InnerProductSpace
namespace QuantitativeMaass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An explicit energy loss for the average of two complementary
orthogonal projections, valid also in infinite dimension. -/
theorem two_projection_filter_energy (P Q : E→ₗ[ℂ]E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q) (v : E) :
    ‖(1-(1/2:ℂ) • (P+Q)) v‖^2 ≤
      ‖v‖^2-(‖P v‖^2+‖Q v‖^2)/2 := by
  have hsum : ‖P v+Q v‖^2 ≤ 2*(‖P v‖^2+‖Q v‖^2) := by
    have h := norm_add_le (P v) (Q v)
    have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith only [hs,sq_nonneg (‖P v‖-‖Q v‖)]
  have hi : (inner ℂ v (P v+Q v)).re=‖P v‖^2+‖Q v‖^2 := by
    have hc : (inner ℂ v (P v+Q v)).re=(inner ℂ (P v+Q v) v).re :=
      inner_re_symm (𝕜:=ℂ) v (P v+Q v)
    rw [hc,inner_add_left,Complex.add_re,
      symmetric_idempotent_inner P hP hPP v,symmetric_idempotent_inner Q hQ hQQ v]
  change ‖v-(1/2:ℂ) • (P v+Q v)‖^2 ≤ _
  rw [norm_sub_sq (𝕜:=ℂ),inner_smul_right,norm_smul]
  have hn : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  have hr : ((1/2:ℂ)*inner ℂ v (P v+Q v)).re=
      (1/2:ℝ)*(inner ℂ v (P v+Q v)).re := by
    simp only [Complex.mul_re]; norm_num
  rw [hn]
  change ‖v‖^2-2*((1/2:ℂ)*inner ℂ v (P v+Q v)).re+
    ((1/2:ℝ)*‖P v+Q v‖)^2 ≤ _
  rw [hr,hi]
  nlinarith only [hsum]

/-- A coercive old-projection estimate yields geometric decay of the
same polynomial on any invariant subspace where the estimate holds. -/
theorem two_projection_filter_power_gap (P Q : E→ₗ[ℂ]E)
    (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPP : IsIdempotentElem P) (hQQ : IsIdempotentElem Q)
    (U : Submodule ℂ E) (γ : ℝ) (hγ : γ≤2)
    (hU : ∀ v∈U,(1-(1/2:ℂ) • (P+Q)) v∈U)
    (hgap : ∀ v∈U,γ*‖v‖^2≤‖P v‖^2+‖Q v‖^2)
    (m : ℕ) (v : E) (hv : v∈U) :
    ‖((1-(1/2:ℂ) • (P+Q))^m) v‖^2 ≤ (1-γ/2)^m*‖v‖^2 := by
  have hnonneg : 0≤1-γ/2 := by linarith
  have hmem (n : ℕ) : ((1-(1/2:ℂ) • (P+Q))^n) v∈U := by
    induction n with
    | zero => simpa using hv
    | succ n ih => rw [pow_succ',Module.End.mul_apply]; exact hU _ ih
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' (1-(1/2:ℂ) • (P+Q)) m,Module.End.mul_apply,pow_succ' (1-γ/2) m]
    have hstep := two_projection_filter_energy P Q hP hQ hPP hQQ
      (((1-(1/2:ℂ) • (P+Q))^m) v)
    have hg := hgap _ (hmem m)
    have hcontract : ‖(1-(1/2:ℂ) • (P+Q)) (((1-(1/2:ℂ) • (P+Q))^m) v)‖^2 ≤
        (1-γ/2)*‖((1-(1/2:ℂ) • (P+Q))^m) v‖^2 := by nlinarith only [hstep,hg]
    exact hcontract.trans ((mul_le_mul_of_nonneg_left ih hnonneg).trans_eq (mul_assoc _ _ _).symm)

#print axioms two_projection_filter_energy
#print axioms two_projection_filter_power_gap
end QuantitativeMaass
