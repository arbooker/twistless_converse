module

public import MaassAxisInversionV1
public import FinitenessInputBoundsV1

set_option autoImplicit false

@[expose] public section

open Complex Filter Asymptotics FinitenessMellinSeries

namespace MaassOriginal

/-- Individual polynomial growth for complex coefficients; no common
growth exponent is imposed across the eventual solution space. -/
def PolynomialGrowth (b : ℕ → ℂ) : Prop :=
  ∃ τ : ℝ, (fun n => ‖b n‖) =O[atTop] (fun n : ℕ => (n:ℝ)^τ)

noncomputable def dirichlet (b : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, b (n+1)*((n+1:ℕ):ℂ)^(-s)

noncomputable def completed (L : ℝ) (p : MaassSpectral.Parameter) (δ : ℕ)
    (b : ℕ → ℂ) (s : ℂ) : ℂ :=
  (L:ℂ)^(s/2)*MaassMellin.realGammaPair (MaassSpectral.order p) (s+(δ:ℂ))*dirichlet b s

/-- Exactly the entire finite-order continuation and functional equation
for one completed series. Its normalization is L^(s/2), not the older
holomorphic draft's L^((s-1/2)/2). -/
def Continuation (L : ℝ) (p : MaassSpectral.Parameter) (δ : ℕ)
    (b : ℕ → ℂ) (ε : ℂ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ FinitenessOriginalInput.FiniteOrder F ∧
    (∃ c : ℝ, ∀ s : ℂ, c<s.re → F s=completed L p δ b s) ∧
    ∀ s : ℂ, F s=ε*F (1-s)

noncomputable def frequencies (L : ℝ) (n : ℕ) : ℝ :=
  Real.log (n+1)-Real.log L/2

noncomputable def axisSum (L : ℝ) (p : MaassSpectral.Parameter) (δ : ℕ)
    (b : ℕ → ℂ) (l : ℝ) : ℂ :=
  ∑' n : ℕ, b (n+1)*MaassMellin.parityKernel p δ (Real.exp (l+frequencies L n))

theorem frequency_term {L : ℝ} (hL : 0<L) (b : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    b (n+1)*Complex.exp (((-frequencies L n:ℝ):ℂ)*s) =
      (L:ℂ)^(s/2)*(b (n+1)*((n+1:ℕ):ℂ)^(-s)) := by
  have hn : 0<((n+1:ℕ):ℝ) := by positivity
  rw [MaassMellin.cpow_pos L hL]
  rw [show ((n+1:ℕ):ℂ) = (((n+1:ℕ):ℝ):ℂ) by simp,
    MaassMellin.cpow_pos _ hn]
  have he : (((-frequencies L n:ℝ):ℂ)*s) =
      (Real.log L:ℂ)*(s/2)+(Real.log ((n+1:ℕ):ℝ):ℂ)*(-s) := by
    unfold frequencies
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

theorem completed_series {L : ℝ} (hL : 0<L) (p : MaassSpectral.Parameter) (δ : ℕ)
    (b : ℕ → ℂ) (s : ℂ) :
    completed L p δ b s = MaassMellin.realGammaPair (MaassSpectral.order p) (s+(δ:ℂ))*
      series (fun n => b (n+1)) (frequencies L) s := by
  unfold completed dirichlet series
  simp_rw [frequency_term hL]
  rw [tsum_mul_left]
  ring

theorem weighted_summable {b : ℕ → ℂ} {τ c : ℝ}
    (hb : (fun n => ‖b n‖) =O[atTop] (fun n : ℕ => (n:ℝ)^τ))
    (hc : τ+1<c) (L : ℝ) :
    Summable (fun n => ‖b (n+1)‖*Real.exp (-c*frequencies L n)) := by
  have h := FinitenessInputBounds.absolute_convergence hb hc
  simp only [Real.norm_eq_abs, abs_norm] at h
  have he (n:ℕ) : ‖b (n+1)‖*Real.exp (-c*frequencies L n) =
      Real.exp (c*Real.log L/2)*(‖b (n+1)‖*Real.exp (-c*Real.log (n+1))) := by
    unfold frequencies
    rw [show -c*(Real.log (n+1)-Real.log L/2) = c*Real.log L/2+(-c*Real.log (n+1)) by ring,
      Real.exp_add]
    ring
  simp_rw [he]
  exact h.mul_left _

/-- The original growth and completed FE imply axis inversion. No
convergence, Mellin identity, rapid decay or contour-shift hypothesis is
added to the original analytic input. -/
theorem axis_inversion {L : ℝ} (hL : 0<L) (p : MaassSpectral.Parameter) (δ : ℕ)
    {b : ℕ → ℂ} (hb : PolynomialGrowth b) {ε : ℂ} (hε : ‖ε‖=1)
    (hcont : Continuation L p δ b ε) (l : ℝ) :
    axisSum L p δ b l = ε*(Real.exp (-l):ℂ)*axisSum L p δ b (-l) := by
  obtain ⟨τ,hgrowth⟩ := hb
  obtain ⟨F,hhol,hfinite,⟨c0,hline⟩,hFE⟩ := hcont
  obtain ⟨c,hc⟩ := exists_gt (max 1 (max (τ+1) c0))
  have hc1 : 1<c := (le_max_left _ _).trans_lt hc
  have hcτ : τ+1<c := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hc
  have hcc : c0<c := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hc
  apply MaassMellin.parity_axis_inversion p δ hc1 (weighted_summable hgrowth hcτ L)
    hhol (FinitenessInputBounds.finiteOrder_bound hhol.continuous hfinite) _ hε hFE l
  intro z hz
  rw [hline z (by rw [hz]; exact hcc), completed_series hL]

#print axioms completed_series
#print axioms weighted_summable
#print axioms axis_inversion

end MaassOriginal
