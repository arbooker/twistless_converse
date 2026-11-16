module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- A strong L² limit agrees almost everywhere with an a.e. pointwise limit
of representatives of the same sequence. -/
theorem lp_limit_ae_eq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {v : ℕ → Lp ℂ 2 μ} {V : Lp ℂ 2 μ} (hv : Tendsto v atTop (𝓝 V))
    {f : ℕ → A → ℂ} {g : A → ℂ} (hf : ∀ n,(v n : A → ℂ)=ᵐ[μ]f n)
    (hg : ∀ᵐ x ∂μ,Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    (V : A → ℂ)=ᵐ[μ]g := by
  obtain ⟨φ,hφ,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [hlim,ae_all_iff.mpr hf,hg] with x hx hfx hgx
  have ht := hgx.comp hφ.tendsto_atTop
  have he : (fun n => v (φ n) x)=(fun n => f (φ n) x) := funext (fun n => hfx (φ n))
  rw [he] at hx
  exact tendsto_nhds_unique hx ht

#print axioms lp_limit_ae_eq

end QuantitativeMaass
