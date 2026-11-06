module

public import AsymptoticClassicalTraceIntegrandV1
public import AsymptoticOrbitDensityTransportV1
public import AsymptoticClassicalOldLevelsV1
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory AsymptoticClassicalCusp
open AsymptoticCongruenceStrip AsymptoticOrbitDensity
open scoped ENNReal InnerProduct

variable (N M : ℕ) [NeZero N] [NeZero M] (k : ℤ) (hMN : M ∣ N)

/-- The unnormalized classical trace is adjoint to lower-level inclusion
 for the Petersson products on the actual cusp-form spaces. -/
theorem trace_adjoint (f : CuspForm (level N) k) (g : CuspForm (level M) k) :
    inner ℂ (arithmeticTrace (level N) (level M) k f) g =
      inner ℂ f (restrict k (level_antitone hMN) g) := by
  classical
  let H := (gamma N).subgroupOf (gamma M)
  let := Fintype.ofFinite (gamma M ⧸ H)
  let σ : ℍ → ℝ≥0∞ := inducedDensity H (density M)
  have hm : Measurable σ := inducedDensity_measurable H (density M) volume
    (fun a => AsymptoticRationalGroup.measurePreserving a.val) (density_measurable M)
  have hn (z : ℍ) : ∑' a : gamma N, σ (a.val • z) = 1 := by
    have he := (Subgroup.subgroupOfEquivOfLe (gamma_le_of_dvd hMN)).toEquiv.tsum_eq
      (fun a : gamma N => σ (a.val • z))
    exact he.symm.trans (inducedDensity_normalized H (density M) (density_orbit_sum M) z)
  have hfin : (∫⁻ z : ℍ, density M z) ≠ ∞ := by
    rw [density_integral M (Nat.pos_of_ne_zero (NeZero.ne M))]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hp : Measurable (petersson k f g) :=
    (petersson_continuous k f.holo'.continuous g.holo'.continuous).measurable
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (level N) f
    (restrict k (level_antitone hMN) g)
  calc
    _ = ∫ z, petersson k (arithmeticTrace (level N) (level M) k f) g z
        ∂volume.withDensity (density M) := inner_eq_integral M k _ g
    _ = ∫ z, ∑ q : gamma M ⧸ H, petersson k f g (q.out.val⁻¹ • z)
        ∂volume.withDensity (density M) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        simpa only [tsum_fintype] using trace_integrand N M k f g z)
    _ = ∫ z, petersson k f g z ∂volume.withDensity σ :=
      integral_coset_unfold volume (fun a : gamma M =>
        AsymptoticRationalGroup.measurePreserving a.val) (density M) (density_measurable M)
        H hfin (petersson k f g) hp C hC
    _ = _ := (inner_eq_integral_density N k σ hm hn f
      (restrict k (level_antitone hMN) g)).symm

/-- Vanishing trace is equivalent to orthogonality to every included
 lower-level cusp form. -/
theorem trace_zero_iff (f : CuspForm (level N) k) :
    arithmeticTrace (level N) (level M) k f = 0 ↔
      ∀ g : CuspForm (level M) k, inner ℂ f (restrict k (level_antitone hMN) g) = 0 := by
  constructor
  · intro hf g
    rw [← trace_adjoint N M k hMN, hf, inner_zero_left]
  · intro hf
    have hh := hf (arithmeticTrace (level N) (level M) k f)
    rw [← trace_adjoint N M k hMN] at hh
    exact inner_self_eq_zero.mp hh

/-- The first old-trace kernel is the actual Petersson orthogonal
 complement of the lower-level inclusion. -/
theorem trace_kernel_eq_orthogonal :
    LinearMap.ker (arithmeticTrace (level N) (level M) k) =
      (LinearMap.range (restrict k (level_antitone hMN)))ᗮ := by
  ext f
  rw [LinearMap.mem_ker, trace_zero_iff N M k hMN, Submodule.mem_orthogonal']
  constructor
  · rintro hf _ ⟨g, rfl⟩
    exact hf g
  · intro hf g
    exact hf _ ⟨g, rfl⟩

#print axioms trace_adjoint
#print axioms trace_zero_iff
#print axioms trace_kernel_eq_orthogonal

end AsymptoticClassicalPetersson
