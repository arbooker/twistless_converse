module

public import AsymptoticClassicalFrickeTraceIntegrandV1
public import AsymptoticOrbitDensityAverageV1
public import Mathlib.Analysis.InnerProductSpace.Orthogonal

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace AsymptoticClassicalPetersson

open UpperHalfPlane MeasureTheory AsymptoticClassicalCusp
open AsymptoticCongruenceStrip AsymptoticOrbitDensity
open scoped ENNReal InnerProduct

variable (N M : ℕ) [NeZero N] [NeZero M] (hN : 0 < N) (k : ℤ) (hMN : M ∣ N)

/-- The Fricke old trace satisfies the averaging identity in the actual
 Petersson space at level N. No new norm on the conjugated target is needed. -/
theorem fricke_trace_inner_average (f : CuspForm (level N) k)
    (g : CuspForm (frickeOldLevel N M hN) k) :
    (((gamma N).relIndex (frickeOldGroup N M hN) : ℝ)⁻¹) •
      inner ℂ (restrict k (level_le_frickeOldLevel hN hMN)
        (arithmeticTrace (level N) (frickeOldLevel N M hN) k f))
        (restrict k (level_le_frickeOldLevel hN hMN) g) =
      inner ℂ f (restrict k (level_le_frickeOldLevel hN hMN) g) := by
  classical
  let J := frickeOldGroup N M hN
  let H := (gamma N).subgroupOf J
  let := Fintype.ofFinite (J ⧸ H)
  have hn (z : ℍ) : ∑' a : H, density N (a.val.val • z) = 1 := by
    have he := (Subgroup.subgroupOfEquivOfLe (gamma_le_frickeOldGroup hN hMN)).toEquiv.tsum_eq
      (fun a : gamma N => density N (a.val • z))
    exact he.trans (density_orbit_sum N z)
  have hfin : (∫⁻ z : ℍ, density N z) ≠ ∞ := by
    rw [density_integral N (Nat.pos_of_ne_zero (NeZero.ne N))]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hp : Measurable (petersson k f g) :=
    (petersson_continuous k f.holo'.continuous g.holo'.continuous).measurable
  have hinv (a : H) (z : ℍ) : petersson k f g (a.val.val • z) = petersson k f g z :=
    integrand_invariant N k f (restrict k (level_le_frickeOldLevel hN hMN) g)
      ⟨a.val.val, a.property⟩ z
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k (level N) f
    (restrict k (level_le_frickeOldLevel hN hMN) g)
  have he := integral_coset_average volume
    (fun a : J => AsymptoticRationalGroup.measurePreserving a.val)
    H (density N) (density_measurable N) hn hfin (petersson k f g) hp hinv C hC
  rw [inner_eq_integral, inner_eq_integral]
  change ((H.index : ℝ)⁻¹) •
    (∫ z, petersson k (arithmeticTrace (level N) (frickeOldLevel N M hN) k f) g z
      ∂volume.withDensity (density N)) = _
  have ht : (fun z => petersson k (arithmeticTrace (level N) (frickeOldLevel N M hN) k f) g z) =
      fun z => ∑ q : J ⧸ H, petersson k f g (q.out.val⁻¹ • z) := by
    funext z
    simpa only [tsum_fintype] using fricke_trace_integrand N M hN k f g z
  rw [ht]
  exact he

theorem fricke_trace_zero_iff (f : CuspForm (level N) k) :
    arithmeticTrace (level N) (frickeOldLevel N M hN) k f = 0 ↔
      ∀ g : CuspForm (frickeOldLevel N M hN) k,
        inner ℂ f (restrict k (level_le_frickeOldLevel hN hMN) g) = 0 := by
  constructor
  · intro hf g
    have he := fricke_trace_inner_average N M hN k hMN f g
    rw [hf, map_zero, inner_zero_left, smul_zero] at he
    exact he.symm
  · intro hf
    let T := arithmeticTrace (level N) (frickeOldLevel N M hN) k
    have he := (fricke_trace_inner_average N M hN k hMN f (T f)).trans (hf (T f))
    have hc : (((gamma N).relIndex (frickeOldGroup N M hN) : ℝ)⁻¹) ≠ 0 := by
      apply inv_ne_zero
      exact_mod_cast ((gamma N).subgroupOf (frickeOldGroup N M hN)).index_ne_zero_of_finite
    have hz := inner_self_eq_zero.mp ((smul_eq_zero.mp he).resolve_left hc)
    apply restrict_injective k (level_le_frickeOldLevel hN hMN)
    simpa only [map_zero] using hz

/-- The second old-trace kernel is exactly the orthogonal complement of
 the Fricke-conjugated old inclusion. -/
theorem fricke_trace_kernel_eq_orthogonal :
    LinearMap.ker (arithmeticTrace (level N) (frickeOldLevel N M hN) k) =
      (LinearMap.range (restrict k (level_le_frickeOldLevel hN hMN)))ᗮ := by
  ext f
  rw [LinearMap.mem_ker, fricke_trace_zero_iff N M hN k hMN, Submodule.mem_orthogonal']
  constructor
  · rintro hf _ ⟨g, rfl⟩
    exact hf g
  · intro hf g
    exact hf _ ⟨g, rfl⟩

#print axioms fricke_trace_inner_average
#print axioms fricke_trace_zero_iff
#print axioms fricke_trace_kernel_eq_orthogonal

end AsymptoticClassicalPetersson
