module

public import AsymptoticFourierNormV1
public import AsymptoticL2MultiplierV1
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open MeasureTheory Set Filter AsymptoticFourierNorm
open scoped InnerProduct

/-- The translation cylinder in flat coordinates. Multiplication by w_t/y
identifies the paper's weighted hyperbolic L² space with this fixed L²
space; the Fourier modes below already include that factor. -/
abbrev Cylinder := AddCircle (1:ℝ) × ℝ

noncomputable def measure : Measure Cylinder :=
  (AddCircle.haarAddCircle (T:=1)).prod (volume.restrict (Ioi 0))

noncomputable abbrev Space := Lp ℂ 2 measure

theorem height_positive : ∀ᵐ z ∂measure,0<z.2 := by
  exact measurePreserving_snd.quasiMeasurePreserving.ae (ae_restrict_mem measurableSet_Ioi)

/-- An unnormalized positive Fourier mode in the conjugated cylinder. -/
noncomputable def mode (m t n : ℕ) (scale ε : ℝ) (z : Cylinder) : ℂ :=
  fourier (T:=1) (n+1:ℕ) z.1 * (Real.sqrt (density m t (scale*(n+1:ℕ)) ε z.2):ℂ)

theorem mode_norm_sq (m t n : ℕ) (scale : ℝ) {ε : ℝ} (hε : 0<ε)
    {z : Cylinder} (hz : 0≤z.2) :
    ‖mode m t n scale ε z‖^2=density m t (scale*(n+1:ℕ)) ε z.2 := by
  rw [mode,norm_mul]
  have hf : ‖fourier (T:=1) (n+1:ℕ) z.1‖=1 := Circle.norm_coe _
  rw [hf,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (density_nonneg m t _ hε hz)

theorem mode_continuous (m t n : ℕ) (scale ε : ℝ) : Continuous (mode m t n scale ε) := by
  unfold mode density AsymptoticGammaTail.kernel
  fun_prop

theorem mode_memLp (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    MemLp (mode m t n scale ε) 2 measure := by
  apply (memLp_two_iff_integrable_sq_norm (mode_continuous m t n scale ε).aestronglyMeasurable).mpr
  have hi := (integrable_density m t (mul_pos hs (by positivity : (0:ℝ)<(n+1:ℕ))) hε).comp_snd
    (AddCircle.haarAddCircle (T:=1))
  apply hi.congr
  filter_upwards [height_positive] with z hz
  exact (mode_norm_sq m t n scale hε hz.le).symm

noncomputable def modeLp (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) : Space :=
  (mode_memLp m t n hs hε).toLp (mode m t n scale ε)

theorem modeLp_coeFn (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    modeLp m t n hs hε =ᵐ[measure] mode m t n scale ε := MemLp.coeFn_toLp _

/-- The L² normalization is exactly the radial beta integral previously
estimated, not an independently specified sequence of normalization constants. -/
theorem modeLp_norm_sq (m t n : ℕ) {scale ε : ℝ} (hs : 0<scale) (hε : 0<ε) :
    ‖modeLp m t n hs hε‖^2=beta m t (scale*(n+1:ℕ)) ε := by
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  calc
    (∫ z,‖modeLp m t n hs hε z‖^2 ∂measure) =
        ∫ z,density m t (scale*(n+1:ℕ)) ε z.2 ∂measure := by
      apply integral_congr_ae
      filter_upwards [modeLp_coeFn m t n hs hε,height_positive] with z hz hpos
      rw [hz]
      exact mode_norm_sq m t n scale hε hpos.le
    _ = _ := by
      have hh := integral_prod_mul (μ:=AddCircle.haarAddCircle (T:=1))
        (ν:=volume.restrict (Ioi 0)) (fun _ : AddCircle (1:ℝ) => (1:ℝ))
        (density m t (scale*(n+1:ℕ)) ε)
      simpa [measure,beta] using hh

#print axioms modeLp_norm_sq

end AsymptoticCylinder
