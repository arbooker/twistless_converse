module

public import FinitenessAllLevelBoundarySamplingV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelBoundaryGeometry

open Complex Metric Set MeasureTheory FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundarySampling FinitenessAllLevelCauchyOperator

def line (x b : ℝ) : ℂ := (x : ℂ) + (b : ℂ) * I

@[simp] theorem line_im (x b : ℝ) : (line x b).im = b := by simp [line]

theorem line_measurable {x : ℂ → ℝ} (hx : Measurable x) (b s : ℝ) :
    Measurable (fun w => line (x w + s) b) :=
  ((Complex.continuous_ofReal.measurable.comp (hx.add_const s)).add measurable_const)

theorem line_norm_lower (x : ℝ) {b : ℝ} (hb : 0 ≤ b) : b ≤ ‖line x b‖ := by
  simpa only [line_im, abs_of_nonneg hb] using Complex.abs_im_le_norm (line x b)

/-- An ordinary primitive Fricke branch: the final translation t is the
primitive-twist summation shift, while s is the certificate row shift. -/
def frickeSource (L b s t : ℝ) (x : ℂ → ℝ) (w : ℂ) : ℂ :=
  Function.Periodic.qParam 1 (-1 / ((L : ℂ) * line (x w + s) b) + (t : ℂ))

def frickeWeight (L b s : ℝ) (x : ℂ → ℝ) (χ : ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  χ / (((Real.sqrt L : ℝ) : ℂ) * line (x w + s) b) ^ k

theorem frickeSource_measurable (L b s t : ℝ) {x : ℂ → ℝ} (hx : Measurable x) :
    Measurable (frickeSource L b s t x) :=
  Function.Periodic.continuous_qParam.measurable.comp
    ((measurable_const.div (measurable_const.mul (line_measurable hx b s))).add_const (t : ℂ))

theorem frickeWeight_measurable (L b s : ℝ) {x : ℂ → ℝ} (hx : Measurable x)
    (χ : ℂ) (k : ℕ) : Measurable (frickeWeight L b s x χ k) :=
  measurable_const.div ((measurable_const.mul (line_measurable hx b s)).pow_const k)

theorem frickeWeight_bound {L b : ℝ} (hL : 0 < L) (hb : 0 < b)
    (s : ℝ) (x : ℂ → ℝ) (χ : ℂ) (k : ℕ) (w : ℂ) :
    ‖frickeWeight L b s x χ k w‖ ≤ ‖χ‖ / (Real.sqrt L * b) ^ k := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  rw [frickeWeight, norm_div, norm_pow, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs.le]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos (mul_pos hs hb) k)
  exact pow_le_pow_left₀ (mul_nonneg hs.le hb.le)
    (mul_le_mul_of_nonneg_left (line_norm_lower (x w + s) hb.le) hs.le) k

/-- The actual form of each primitive reconstruction branch supplies the
bounded measurable sampling interface without a growth assumption on F. -/
def frickeSample (r : ℝ) {R L b : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (hb : 0 < b)
    (s t : ℝ) (x : ℂ → ℝ) (hx : Measurable x) (χ : ℂ) (k : ℕ) :
    BoundaryOperator (space r) R :=
  sample r hR (by positivity) (frickeWeight L b s x χ k) (frickeSource L b s t x)
    (frickeWeight_measurable L b s hx χ k) (frickeSource_measurable L b s t hx)
    (fun w _ => frickeWeight_bound hL hb s x χ k w)

/-- Both retained-row sources are dilations of the same shifted height line. -/
def dilationSource (d b s : ℝ) (x : ℂ → ℝ) (w : ℂ) : ℂ :=
  Function.Periodic.qParam 1 ((d : ℂ) * line (x w + s) b)

theorem dilationSource_measurable (d b s : ℝ) {x : ℂ → ℝ} (hx : Measurable x) :
    Measurable (dilationSource d b s x) :=
  Function.Periodic.continuous_qParam.measurable.comp
    (measurable_const.mul (line_measurable hx b s))

def dilationSample (r : ℝ) {R : ℝ} (hR : 0 ≤ R) (d b s : ℝ)
    (x : ℂ → ℝ) (hx : Measurable x) (c : ℂ) : BoundaryOperator (space r) R :=
  sample r hR (norm_nonneg c) (fun _ => c) (dilationSource d b s x)
    measurable_const (dilationSource_measurable d b s hx) (fun _ _ => le_rfl)

def frickeCell (r : ℝ) {R L b : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (hb : 0 < b)
    (cell : Set ℂ) (hc : MeasurableSet cell) (s t : ℝ)
    (x : ℂ → ℝ) (hx : Measurable x) (χ : ℂ) (k : ℕ) :
    BoundaryOperator (space r) R :=
  cellSample r hR (by positivity) cell hc
    (frickeWeight L b s x χ k) (frickeSource L b s t x)
    (frickeWeight_measurable L b s hx χ k) (frickeSource_measurable L b s t hx)
    (fun w _ _ => frickeWeight_bound hL hb s x χ k w)

def dilationCell (r : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (cell : Set ℂ) (hc : MeasurableSet cell) (d b s : ℝ)
    (x : ℂ → ℝ) (hx : Measurable x) (c : ℂ) : BoundaryOperator (space r) R :=
  cellSample r hR (norm_nonneg c) cell hc (fun _ => c) (dilationSource d b s x)
    measurable_const (dilationSource_measurable d b s hx) (fun _ _ _ => le_rfl)

#print axioms frickeSource_measurable
#print axioms frickeWeight_bound
#print axioms frickeSample
#print axioms dilationSample

end FinitenessAllLevelBoundaryGeometry
