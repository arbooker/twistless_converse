module

public import QuantitativeMaassPlaneLinearV1
public import MaassFrickeSmoothV1
public import QuantitativeMaassEulerFrickeAnalyticV1
public import QuantitativeMaassEulerWaveEquationV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem fricke_pullback_contDiffOn {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2}) (L : ℝ) (hL : 0<L) :
    ContDiffOn ℝ ∞ (MaassDifferential.pullback L f) {z : ℝ × ℝ | 0<z.2} :=
  MaassDifferential.pullback_contDiffOn hf hL

theorem fricke_axis (L y : ℝ) (hL : 0<L) (hy : 0<y) :
    MaassDifferential.F L 0 y=(0,1/(L*y)) := by
  apply Prod.ext
  · simp [MaassDifferential.F]
  · dsimp [MaassDifferential.F]
    field_simp
    ring

/-- The Fricke pullback reverses the normal direction on the imaginary axis,
with exact scale -1/(L*y^2). -/
theorem fricke_normal_axis {f : (ℝ × ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℝ × ℝ | 0<z.2})
    (L y : ℝ) (hL : 0<L) (hy : 0<y) :
    planeDerivative (1,0) (MaassDifferential.pullback L f) (0,y)=
      ((-1/(L*y^2):ℝ):ℂ)*planeDerivative (1,0) f (0,1/(L*y)) := by
  have hU : IsOpen {z : ℝ × ℝ | 0<z.2} := isOpen_lt continuous_const continuous_snd
  have hp := MaassDifferential.F_height_pos (x:=0) hL hy
  have hdf := ((hf.contDiffAt (hU.mem_nhds (show MaassDifferential.F L 0 y∈{z : ℝ × ℝ | 0<z.2} from hp))).differentiableAt (by simp)).hasFDerivAt
  have hg : HasDerivAt (fun t => MaassDifferential.F L t y) (MaassDifferential.a L 0 y,-MaassDifferential.b L 0 y) 0 :=
    MaassDifferential.F_hasDerivAt_X hL (MaassDifferential.radius_pos hy).ne'
  have he : (MaassDifferential.a L 0 y,-MaassDifferential.b L 0 y)=
      (-1/(L*y^2)) • ((1,0):ℝ × ℝ) := by
    apply Prod.ext
    · dsimp [MaassDifferential.a]
      field_simp
      ring
    · simp [MaassDifferential.b]
  have hh := (hdf.comp_hasDerivAt (l:=f) 0 hg).deriv
  rw [he,map_smul,fricke_axis L y hL hy] at hh
  rw [←planeDerivative_horizontal (fricke_pullback_contDiffOn hf L hL) hU 0 y hy]
  simpa only [MaassDifferential.pullback,Function.comp_def,planeDerivative,Complex.real_smul] using hh

#print axioms fricke_pullback_contDiffOn
#print axioms fricke_axis
#print axioms fricke_normal_axis

end QuantitativeMaass
