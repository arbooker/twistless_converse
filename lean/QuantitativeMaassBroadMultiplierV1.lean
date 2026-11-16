module

public import QuantitativeMaassBroadCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

def broadBaseSchwartz : SchwartzMap ℝ ℂ :=
  (broadTimeBase_compact.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp broadTimeBase_smooth)

theorem broadBaseSchwartz_even : Function.Even broadBaseSchwartz := by
  intro s
  change (broadTimeBase (-s):ℂ)=(broadTimeBase s:ℂ)
  rw [broadTimeBase_even s]

/-- Exact moving-frequency multiplier of the concrete broad packet,
expressed by two dilated translates of one fixed Schwartz transform. -/
theorem broadTimeWeight_cosinePacket (L : ℝ) (hL : 0<L) (t r : ℝ) :
    cosinePacket (broadTimeWeight L t) r=
      (angularFourier broadBaseSchwartz ((r-t)/L)+
        angularFourier broadBaseSchwartz ((r+t)/L))/
          ((2*cosineSquareMass (broadTimeDensity L) t : ℝ):ℂ) := by
  let m := cosineSquareMass (broadTimeDensity L) t
  have hm : m≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2)
    (broadTimeDensity_cosineSquareMass_half L hL t))
  have he : broadTimeWeight L t=fun s => ((L/m:ℝ):ℂ)*
      scaledModulatedTimeTest broadBaseSchwartz (1/L) t s := by
    funext s
    have hs : s/(1/L)=L*s := by field_simp
    simp only [broadTimeWeight,normalizedCosineWeight,broadTimeDensity,
      scaledModulatedTimeTest,hs]
    change ((L*broadTimeBase (L*s)*Real.cos (t*s)/m:ℝ):ℂ)=
      ((L/m:ℝ):ℂ)*((broadTimeBase (L*s):ℂ)*(Real.cos (s*t):ℂ))
    rw [mul_comm s t]
    push_cast
    ring
  rw [he]
  have hlin : cosinePacket (fun s => ((L/m:ℝ):ℂ)*
      scaledModulatedTimeTest broadBaseSchwartz (1/L) t s) r=
      ((L/m:ℝ):ℂ)*cosinePacket (scaledModulatedTimeTest broadBaseSchwartz (1/L) t) r := by
    unfold cosinePacket
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  rw [hlin,scaledModulated_cosinePacket broadBaseSchwartz
    broadBaseSchwartz.continuous
    (broadTimeBase_compact.comp_left Complex.ofReal_zero) (1/L) t r (by positivity),
    cosinePacket_eq_angularFourier broadBaseSchwartz broadBaseSchwartz_even,
    cosinePacket_eq_angularFourier broadBaseSchwartz broadBaseSchwartz_even]
  have hmC : (m:ℂ)≠0 := by exact_mod_cast hm
  have hLC : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  rw [show (1/L)*(r-t)=(r-t)/L by ring,show (1/L)*(r+t)=(r+t)/L by ring]
  change _ = _/((2*m:ℝ):ℂ)
  push_cast
  field_simp

theorem broadTimeWeight_cosinePacket_norm_le (L : ℝ) (hL : 0<L) (t r : ℝ) :
    ‖cosinePacket (broadTimeWeight L t) r‖≤
      ‖angularFourier broadBaseSchwartz ((r-t)/L)‖+
        ‖angularFourier broadBaseSchwartz ((r+t)/L)‖ := by
  rw [broadTimeWeight_cosinePacket L hL t r,norm_div,Complex.norm_real,Real.norm_eq_abs]
  have hm := broadTimeDensity_cosineSquareMass_half L hL t
  have hd : 0<2*cosineSquareMass (broadTimeDensity L) t := by linarith
  rw [abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  apply (norm_add_le _ _).trans
  have hn : 0≤‖angularFourier broadBaseSchwartz ((r-t)/L)‖+
      ‖angularFourier broadBaseSchwartz ((r+t)/L)‖ := by positivity
  nlinarith

#print axioms broadTimeWeight_cosinePacket
#print axioms broadTimeWeight_cosinePacket_norm_le

end QuantitativeMaass
