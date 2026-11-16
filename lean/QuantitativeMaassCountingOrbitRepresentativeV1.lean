module

public import QuantitativeMaassCountingNormalizerMetricV1
public import QuantitativeMaassAllModulusLawsV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticNestedQuotients
open AsymptoticClassicalPetersson
namespace QuantitativeMaass.CountingMetric
attribute [local instance] Classical.propDecidable

/-- A counting function is realized pointwise on one free rational orbit,
and is zero elsewhere. Its quotient L2 class is zero, but its pointwise
values allow reuse of the purely algebraic modular/ramified identities. -/
def orbitLift (z : ℍ) (f : AsymptoticRationalGroup.Group→ℂ) (w : ℍ) : ℂ :=
  if h : ∃ a : AsymptoticRationalGroup.Group,a • z=w then f (Classical.choose h) else 0

theorem orbitLift_apply (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : AsymptoticRationalGroup.Group→ℂ) (a : AsymptoticRationalGroup.Group) :
    orbitLift z f (a • z)=f a := by
  have h : ∃ b : AsymptoticRationalGroup.Group,b • z=a • z := ⟨a,rfl⟩
  rw [orbitLift,dite_eq_left h,hz (Classical.choose_spec h)]

theorem orbitLift_off (z : ℍ) (f : AsymptoticRationalGroup.Group→ℂ) (w : ℍ)
    (hw : ¬∃ a : AsymptoticRationalGroup.Group,a • z=w) : orbitLift z f w=0 := by
  rw [orbitLift,dite_eq_right hw]

theorem orbitLift_transport (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : AsymptoticRationalGroup.Group→ℂ) (a : AsymptoticRationalGroup.Group) (w : ℍ) :
    orbitLift z f (a • w)=orbitLift z (fun b => f (a*b)) w := by
  by_cases hw : ∃ b : AsymptoticRationalGroup.Group,b • z=w
  · obtain ⟨b,rfl⟩ := hw
    rw [←mul_smul,orbitLift_apply z hz,orbitLift_apply z hz]
  · have haw : ¬∃ b : AsymptoticRationalGroup.Group,b • z=a • w := by
      rintro ⟨b,hb⟩
      exact hw ⟨a⁻¹*b,by rw [mul_smul,hb,inv_smul_smul]⟩
    rw [orbitLift_off z f _ haw,orbitLift_off z _ _ hw]

theorem orbitLift_measurable (z : ℍ) (f : AsymptoticRationalGroup.Group→ℂ) :
    Measurable (orbitLift z f) := by
  apply (measurable_const : Measurable (fun _ : ℍ => (0:ℂ))).measurable_of_countable_ne
  apply (Set.countable_range (fun a : AsymptoticRationalGroup.Group => a • z)).mono
  intro w hw
  by_contra h
  exact hw (orbitLift_off z f w h).symm

theorem orbitLift_ae_zero (N : ℕ) (z : ℍ) (f : AsymptoticRationalGroup.Group→ℂ) :
    orbitLift z f=ᵐ[quotientMeasure N]0 := by
  let : NullSingletonClass (volume : Measure ℍ) := ⟨AsymptoticRationalFreeness.volume_singleton⟩
  let : NullSingletonClass (quotientMeasure N) := inferInstanceAs
    (NullSingletonClass (volume.withDensity (density N)))
  filter_upwards [(Set.countable_range (fun a : AsymptoticRationalGroup.Group => a • z)).ae_notMem
    (quotientMeasure N)] with w hw
  exact orbitLift_off z f w hw

def orbitRepresentative (N : ℕ) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : Classes (gamma N)→ℂ) : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  ⟨orbitLift z (fun a => f (classOf (gamma N) a)),orbitLift_measurable z _,
    (by
      intro a w
      rw [orbitLift_transport z hz]
      congr 1
      funext b
      exact congrArg f (classOf_mul (gamma N) a b)),
    (memLp_congr_ae (orbitLift_ae_zero N z _)).mpr MemLp.zero⟩

theorem orbitRepresentative_apply (N : ℕ) (z : ℍ)
    (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z))
    (f : Classes (gamma N)→ℂ) (a : AsymptoticRationalGroup.Group) :
    (orbitRepresentative N z hz f).val (a • z)=f (classOf (gamma N) a) :=
  orbitLift_apply z hz (fun b => f (classOf (gamma N) b)) a

#print axioms orbitLift_transport
#print axioms orbitLift_measurable
#print axioms orbitLift_ae_zero
#print axioms orbitRepresentative_apply
end QuantitativeMaass.CountingMetric
