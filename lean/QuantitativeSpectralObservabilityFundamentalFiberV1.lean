module

public import QuantitativeSpectralObservabilityFundamentalV1
public import AsymptoticCongruenceQuotientV1
public import AsymptoticFiberProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 100000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane Set MeasureTheory
open AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticRegularTrace
open scoped Pointwise lp

abbrev OrbitGroup := AsymptoticRationalGroup.Group

/-- One invariant conull set removes every fundamental-domain boundary
collision on the entire rational orbit, not just at the root. -/
def fundamentalGood (N : ℕ) (x : ℍ) : Prop :=
  ∀ a : OrbitGroup, ∀ h : gamma N, h≠1 →
    ¬(a • x∈fundamentalSet N ∧ h.val • (a • x)∈fundamentalSet N)

theorem fundamentalGood_measurable (N : ℕ) (hN : 0<N) :
    MeasurableSet {x | fundamentalGood N x} := by
  have hm := fundamentalSet_measurable N hN
  simp only [fundamentalGood,ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro h
  apply MeasurableSet.iInter
  intro _
  exact ((hm.preimage (AsymptoticRationalGroup.measurePreserving a).measurable).inter
    (hm.preimage ((AsymptoticRationalGroup.measurePreserving h.val).measurable.comp
      (AsymptoticRationalGroup.measurePreserving a).measurable))).compl

theorem fundamental_collision_ae (N : ℕ) (hN : 0<N) (h : gamma N) (hh : h≠1) :
    ∀ᵐ x : ℍ ∂volume, ¬(x∈fundamentalSet N ∧ h.val • x∈fundamentalSet N) := by
  have hf := fundamentalSet_isFundamental N hN
  have hd := hf.aedisjoint (i:=1) (j:=h⁻¹) (by simpa using hh)
  change volume ((1:gamma N) • fundamentalSet N ∩ h⁻¹ • fundamentalSet N)=0 at hd
  rw [one_smul] at hd
  rw [ae_iff]
  have he : {x : ℍ | ¬¬(x∈fundamentalSet N ∧ h.val • x∈fundamentalSet N)} =
      fundamentalSet N ∩ h⁻¹ • fundamentalSet N := by
    ext x
    simp only [mem_ofPred_eq,not_not,mem_inter_iff,mem_smul_set_iff_inv_smul_mem,inv_inv]
    rfl
  rw [he]
  exact hd

theorem fundamentalGood_ae (N : ℕ) (hN : 0<N) :
    ∀ᵐ x : ℍ ∂volume, fundamentalGood N x := by
  unfold fundamentalGood
  have ha (a : OrbitGroup) (h : gamma N) (hh : h≠1) :
      ∀ᵐ x : ℍ ∂volume,
        ¬(a • x∈fundamentalSet N ∧ h.val • (a • x)∈fundamentalSet N) :=
    (AsymptoticRationalGroup.measurePreserving a).quasiMeasurePreserving.ae
      (p:=fun y : ℍ => ¬(y∈fundamentalSet N ∧ h.val • y∈fundamentalSet N))
      (fundamental_collision_ae N hN h hh)
  exact ae_all_iff.mpr (fun a => ae_all_iff.mpr (fun h => ae_all_iff.mpr (ha a h)))

theorem fundamentalGood_smul_iff (N : ℕ) (x : ℍ) (b : OrbitGroup) :
    fundamentalGood N (b • x) ↔ fundamentalGood N x := by
  constructor
  · intro hx a h hh hz
    apply hx (a*b⁻¹) h hh
    simpa only [mul_smul,inv_smul_smul] using hz
  · intro hx a h hh hz
    apply hx (a*b) h hh
    simpa only [mul_smul] using hz

theorem fundamental_class_unique (N : ℕ) (x : ℍ) (hx : fundamentalGood N x)
    (a b : OrbitGroup) (hab : classOf N a=classOf N b)
    (ha : a • x∈fundamentalSet N) (hb : b • x∈fundamentalSet N) : a=b := by
  by_contra hne
  let h : gamma N := ⟨b*a⁻¹,QuotientGroup.rightRel_apply.mp (Quotient.exact hab)⟩
  have hh : h≠1 := by
    intro he
    have he' : b*a⁻¹=1 := congrArg Subtype.val he
    exact hne (mul_inv_eq_one.mp he').symm
  apply hx a h hh
  refine ⟨ha,?_⟩
  simpa only [h,mul_smul,inv_smul_smul] using hb

theorem fundamental_fibre_unique (N : ℕ) (x : ℍ) (hx : fundamentalGood N x)
    (q : Classes N) :
    ∃! g : {g : OrbitGroup // classOf N g=q}, g.val • x∈fundamentalSet N := by
  obtain ⟨h,hh⟩ := fundamentalSet_orbit_meets N (q.out • x)
  let g : {g : OrbitGroup // classOf N g=q} :=
    ⟨h.val*q.out,(classOf_mul N h q.out).trans q.out_eq⟩
  have hg : g.val • x∈fundamentalSet N := by simpa only [g,mul_smul] using hh
  refine ⟨g,hg,?_⟩
  intro a ha
  apply Subtype.ext
  exact fundamental_class_unique N x hx a.val g.val (a.property.trans g.property.symm) ha hg

def fundamentalAmplitude (N : ℕ) (z : ℍ) : ℂ :=
  (fundamentalSet N).indicator (fun _ => (1:ℂ)) z

theorem fundamental_amplitude_hasSum (N : ℕ) (x : ℍ) (hx : fundamentalGood N x)
    (q : Classes N) :
    HasSum (fun g : {g : OrbitGroup // classOf N g=q} =>
      ‖fundamentalAmplitude N (g.val • x)‖^2) 1 := by
  classical
  obtain ⟨g,hg,huniq⟩ := fundamental_fibre_unique N x hx q
  convert hasSum_ite_eq g (1:ℝ) using 1
  ext a
  by_cases ha : a=g
  · subst a
    simp [fundamentalAmplitude,hg]
  · have hnot : a.val • x∉fundamentalSet N := fun h => ha (huniq a h)
    simp [fundamentalAmplitude,hnot,ha]

/-- Unweighted quotient coordinates represented once in the genuine
fundamental set, with exact counting-L² normalization. -/
def fundamentalInduction (N : ℕ) (x : ℍ) (hx : fundamentalGood N x) :
    ℓ²(Classes N,ℂ) →ₗᵢ[ℂ] ℓ²(OrbitGroup,ℂ) :=
  AsymptoticFiberIsometry.isometry (classOf N)
    (fun g => fundamentalAmplitude N (g • x)) (fundamental_amplitude_hasSum N x hx)

theorem fundamentalInduction_apply (N : ℕ) (x : ℍ) (hx : fundamentalGood N x)
    (f : ℓ²(Classes N,ℂ)) (g : OrbitGroup) :
    fundamentalInduction N x hx f g=fundamentalAmplitude N (g • x)*f (classOf N g) := rfl

#print axioms fundamentalGood_ae
#print axioms fundamental_fibre_unique
#print axioms fundamentalInduction_apply

end QuantitativeSpectralObservability
