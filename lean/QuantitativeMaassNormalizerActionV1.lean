module

public import QuantitativeMaassNormalizerGeneratorsV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticCongruenceStrip AsymptoticClassicalPetersson

namespace QuantitativeMaass

abbrev quotientNormalizerGroup (N : ℕ) : Subgroup AsymptoticRationalGroup.Group :=
  Subgroup.normalizer (gamma N : Set AsymptoticRationalGroup.Group)

theorem normalizer_mem_of_conjugations (N : ℕ) (g : AsymptoticRationalGroup.Group)
    (hc : ∀ a∈gamma N,g*a*g⁻¹∈gamma N)
    (hci : ∀ a∈gamma N,g⁻¹*a*g∈gamma N) : g∈(quotientNormalizerGroup N) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hc a
  · intro ha
    have h := hci (g*a*g⁻¹) ha
    convert h using 1; group

theorem normalizer_conj_mem (N : ℕ) (g : (quotientNormalizerGroup N))
    {a : AsymptoticRationalGroup.Group} (ha : a∈gamma N) : g.val*a*g.val⁻¹∈gamma N :=
  ((Subgroup.mem_normalizer_iff.mp g.property) a).mp ha

theorem normalizer_inv_conj_mem (N : ℕ) (g : (quotientNormalizerGroup N))
    {a : AsymptoticRationalGroup.Group} (ha : a∈gamma N) : g.val⁻¹*a*g.val∈gamma N :=
  ((Subgroup.mem_normalizer_iff''.mp g.property) a).mp ha

/-- Actual normalizer pullback on every vector of the quotient Hilbert space. -/
def quotientNormalizerPullback (N : ℕ) (g : (quotientNormalizerGroup N)) :
    AutomorphicSpace N →ₗᵢ[ℂ] AutomorphicSpace N :=
  AutomorphicL2.normalizerIsometry volume AsymptoticRationalGroup.measurePreserving
    (gamma N) g.val (fun _ ha => normalizer_conj_mem N g ha)
    (fun _ ha => normalizer_inv_conj_mem N g ha)
    (density N) (density_measurable N) (density_orbit_sum N)

def quotientNormalizerRepresentative (N : ℕ) (g : (quotientNormalizerGroup N)) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
      AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  AutomorphicL2.normalizerRepresentative volume AsymptoticRationalGroup.measurePreserving
    (gamma N) g.val (fun _ ha => normalizer_conj_mem N g ha)
    (fun _ ha => normalizer_inv_conj_mem N g ha)
    (density N) (density_measurable N) (density_orbit_sum N)

theorem quotientNormalizerPullback_representative (N : ℕ) (g : (quotientNormalizerGroup N))
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    quotientNormalizerPullback N g (AutomorphicL2.denseEmbedding _ _ f)=
      AutomorphicL2.denseEmbedding _ _ (quotientNormalizerRepresentative N g f) :=
  AutomorphicL2.normalizerIsometry_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma N) g.val _ _ (density N) (density_measurable N) (density_orbit_sum N) f

theorem quotientNormalizerPullback_one (N : ℕ) (x : AutomorphicSpace N) :
    quotientNormalizerPullback N 1 x=x := by
  have he : (fun x : AutomorphicSpace N => quotientNormalizerPullback N 1 x)=id := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (quotientNormalizerPullback N 1).continuous continuous_id
    funext f
    rw [Function.comp_apply,Function.comp_apply,quotientNormalizerPullback_representative]
    congr 1
    apply Subtype.ext
    funext z
    change f.val ((1:AsymptoticRationalGroup.Group) • z)=f.val z
    rw [one_smul]
  exact congrFun he x

theorem quotientNormalizerPullback_mul (N : ℕ) (g h : (quotientNormalizerGroup N))
    (x : AutomorphicSpace N) :
    quotientNormalizerPullback N (g*h) x=
      quotientNormalizerPullback N h (quotientNormalizerPullback N g x) := by
  have he : (fun x : AutomorphicSpace N => quotientNormalizerPullback N (g*h) x)=
      fun x => quotientNormalizerPullback N h (quotientNormalizerPullback N g x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (quotientNormalizerPullback N (g*h)).continuous
      ((quotientNormalizerPullback N h).continuous.comp (quotientNormalizerPullback N g).continuous)
    funext f
    change quotientNormalizerPullback N (g*h) (AutomorphicL2.denseEmbedding _ _ f)=
      quotientNormalizerPullback N h (quotientNormalizerPullback N g (AutomorphicL2.denseEmbedding _ _ f))
    rw [quotientNormalizerPullback_representative N (g*h) f,
      quotientNormalizerPullback_representative N g f,
      quotientNormalizerPullback_representative N h (quotientNormalizerRepresentative N g f)]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
    apply Subtype.ext
    funext z
    change f.val ((g.val*h.val) • z)=f.val (g.val • (h.val • z))
    rw [mul_smul]
  exact congrFun he x

/-- Unit-modulus eigenvectors stay eigenvectors under arbitrary words,
including inverses, in the actual completed normalizer action. -/
def normalizerEigenStabilizer (N : ℕ) (x : AutomorphicSpace N) :
    Subgroup ((quotientNormalizerGroup N)) where
  carrier := {g | ∃ c : ℂ,‖c‖=1 ∧ quotientNormalizerPullback N g x=c • x}
  one_mem' := ⟨1,by simp,by rw [quotientNormalizerPullback_one,one_smul]⟩
  mul_mem' := by
    rintro g h ⟨c,hc,he⟩ ⟨d,hd,hf⟩
    refine ⟨c*d,by rw [norm_mul,hc,hd,one_mul],?_⟩
    rw [quotientNormalizerPullback_mul,he,map_smul,hf,smul_smul]
  inv_mem' := by
    rintro g ⟨c,hc,he⟩
    have hc0 : c≠0 := by intro h; simp [h] at hc
    refine ⟨c⁻¹,by rw [norm_inv,hc,inv_one],?_⟩
    have hh : c • quotientNormalizerPullback N g⁻¹ x=x := by
      rw [←map_smul,←he,←quotientNormalizerPullback_mul,mul_inv_cancel,quotientNormalizerPullback_one]
    calc
      _=c⁻¹ • (c • quotientNormalizerPullback N g⁻¹ x) := by
        rw [smul_smul,inv_mul_cancel₀ hc0,one_smul]
      _=c⁻¹ • x := by rw [hh]

#print axioms normalizer_mem_of_conjugations
#print axioms quotientNormalizerPullback_representative
#print axioms quotientNormalizerPullback_one
#print axioms quotientNormalizerPullback_mul
#print axioms normalizerEigenStabilizer

end QuantitativeMaass
