module

public import QuantitativeSpectralObservabilityFundamentalSamplingV1
public import AsymptoticQuotientCoordinatesV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

namespace QuantitativeSpectralObservability

open UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open scoped lp BigOperators

attribute [local instance] Classical.propDecidable

theorem coordinate_eq_adjoint_of_quotient (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (u : ℓ²(OrbitGroup,ℂ))
    (hu : u∈quotientSpace N hε ht x) (g : OrbitGroup) :
    coordinate N ε t x g u=
      (induction N hε ht x).toContinuousLinearMap.adjoint u (classOf N g) := by
  obtain ⟨f,rfl⟩ := hu
  change coordinate N ε t x g (induction N hε ht x f)=_
  rw [coordinate_induction]
  have hi := AsymptoticFiberIsometry.adjoint_comp (classOf N)
    (fun g => AsymptoticCongruenceWeight.amplitude N ε t (g • x))
    (fibre_amplitude_hasSum N hε ht x)
  have he := congrArg (fun B : ℓ²(Classes N,ℂ) →L[ℂ] ℓ²(Classes N,ℂ) => B f (classOf N g)) hi
  exact he.symm

theorem coordinate_gamma_mul_of_quotient (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (u : ℓ²(OrbitGroup,ℂ))
    (hu : u∈quotientSpace N hε ht x) (h : gamma N) (g : OrbitGroup) :
    coordinate N ε t x (h.val*g) u=coordinate N ε t x g u := by
  calc
    _ = (induction N hε ht x).toContinuousLinearMap.adjoint u (classOf N (h.val*g)) :=
      coordinate_eq_adjoint_of_quotient N hε ht x u hu (h.val*g)
    _ = (induction N hε ht x).toContinuousLinearMap.adjoint u (classOf N g) :=
      congrArg (fun q => (induction N hε ht x).toContinuousLinearMap.adjoint u q)
        (classOf_mul N h g)
    _ = _ := (coordinate_eq_adjoint_of_quotient N hε ht x u hu g).symm

/-- The normalized sampler returns precisely the original compact sample
in its genuine fundamental-domain coordinate. -/
theorem fundamentalSampling_coordinate (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x)
    (v : ℓ²(OrbitGroup,ℂ)) (g : OrbitGroup)
    (hg : g • x∈fundamentalSet N) :
    coordinate N ε t x g (fundamentalSampling N hN H hε ht x v)=
      fundamentalRawSampling N hN H hε t x v g := by
  have he := congrArg (fun u : ℓ²(OrbitGroup,ℂ) => u g)
    (fundamentalSampling_recover N hN H hε ht x hx v)
  rw [fundamentalInduction_apply] at he
  simp only [fundamentalAmplitude,Set.indicator_of_mem hg,one_mul] at he
  rw [coordinate_eq_adjoint_of_quotient N hε ht x _
    (fundamentalSampling_range N hN H hε ht x v)]
  exact he

/-- A reducing congruence word may be removed from the quotient
coordinate, while the raw sampler is evaluated at its reduced label. -/
theorem fundamentalSampling_reduced_coordinate (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x)
    (v : ℓ²(OrbitGroup,ℂ)) (h : gamma N) (g : OrbitGroup)
    (hg : (h.val*g) • x∈fundamentalCompact N H) :
    coordinate N ε t x g (fundamentalSampling N hN H hε ht x v)=
      fundamentalRawSampling N hN H hε t x v (h.val*g) := by
  rw [← coordinate_gamma_mul_of_quotient N hε ht x _
    (fundamentalSampling_range N hN H hε ht x v) h g]
  exact fundamentalSampling_coordinate N hN H hε ht x hx v _
    (fundamentalCompact_subset N H hg)

theorem fundamentalSampling_reduced_decode (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ}
    (hε : 0<ε) {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x)
    (v : ℓ²(OrbitGroup,ℂ)) (h : gamma N) (g : OrbitGroup)
    (hg : (h.val*g) • x∈fundamentalCompact N H) :
    coordinate N ε t x g (fundamentalSampling N hN H hε ht x v)=
      AsymptoticOrbitDecode.decode ε t x v (h.val*g) := by
  rw [fundamentalSampling_reduced_coordinate N hN H hε ht x hx v h g hg,
    fundamentalRawSampling_decode,ite_eq_left hg]

/-- The actual finite quotient residual is the reduced raw row. This
identity is pointwise and imposes no invariance on the original input. -/
theorem fundamentalSampling_row_coordinates {I : Type*} [Fintype I]
    (N : ℕ) (hN : 0<N) (H : ℝ) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) (x : ℍ) (hx : fundamentalGood N x)
    (v : ℓ²(OrbitGroup,ℂ)) (b : I → OrbitGroup) (h : I → gamma N)
    (c : I → ℂ) (g : OrbitGroup)
    (hg : ∀ i, ((h i).val*(b i*g)) • x∈fundamentalCompact N H) :
    (∑ i, c i*coordinate N ε t x (b i*g) (fundamentalSampling N hN H hε ht x v))=
      ∑ i, c i*fundamentalRawSampling N hN H hε t x v ((h i).val*(b i*g)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [fundamentalSampling_reduced_coordinate N hN H hε ht x hx v (h i) (b i*g) (hg i)]

#print axioms fundamentalSampling_coordinate
#print axioms fundamentalSampling_reduced_decode
#print axioms fundamentalSampling_row_coordinates

end QuantitativeSpectralObservability
