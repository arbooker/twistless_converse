module

public import AsymptoticCylinderEmbeddingV1
public import AsymptoticCoefficientGrowthV1
public import FinitenessSignPatternsV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinder

open FinitenessPolynomialSeries FinitenessFourierConstruction
open FinitenessCertificate FinitenessGlobalHeight

/-- The canonical disk representative of a coefficient sequence. -/
noncomputable def coefficientDiskMap (d : ℕ) :
    coefficientSpace d →ₗ[ℂ] FinitenessDiskJet.space where
  toFun a := ⟨disk a.val,disk_holomorphic (coefficientSpace_polynomial d a)⟩
  map_add' a b := by
    apply Subtype.ext
    funext w
    change disk (a.val+b.val) w=disk a.val w+disk b.val w
    unfold disk
    split_ifs with hw
    · simp only [sum_eq_tsum,Pi.add_apply,add_mul]
      exact (summable (coefficientSpace_polynomial d a) hw).tsum_add
        (summable (coefficientSpace_polynomial d b) hw)
    · simp
  map_smul' c a := by
    apply Subtype.ext
    funext w
    change disk (c • a.val) w=c*disk a.val w
    unfold disk
    split_ifs
    · simp only [sum_eq_tsum,Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]
    · simp

theorem coefficientDiskMap_injective (d : ℕ) : Function.Injective (coefficientDiskMap d) := by
  intro a b hab
  apply Subtype.ext
  apply FinitenessPolynomialSeries.coefficients_unique
    (coefficientSpace_polynomial d a) (coefficientSpace_polynomial d b)
  intro w hw
  have he := congrFun (congrArg Subtype.val hab) w
  have hw' : ‖w‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hw
  change disk a.val w=disk b.val w at he
  simpa only [disk,ite_eq_left hw'] using he

/-- Fixed-multiplier cusp solutions, represented by their Fourier
coefficients. The degree is chosen from the direct-height certificate. -/
noncomputable def coefficientSector (N Q : ℕ) (χ : ℕ → ℂ) (m d : ℕ) :
    Submodule ℂ (coefficientSpace d) :=
  (FinitenessHolomorphicSpace.space N Q χ m).comap (coefficientDiskMap d)

noncomputable def sectorDiskMap (N Q : ℕ) (χ : ℕ → ℂ) (m d : ℕ) :
    coefficientSector N Q χ m d →ₗ[ℂ] FinitenessHolomorphicSpace.space N Q χ m :=
  ((coefficientDiskMap d).comp (coefficientSector N Q χ m d).subtype).codRestrict
    (FinitenessHolomorphicSpace.space N Q χ m) (fun a => a.property)

theorem sectorDiskMap_injective (N Q : ℕ) (χ : ℕ → ℂ) (m d : ℕ) :
    Function.Injective (sectorDiskMap N Q χ m d) := by
  intro a b hab
  apply Subtype.ext
  exact coefficientDiskMap_injective d (congrArg Subtype.val hab)

/-- These sectors are finite-dimensional by the already established
direct-height theorem, before any asymptotic trace comparison is made. -/
theorem coefficientSector_finiteDimensional {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (χ : ℕ → ℂ) (m d : ℕ) (hm : 0<m)
    (hχ : ∀ q, q∣Q → ‖χ q‖=1) :
    FiniteDimensional ℂ (coefficientSector N Q χ m d) := by
  obtain ⟨_,_,hb⟩ := FinitenessHolomorphicSpace.linear_bound hN A P
  let _ : FiniteDimensional ℂ (FinitenessHolomorphicSpace.space N Q χ m) := (hb χ m hm hχ).1
  apply FiniteDimensional.of_injective (V₂:=FinitenessHolomorphicSpace.space N Q χ m)
    (sectorDiskMap N Q χ m d)
  exact sectorDiskMap_injective N Q χ m d

noncomputable def sectorCylinderMap (N Q h d t : ℕ) (χ : ℕ → ℂ) {ε : ℝ}
    (hε : 0<ε) (hd : 2*d+4≤2*h+2*t+1) :
    coefficientSector N Q χ (h+1) d →ₗ[ℂ]
      holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) hε :=
  (fourierMap (2*h) t d (by positivity) hε hd).comp
    (coefficientSector N Q χ (h+1) d).subtype

theorem sectorCylinderMap_injective (N Q h d t : ℕ) (χ : ℕ → ℂ) {ε : ℝ}
    (hε : 0<ε) (hd : 2*d+4≤2*h+2*t+1) :
    Function.Injective (sectorCylinderMap N Q h d t χ hε hd) :=
  (fourierMap_injective (2*h) t d (by positivity) hε hd).comp Subtype.val_injective

theorem sectorCylinderMap_finrank (N Q h d t : ℕ) (χ : ℕ → ℂ) {ε : ℝ}
    (hε : 0<ε) (hd : 2*d+4≤2*h+2*t+1) :
    Module.finrank ℂ (LinearMap.range (sectorCylinderMap N Q h d t χ hε hd))=
      Module.finrank ℂ (coefficientSector N Q χ (h+1) d) :=
  LinearMap.finrank_range_of_inj (sectorCylinderMap_injective N Q h d t χ hε hd)

/-- Uniform degree for the normalized coefficients of every actual Euler
solution, with the constant still allowed to depend on the solution. -/
theorem euler_mem_coefficientSpace {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (m : ℕ)
    (f : FinitenessOriginalInput.S N (2*m)) :
    FinitenessOriginalFourier.fullCoefficients f.val (2*m)∈coefficientSpace (m+P.s) := by
  obtain ⟨χ,_,hχ,hFE⟩ := FinitenessOriginalTwistedContinuations.solution_laws hN hQ f.property
  have ha := FinitenessOriginalDiskIndependence.polynomial N (2*m) f
  have ha0 := FinitenessOriginalFourier.fullCoefficients_zero f.property.zero (2*m)
  exact ⟨ha0,AsymptoticCoefficientGrowth.uniform_degree hN A P χ m (fun q _ => hχ q)
    _ ha ha0 hFE⟩

noncomputable def eulerCoefficients {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (m : ℕ)
    (f : FinitenessOriginalInput.S N (2*m)) : coefficientSpace (m+P.s) :=
  ⟨FinitenessOriginalFourier.fullCoefficients f.val (2*m),euler_mem_coefficientSpace hN A P m f⟩

/-- The finite sign-pattern cover is preserved by the concrete Fourier
realization. Membership follows from the original Euler hypotheses. -/
theorem euler_sector_cover {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (m : ℕ)
    (f : FinitenessOriginalInput.S N (2*m)) :
    ∃ e : FinitenessSignPatterns.Pattern Q,
      eulerCoefficients hN A P m f∈coefficientSector N Q
        (FinitenessSignPatterns.multiplier Q m e) m (m+P.s) := by
  obtain ⟨e,he⟩ := FinitenessSignPatterns.cover hN hQ f
  exact ⟨e,he⟩

#print axioms coefficientDiskMap_injective
#print axioms coefficientSector_finiteDimensional
#print axioms sectorCylinderMap_finrank
#print axioms euler_mem_coefficientSpace
#print axioms euler_sector_cover

end AsymptoticCylinder
