module

public import QuantitativeArithmeticRetainedCylinderNormalizationV1
public import QuantitativeArithmeticRamifiedFullTraceV1
public import AsymptoticSectorReconstructionV1
public import QuantitativeArithmeticRetainedHolomorphicSpaceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedSectorReconstruction

open MeasureTheory ContinuousLinearMap AsymptoticSectorSigns AsymptoticCylinder
open FinitenessFourierConstruction AsymptoticRamifiedSectors
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight

/-- The actual ramified parameter in a geometric sign sector: zero at
square-dividing primes and the prescribed sign at simple primes. -/
def ramifiedParameter {N : ℕ} (e : Sector N) (p : ℕ) : ℂ :=
  if p^2∣N then 0 else delta e p

theorem ramifiedParameter_norm {N : ℕ} (e : Sector N) (p : ℕ) :
    ‖ramifiedParameter e p‖≤1 := by
  unfold ramifiedParameter
  split_ifs <;> simp [delta_norm]

/-- Every vector in the original linear coefficient sector supplies the
complete retained row; this is not an extra hypothesis on an eigenform. -/
theorem sector_complete {N h d : ℕ} (e : Sector N)
    (a : sector N h d e) {p : ℕ} (hp : p.Prime) (hpN : p∣N)
    {z : ℂ} (hz : 0<z.im) :
    QuantitativeArithmeticRetainedReconstruction.completeTwist (fourier a.val.val) p z=
      (ramifiedParameter e p*(p:ℂ)^(h+1))*fourier a.val.val ((p:ℂ)*z) := by
  have hrow : ∀n,a.val.val (p*n)=(ramifiedParameter e p*(p:ℂ)^h)*a.val.val n := by
    intro n
    by_cases hs : p^2∣N
    · simp only [ramifiedParameter,ite_eq_left hs,zero_mul]
      exact a.property.2.2 p hp hs n
    · simpa only [ramifiedParameter,ite_eq_right hs] using
        a.property.2.1 p (mem_simplePrimes.mpr ⟨hp,hpN,hs⟩) n
  rw [QuantitativeArithmeticRamifiedFullTrace.complete_of_row a.val.val
    (coefficientSpace_polynomial d a.val) hp.pos _ hrow hz]
  simp only [pow_succ]
  ring

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime)

include hS in
/-- The original linear coefficient sector embeds in the already proved
mixed disk-law space. Hence its finite dimensionality uses the retained
certificate, not the stronger primitive-only spanning hypothesis. -/
theorem sector_finiteDimensional (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h d : ℕ) (e : Sector N) :
    FiniteDimensional ℂ (sector N h d e) := by
  let b : ℕ → ℂ := fun p => ramifiedParameter e p*(p:ℂ)^(h+1)
  let V := QuantitativeArithmeticRetainedHolomorphicSpace.space N Q S (multiplier e) b (h+1)
  obtain ⟨C,hC,hbound⟩ := QuantitativeArithmeticRetainedHolomorphicSpace.linear_bound
    hN A P hS hdiv
  let _ : FiniteDimensional ℂ V := (hbound (multiplier e) b (h+1) (by omega)
    (fun q _ => multiplier_norm e q) (by
      intro p _
      dsimp [b]
      rw [norm_mul,norm_pow,Complex.norm_natCast]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (ramifiedParameter_norm e p) (by positivity : 0≤(p:ℝ)^(h+1)))).1
  have hmem (a : sector N h d e) : coefficientDiskMap d a.val∈V := by
    refine ⟨a.property.1 Q hQ,?_⟩
    intro p hp z hz
    have he (w : ℂ) (hw : 0<w.im) :
        FinitenessHolomorphicSpace.lift (disk a.val.val) w=fourier a.val.val w :=
      disk_eq_fourier _ hw
    have ht : QuantitativeArithmeticRetainedReconstruction.completeTwist
        (FinitenessHolomorphicSpace.lift (disk a.val.val)) p z=
        QuantitativeArithmeticRetainedReconstruction.completeTwist (fourier a.val.val) p z := by
      unfold QuantitativeArithmeticRetainedReconstruction.completeTwist
      apply Finset.sum_congr rfl
      intro u _
      apply he
      simpa using hz
    change QuantitativeArithmeticRetainedReconstruction.completeTwist
      (FinitenessHolomorphicSpace.lift (disk a.val.val)) p z=
      b p*FinitenessHolomorphicSpace.lift (disk a.val.val) ((p:ℂ)*z)
    rw [ht,he _ (QuantitativeArithmeticRamifiedFullTrace.dilation_height (hS p hp).pos hz)]
    exact sector_complete e a (hS p hp) (hbad p hp) hz
  let j : sector N h d e →ₗ[ℂ] V :=
    ((coefficientDiskMap d).comp (sector N h d e).subtype).codRestrict V hmem
  apply FiniteDimensional.of_injective (V₂:=V) j
  intro a b hab
  apply Subtype.ext
  exact coefficientDiskMap_injective d (congrArg Subtype.val hab)

/-- The same original coefficient sector, realized at one extra capped
weight. The degree and base exponent are explicit, with no primitive-only
certificate hidden in the definition. -/
def cylinderSector (P : Parameters A) (h d t : ℕ) (e : Sector N)
    (hd : 2*d+4≤2*h+2*(t+1)+1) :
    Submodule ℂ (holomorphicSpace (2*h) (t+1) (by positivity : 0<4*Real.pi) P.epsilon_pos) :=
  LinearMap.range (cylinderMap N h d (t+1) e P.epsilon_pos hd)

theorem cylinderSector_finrank (P : Parameters A) (h d t : ℕ) (e : Sector N)
    (hd : 2*d+4≤2*h+2*(t+1)+1) :
    Module.finrank ℂ (cylinderSector A P h d t e hd)=Module.finrank ℂ (sector N h d e) :=
  cylinderMap_finrank N h d (t+1) e P.epsilon_pos hd

/-- Mixed reconstruction recovers every vector of the original sector
from its terminal restriction, using only its defining twist and ramified laws. -/
theorem sector_reconstructed (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (h d t : ℕ) (ht : 2≤t) (hd : 2*d+4≤2*h+2*t+1) (e : Sector N)
    (hK : ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) t (h+1)‖<1)
    (w : holomorphicSpace (2*h) (t+1) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈cylinderSector A P h d t e (by omega)) :
    ∃g : AsymptoticCylinderTerminal.Space P.ε,
      (inclusion P.epsilon_pos).comp
        (QuantitativeArithmeticRetainedCylinderExtension.extension A hS hN P
          (multiplier e) (ramifiedParameter e) ht (h+1)) g=(w:Space) := by
  obtain ⟨a,rfl⟩ := hw
  let f : Space := (fourierMap (2*h) t d (by positivity) P.epsilon_pos hd a.val :
    holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) P.epsilon_pos)
  let g := AsymptoticRegionL2.restrict measure (AsymptoticCylinderTerminal.region P.ε)
    (AsymptoticCylinderTerminal.region_measurable P.ε) f
  have hFE := AsymptoticSectorReconstruction.coefficientSector_laws hN hQ
    (multiplier e) (h+1) d a.val (a.property.1 Q hQ)
  have he := QuantitativeArithmeticRetainedCylinderExtension.extension_of_FE A hS hN P hdiv
    (multiplier e) (ramifiedParameter e) ht (h+1)
    (fourier a.val.val) (periodic a.val.val) hFE
    (fun p hp _ hz => sector_complete e a (hS p hp) (hbad p hp) hz) f
    (AsymptoticCylinderLift.lift_fourierMap h t d P.epsilon_pos hd a.val) hK
  refine ⟨g,?_⟩
  change inclusion P.epsilon_pos (QuantitativeArithmeticRetainedCylinderExtension.extension A hS hN P
    (multiplier e) (ramifiedParameter e) ht (h+1) g)=_
  rw [he]
  exact AsymptoticSectorReconstruction.fourierMap_inclusion h t d P.epsilon_pos hd (by omega) a.val

/-- Normalizing the actual reconstruction changes its coordinates on
terminal data but preserves every original sector vector in its range. -/
theorem sector_normalized (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N)
    (h d t : ℕ) (ht : 2≤t) (hd : 2*d+4≤2*h+2*t+1) (e : Sector N)
    (hK : ‖QuantitativeArithmeticRetainedCertificateOperators.low A hS hN P
      (multiplier e) (ramifiedParameter e) t (h+1)‖<1/2)
    (w : holomorphicSpace (2*h) (t+1) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈cylinderSector A P h d t e (by omega)) :
    ∃g : AsymptoticCylinderTerminal.Space P.ε,
      QuantitativeArithmeticRetainedCylinderNormalization.normalized A hS hN P
        (multiplier e) (ramifiedParameter e) ht (h+1) g=(w:Space) := by
  obtain ⟨g,hg⟩ := sector_reconstructed A hS hN P hdiv hbad h d t ht hd e
    (hK.trans (by norm_num)) w hw
  let R := QuantitativeArithmeticRetainedCylinderNormalization.scaled A hS hN P
    (multiplier e) (ramifiedParameter e) ht (h+1)
  let B := QuantitativeArithmeticRetainedCylinderNormalization.bound A P
  have hB : B≠0 := (zero_lt_one.trans_le
    (QuantitativeArithmeticRetainedCylinderNormalization.bound_one_le A P)).ne'
  have hr : R (B • g)=(w:Space) := by
    change (B⁻¹:ℝ) • ((inclusion P.epsilon_pos).comp
      (QuantitativeArithmeticRetainedCylinderExtension.extension A hS hN P
        (multiplier e) (ramifiedParameter e) ht (h+1)) (B • g))=_
    rw [map_smul_of_tower,hg,smul_smul,inv_mul_cancel₀ hB,one_smul]
  refine ⟨(R.adjoint.comp R).comp
    (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)) (B • g),?_⟩
  exact (QuantitativeHolomorphic.normalizedReconstruction_reconstruct R
    (QuantitativeArithmeticRetainedCylinderNormalization.gramLower_pos A P)
    (QuantitativeArithmeticRetainedCylinderNormalization.scaled_bounds A hS hN P
      (multiplier e) (ramifiedParameter e) (fun q _ => multiplier_norm e q)
      (fun p _ => ramifiedParameter_norm e p) ht (h+1) hK).2 (B • g)).trans hr

#print axioms sector_normalized
#print axioms ramifiedParameter_norm
#print axioms sector_complete
#print axioms sector_finiteDimensional
#print axioms cylinderSector_finrank
#print axioms sector_reconstructed
end QuantitativeArithmeticRetainedSectorReconstruction
