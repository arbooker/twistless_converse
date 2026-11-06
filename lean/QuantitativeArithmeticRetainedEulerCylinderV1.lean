module

public import QuantitativeArithmeticRetainedSectorReconstructionV1
public import QuantitativeArithmeticRetainedEnvelopeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedEulerCylinder

open AsymptoticCylinder AsymptoticSectorSigns FinitenessFourierConstruction
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open FinitenessPolynomialSeries FinitenessOriginalFourier
open QuantitativeArithmeticRetainedSectorReconstruction
open scoped BigOperators

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ)
    (hS : ∀p∈S,p.Prime)

include hS in
/-- The mixed direct-height estimate removes the individual growth
exponent from every original Euler solution. -/
theorem euler_mem_coefficientSpace (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h : ℕ)
    (f : FinitenessOriginalInput.S N (2*(h+1))) :
    fullCoefficients f.val (2*(h+1))∈coefficientSpace (h+1+P.s) := by
  obtain ⟨χ,_,hχ,hFE⟩ := FinitenessOriginalTwistedContinuations.solution_laws hN hQ f.property
  let a := fullCoefficients f.val (2*(h+1))
  have ha : PolynomialBound a := FinitenessOriginalDiskIndependence.polynomial N (2*(h+1)) f
  have ha0 : a 0=0 := fullCoefficients_zero f.property.zero _
  obtain ⟨M,hM0,_,hM⟩ := QuantitativeArithmeticRetainedEnvelope.global_bound hN A P hS hdiv
    (fourier a) (periodic a) χ (QuantitativeArithmeticRamifiedFullTrace.multiplier f.val (h+1)) (h+1)
    (fun q _ => hχ q)
    (fun p hp => QuantitativeArithmeticRamifiedFullTrace.multiplier_norm_le
      f.property.toEulerData (hS p hp) (hbad p hp) (h+1)) hFE
    (fun p hp _ hz => QuantitativeArithmeticRamifiedFullTrace.original_complete_even
      f.property.toEulerData (hS p hp) (hbad p hp) (by omega : 0<h+1) hz)
    (fun y hy => FinitenessCuspBounds.tail (fourier a) (sum a) (holomorphic ha) (zero ha0)
      (fun _ _ => rfl) (h+1+P.s) hy)
  exact ⟨ha0,M*Real.exp (2*Real.pi),mul_nonneg hM0 (Real.exp_pos _).le,
    AsymptoticCoefficientGrowth.coefficient_le_height_bound ha (h+1+P.s) hM⟩

def coefficients (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h : ℕ)
    (f : FinitenessOriginalInput.S N (2*(h+1))) : coefficientSpace (h+1+P.s) :=
  ⟨fullCoefficients f.val (2*(h+1)),euler_mem_coefficientSpace A hS hN P hdiv hbad h f⟩

/-- The geometric Fricke-and-ramified-sign sectors cover the original
solutions, with the uniform degree supplied by the mixed certificate. -/
theorem coefficient_cover (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h : ℕ)
    (f : FinitenessOriginalInput.S N (2*(h+1))) :
    ∃e : Sector N,coefficients A hS hN P hdiv hbad h f∈
      AsymptoticRamifiedSectors.sector N h (h+1+P.s) e := by
  obtain ⟨e,hd,hFE⟩ := AsymptoticSectorSigns.euler_sector hN f.property
  obtain ⟨τ,_,hg⟩ := f.property.growth
  refine ⟨e,?_,?_,?_⟩
  · intro Q' hQ'
    exact FinitenessTwistedAnalyticBridge.disk_mem_space hN hQ' f.property.zero hg
      (fun q hq => hFE q (Nat.pos_of_dvd_of_pos hq hQ'))
  · intro p hp n
    change fullCoefficients f.val (2*(h+1)) (p*n)=
      delta e p*(p:ℂ)^h*fullCoefficients f.val (2*(h+1)) n
    rw [hd p hp]
    obtain ⟨hp',hpN,_⟩ := mem_simplePrimes.mp hp
    exact AsymptoticRamifiedCoefficients.simple_relation f.property.toEulerData hp' hpN h n
  · intro p hp hpsq n
    exact AsymptoticRamifiedCoefficients.square_relation f.property.toEulerData hp hpsq (2*(h+1)) n

def eulerCylinder (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h t : ℕ)
    (hd : 2*(h+1+P.s)+4≤2*h+2*(t+1)+1)
    (f : FinitenessOriginalInput.S N (2*(h+1))) :
    holomorphicSpace (2*h) (t+1) (by positivity : 0<4*Real.pi) P.epsilon_pos :=
  fourierMap (2*h) (t+1) (h+1+P.s) (by positivity) P.epsilon_pos hd
    (coefficients A hS hN P hdiv hbad h f)

theorem eulerCylinder_independent (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h t : ℕ)
    (hd : 2*(h+1+P.s)+4≤2*h+2*(t+1)+1) :
    LinearIndependent ℂ (eulerCylinder A hS hN P hdiv hbad h t hd) := by
  have hc : LinearIndependent ℂ (coefficients A hS hN P hdiv hbad h) := by
    apply LinearIndependent.of_comp (coefficientSpace (h+1+P.s)).subtype
    exact FinitenessOriginalDiskIndependence.normalized_independent N (2*(h+1))
  exact hc.map' (fourierMap (2*h) (t+1) (h+1+P.s) (by positivity) P.epsilon_pos hd)
    (LinearMap.ker_eq_bot.mpr
      (fourierMap_injective (2*h) (t+1) (h+1+P.s) (by positivity) P.epsilon_pos hd))

theorem eulerCylinder_cover (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h t : ℕ)
    (hd : 2*(h+1+P.s)+4≤2*h+2*(t+1)+1)
    (f : FinitenessOriginalInput.S N (2*(h+1))) :
    ∃e : Sector N,eulerCylinder A hS hN P hdiv hbad h t hd f∈
      cylinderSector A P h (h+1+P.s) t e hd := by
  obtain ⟨e,he⟩ := coefficient_cover A hS hN P hdiv hbad h f
  exact ⟨e,⟨⟨coefficients A hS hN P hdiv hbad h f,he⟩,rfl⟩⟩

include hS in
/-- Literal Euler solution count bounded by the finite sum of the actual
mixed cylinder-sector dimensions. All cover and independence inputs are
proved from the original hypotheses. -/
theorem euler_count_le_cylinder_sectors (hN : 0<N) (P : Parameters A)
    (hdiv : ∀p∈S,p∣Q) (hbad : ∀p∈S,p∣N) (h t : ℕ)
    (hd : 2*(h+1+P.s)+4≤2*h+2*(t+1)+1) :
    (FinitenessOriginalInput.S N (2*(h+1))).Finite ∧
      (FinitenessOriginalInput.S N (2*(h+1))).ncard≤
        ∑e : Sector N,Module.finrank ℂ (cylinderSector A P h (h+1+P.s) t e hd) := by
  let _ : ∀e : Sector N,FiniteDimensional ℂ
      (cylinderSector A P h (h+1+P.s) t e hd) := fun e => by
    let _ := sector_finiteDimensional A hS hN P hdiv hbad h (h+1+P.s) e
    unfold cylinderSector
    infer_instance
  obtain ⟨hf,hb⟩ := FinitenessFiniteUnion.bound_sum
    (fun e => cylinderSector A P h (h+1+P.s) t e hd)
    (eulerCylinder A hS hN P hdiv hbad h t hd)
    (eulerCylinder_independent A hS hN P hdiv hbad h t hd)
    (eulerCylinder_cover A hS hN P hdiv hbad h t hd)
  exact ⟨Set.finite_coe_iff.mp hf,by simpa only [Nat.card_coe_set_eq] using hb⟩

#print axioms euler_mem_coefficientSpace
#print axioms coefficient_cover
#print axioms eulerCylinder_independent
#print axioms euler_count_le_cylinder_sectors
end QuantitativeArithmeticRetainedEulerCylinder
