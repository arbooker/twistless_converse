module

public import QuantitativeMaassEulerWindowDataV1
public import QuantitativeMaassIsometricCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns
open scoped BigOperators

namespace QuantitativeMaass.EulerHilbert

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

/-- Literal original-window upper count from the actual normalized residual
compressions. Only spectral action and Hilbert--Schmidt summability remain
as analytic inputs. Sector choice, reconstruction, fixing and independence
are proved from the original Euler conditions. -/
theorem originalWindow_count_of_residual_compressions {ι : Type*}
    (σ : ℕ) (t ε : ℝ)
    (basis : HilbertBasis ι ℂ
      (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (K : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticHyperbolicSlash.Space)
    (s : Set UpperHalfPlane) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) (h : ℝ → ℝ)
    (heigen : ∀ p : QuantitativeConcreteGoals.maassWindow N σ t ε,
      K (originalWindowClass hN A (AsymptoticReconstructedCount.parameters A P) σ t ε p)=
        (h p.val.1 : ℂ) • originalWindowClass hN A
          (AsymptoticReconstructedCount.parameters A P) σ t ε p)
    (hlower : ∀ r ∈ Icc t (t+ε),1≤h r)
    (hB : ∀ e : Sector N,Summable (fun i =>
      ‖filteredCompression (physicalIsometry A hN P e) K (residualFilter A hN P e hs qs d) (basis i)‖^2)) :
    (QuantitativeConcreteGoals.maassWindow N σ t ε).Finite ∧
      ((QuantitativeConcreteGoals.maassWindow N σ t ε).ncard : ℝ) ≤
        ∑ e : Sector N,hilbertSchmidtEnergy basis
          (filteredCompression (physicalIsometry A hN P e) K (residualFilter A hN P e hs qs d)) := by
  classical
  let W := QuantitativeConcreteGoals.maassWindow N σ t ε
  let sector : W → Sector N := windowSector A hN P σ t ε
  let V (e : Sector N) := {p : W // sector p=e}
  let B (e : Sector N) := filteredCompression (physicalIsometry A hN P e) K
    (residualFilter A hN P e hs qs d)
  have hc (e : Sector N) : Finite (V e) ∧
      (Nat.card (V e) : ℝ)≤hilbertSchmidtEnergy basis (B e) := by
    apply filteredCompression_count (physicalIsometry A hN P e) K
      (residualFilter A hN P e hs qs d) basis
      (fun p : V e => windowDatum A hN P σ t ε p.val)
      (windowDatum_sector_independent A hN P σ t ε e) (fun p => h p.val.val.1)
    · intro p
      have hf := windowDatum_fixed A hN P σ t ε p.val s hs qs d
      change residualFilter A hN P (sector p.val) hs qs d _=_ at hf
      simpa only [p.property] using hf
    · intro p
      have hr := windowDatum_realizes A hN P σ t ε p.val
      change physicalIsometry A hN P (sector p.val) _=_ at hr
      rw [p.property] at hr
      rw [hr]
      exact heigen p.val
    · intro p
      exact hlower p.val.val.1 p.val.property.2.1
    · exact hB e
  let : ∀ e : Sector N,Finite (V e) := fun e => (hc e).1
  let : Finite W := Finite.of_equiv (Σ e : Sector N,V e) (Equiv.sigmaFiberEquiv sector)
  refine ⟨Set.toFinite _,?_⟩
  have hcard : Nat.card W=∑ e : Sector N,Nat.card (V e) := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv sector),Nat.card_sigma]
  change (W.ncard : ℝ)≤∑ e : Sector N,hilbertSchmidtEnergy basis (B e)
  rw [← Nat.card_coe_set_eq,hcard,Nat.cast_sum]
  exact Finset.sum_le_sum (fun e _ => (hc e).2)

#print axioms originalWindow_count_of_residual_compressions

end QuantitativeMaass.EulerHilbert
