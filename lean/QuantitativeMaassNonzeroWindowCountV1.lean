module

public import QuantitativeMaassNonzeroFilterV1
public import QuantitativeMaassEulerConcreteCompressionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns
open scoped BigOperators ContDiff

namespace QuantitativeMaass.EulerHilbert.Nonzero

variable {N Q : ℕ} {hQ : 0<Q} (A : FinitenessCertificate.Certificate N Q hQ)
  (hN : 0<N) (P : FinitenessGlobalHeight.Parameters A)

section WindowData

variable (σ : ℕ) (t ε : ℝ)

def windowSector (p : QuantitativeConcreteGoals.maassWindow N σ t ε) : Sector N :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose

def windowDatum (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose_spec.choose

theorem windowDatum_realizes (p : QuantitativeConcreteGoals.maassWindow N σ t ε) :
    physicalIsometry A hN P (windowSector A hN P σ t ε p) (windowDatum A hN P σ t ε p)=
      originalWindowClass hN A (AsymptoticReconstructedCount.parameters A P) σ t ε p :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose_spec.choose_spec.1

theorem windowDatum_fixed (p : QuantitativeConcreteGoals.maassWindow N σ t ε)
    (s : Set UpperHalfPlane) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ) :
    residualFilter A hN P (windowSector A hN P σ t ε p) hs qs d
      (windowDatum A hN P σ t ε p)=windowDatum A hN P σ t ε p :=
  (original_all_filters A hN P p.val.1 σ p.property.2.2).choose_spec.choose_spec.2 s hs qs d

/-- The actual normalized data remain independent within each finite root
sector, across different spectral parameters. -/
theorem windowDatum_sector_independent (e : Sector N) :
    LinearIndependent ℂ (fun p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
      windowSector A hN P σ t ε p=e} => windowDatum A hN P σ t ε p.val) := by
  apply LinearIndependent.of_comp (physicalIsometry A hN P e).toLinearMap
  have he (p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
      windowSector A hN P σ t ε p=e}) :
      physicalIsometry A hN P e (windowDatum A hN P σ t ε p.val)=
        originalWindowClass hN A (AsymptoticReconstructedCount.parameters A P) σ t ε p.val := by
    simpa only [p.property] using windowDatum_realizes A hN P σ t ε p.val
  simpa only [Function.comp_def,LinearMap.comp_apply,LinearIsometry.coe_toLinearMap,he] using!
    (originalWindowClass_independent hN A (AsymptoticReconstructedCount.parameters A P) σ t ε).comp
      (fun p : {p : QuantitativeConcreteGoals.maassWindow N σ t ε //
        windowSector A hN P σ t ε p=e} => p.val) Subtype.val_injective


end WindowData

/-- Literal original-window upper count from the actual normalized residual
compressions. Only spectral action and Hilbert--Schmidt summability remain
as analytic inputs. Sector choice, reconstruction, fixing and independence
are proved from the original Euler conditions. -/
theorem originalWindow_count_of_residual_compressions {ι : Type*}
    (σ : ℕ) (t ε : ℝ)
    (basis : HilbertBasis ι ℂ
      (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε))
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

/-- The exact original-window count for the constructed physical Abel
operator. Spectral action is discharged; the residual Hilbert--Schmidt
summability and the scalar window lower bound remain explicit inputs. -/
theorem originalWindow_count_concrete_abel {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) {ι : Type*}
    (σ : ℕ) (t ε : ℝ)
    (basis : HilbertBasis ι ℂ
      (terminalNonzeroModes (AsymptoticReconstructedCount.parameters A P).ε))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hsF : Function.support F⊆Iic (Real.cosh R))
    (s : Set UpperHalfPlane) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ)
    (hlower : ∀ r∈Icc t (t+ε),1≤(cosinePacket (coshTimeTest F) r).re)
    (hB : ∀ e : Sector N,Summable (fun i =>
      ‖filteredCompression (physicalIsometry A hN P e)
        (physicalCappedAbelOperator F hF hc R hR hsF
          (AsymptoticReconstructedCount.parameters A P).ε
          (AsymptoticReconstructedCount.parameters A P).epsilon_pos
          ((AsymptoticReconstructedCount.parameters A P).s+3))
        (residualFilter A hN P e hs qs d) (basis i)‖^2)) :
    (QuantitativeConcreteGoals.maassWindow N σ t ε).Finite ∧
      ((QuantitativeConcreteGoals.maassWindow N σ t ε).ncard : ℝ)≤
        ∑ e : Sector N,hilbertSchmidtEnergy basis
          (filteredCompression (physicalIsometry A hN P e)
            (physicalCappedAbelOperator F hF hc R hR hsF
              (AsymptoticReconstructedCount.parameters A P).ε
              (AsymptoticReconstructedCount.parameters A P).epsilon_pos
              ((AsymptoticReconstructedCount.parameters A P).s+3))
            (residualFilter A hN P e hs qs d)) := by
  apply originalWindow_count_of_residual_compressions A hN P σ t ε basis _ s hs qs d
    (fun r => (cosinePacket (coshTimeTest F) r).re) _ hlower hB
  intro p
  rw [cosinePacket_real (coshTimeTest F) (fun t => hr (Real.cosh t)) p.val.1]
  exact physicalCappedAbelOperator_original hN A (AsymptoticReconstructedCount.parameters A P)
    p.val.1 σ p.property.2.2 F hF hc hr R hR hsF


#print axioms windowDatum_realizes
#print axioms windowDatum_fixed
#print axioms windowDatum_sector_independent
#print axioms originalWindow_count_of_residual_compressions
#print axioms originalWindow_count_concrete_abel

end QuantitativeMaass.EulerHilbert.Nonzero
