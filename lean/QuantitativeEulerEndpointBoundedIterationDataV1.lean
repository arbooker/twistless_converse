module

public import QuantitativeEulerEndpointBoundedTerminalScheduleV1
public import QuantitativeEulerEndpointBoundedTerminalSupportV1

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBoundedIteration
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeEulerEndpointPrepared QuantitativeEulerEndpointTerminalAlgebra Polynomial
open QuantitativeEulerEndpointExponentialParameters QuantitativeEulerEndpointBlocks
open AsymptoticSubgroupSupport AsymptoticIntegralSubgroup

variable {N Q : ℕ} [NeZero N] {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A) (e : Sector N)

/-- Actual observation region, prime list and threshold of a normalized terminal block. -/
structure Block where
  region : Set UpperHalfPlane
  compact : IsCompact region
  primes : List (EligiblePrime N)
  cutoff : ℝ
  bound : ℕ → ℝ
  norm_bound : ∀ i x,‖normalizedCombinedRows A P e compact primes i x‖≤bound i

variable (n : ℕ) (b : ℕ → Block A P e)
local notation "area" => (AsymptoticReconstructedCount.parameters A P).ε⁻¹

def effortAt (j : ℕ) : ℝ := QuantitativeEulerEndpointBoundedTerminal.effort
  (b j).primes (b j).bound n j (b j).cutoff

def sharpnessAt (j : ℕ) : ℕ := sharpness area (effortAt A P e n b j)

def nextAt (j : ℕ) (F : Algebra A P) (z : ℝ[X]) : Algebra A P :=
  QuantitativeEulerEndpointBoundedTerminal.next A P e (b j).compact (b j).primes (b j).bound (b j).norm_bound F
    (power (effortAt A P e n b j)) z

/-- Checked properties retained from one scheduled polynomial update. -/
structure Step (target : ℝ) (j : ℕ) (F : Algebra A P) (z : ℝ[X]) : Prop where
  degree : z.natDegree≤16*(sharpnessAt A P e n b (j+1))^5+1
  mass : (∑ i∈z.support,|z.coeff i|)≤
    (((16*(sharpnessAt A P e n b (j+1))^5:ℕ):ℝ)+2)*3^(16*(sharpnessAt A P e n b (j+1))^5)
  scalar : QuantitativeEulerEndpointBernstein.ScalarSharpening z
  nonneg : 0≤nextAt A P e n b j F z
  le : nextAt A P e n b j F z≤F
  defect : tr A P (nextAt A P e n b j F z-(nextAt A P e n b j F z)^2)≤
    4*area/(sharpnessAt A P e n b (j+1):ℝ)
  fixed : ∀ D : Algebra A P,F*D=D →
    (∀ i : Fin ((b j).primes.length+1),∀ x,
      normalizedCombinedRows A P e (b j).compact (b j).primes i x*rep A P D x=0) →
    nextAt A P e n b j F z*D=D
  excess : max 0 (tr A P (nextAt A P e n b j F z)-target)≤
    (((b j).primes.map primeFactor).prod+2*blockRelativeLoss n j)*max 0 (tr A P F-target)+
      (1+area*Real.log 2)*blockAdditiveLoss n j

/-- The incoming sharpening pays the current block, and the outgoing
sharpening is chosen from the NEXT block's actual effort. -/
theorem exists_step (j : ℕ) (hj : j≤n) (F : Algebra A P) (hF0 : 0≤F) (hF1 : F≤1)
    (target : ℝ) (hc : 0<(b j).cutoff)
    (hu : QuantitativeEulerEndpointBlockNormalization.factor
      (b j).bound ((b j).primes.length+1)*(b j).cutoff≤1)
    (hchain : cornerMass (fun x => QuantitativeSpectralDeflationChain.chain (half A P F x)
      (fun i => normalizedCombinedRows A P e (b j).compact (b j).primes i x)
      (b j).cutoff ((b j).primes.length+1))-target≤
      ((b j).primes.map primeFactor).prod*(cornerMass (half A P F)-target))
    (hdef : tr A P (F-F^2)≤4*area/(sharpnessAt A P e n b j:ℝ)) :
    ∃ z,Step A P e n b target j F z := by
  obtain ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,hrec⟩ :=
    QuantitativeEulerEndpointBoundedTerminal.exists_scheduled_next A P e (b j).compact (b j).primes (b j).bound (b j).norm_bound
      n j hj F hF0 hF1 target (b j).cutoff hc hu hchain hdef
      (sharpness_pos area (effortAt A P e n b (j+1)))
  exact ⟨z,hdeg,hmass,hscalar,hz0,hzF,hzdef,hfixed,hrec⟩

#print axioms exists_step
end QuantitativeEulerEndpointBoundedIteration
