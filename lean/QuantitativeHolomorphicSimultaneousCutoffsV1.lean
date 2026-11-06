module

public import QuantitativeHolomorphicCutoffScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def amplification (n : ℕ) : ℝ := (1+3*(3^n:ℕ))*(7:ℝ)^(4^n)

theorem amplification_pos (n : ℕ) : 0<amplification n := by unfold amplification; positivity

def reconstructionDepth (P : Parameters A) (D t : ℝ) (n : ℕ) : ℕ :=
  binaryDepth ((2*AsymptoticCertificateOperators.terminalConstant A
    (AsymptoticReconstructedCount.parameters A P)*amplification n*D)/(t/4))

def foldCutoff (P : Parameters A) (D t : ℝ) (j n : ℕ) : ℕ :=
  ⌈(reconstructionFoldTailConstant A (AsymptoticReconstructedCount.parameters A P) j*
    amplification n*D)/(t/4)⌉₊+1

def lowerCutoff (P : Parameters A) (D t : ℝ) (n : ℕ) : ℝ :=
  (AsymptoticReconstructedCount.parameters A P).ε/countReconstructionBound A P *
    (t/4)/(amplification n*D)

theorem reciprocal_ceil_bound {B t : ℝ} (ht : 0<t) :
    B/((⌈B/t⌉₊+1:ℕ):ℝ)≤t := by
  have hJ : 0<((⌈B/t⌉₊+1:ℕ):ℝ) := by positivity
  have hc := Nat.le_ceil (B/t)
  have hb : B/t≤((⌈B/t⌉₊+1:ℕ):ℝ) := by push_cast; linarith
  have h := (div_le_iff₀ ht).mp hb
  exact (div_le_iff₀ hJ).mpr (by nlinarith)

theorem countFilterError_pos (P : Parameters A) {Y : ℝ} (hY : 0<Y) (j J n d : ℕ) :
    0<countFilterError A P Y j J n d := by
  let P' := AsymptoticReconstructedCount.parameters A P
  have hε : 0<P'.ε := P'.epsilon_pos
  have hρ : 0<P'.ρ := P'.rho_pos
  have hT : 0≤AsymptoticCertificateOperators.terminalConstant A P' := by
    unfold AsymptoticCertificateOperators.terminalConstant
    positivity
  have hF : 0≤reconstructionFoldTailConstant A P' j := by
    unfold reconstructionFoldTailConstant terminalFoldTailConstant lowFoldTailConstant AsymptoticCertificateBranches.level
    positivity
  have hB : 0<countReconstructionBound A P :=
    lt_of_lt_of_le zero_lt_one (countReconstructionBound_one_le A P)
  have hc : 0≤1-countGramLower A P := sub_nonneg.mpr (countGramLower_le_one A P)
  unfold countFilterError normalizedCutError cutCountReconstructionError countReconstructionError
  change 0<(2*d+2:ℝ)*((reconstructionFoldTailConstant A P' j/(J:ℝ)+
    2*AsymptoticCertificateOperators.terminalConstant A P'*(1/2:ℝ)^j+
    Y/P'.ε*countReconstructionBound A P)*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
    (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P))
  positivity

/-- All finite reconstruction cutoffs are selected explicitly from the desired
error. The Newton cutoff is logarithmic in its exponential accuracy parameter;
Neumann depth is binary-logarithmic in the amplification, and the fold cutoff
is a literal natural ceiling. No small-error hypothesis is supplied. -/
theorem countFilterError_schedule (P : Parameters A) (d : ℕ) {t : ℝ} (ht : 0<t) :
    let D : ℝ := 2*d+2
    let n := newtonDepth A P D t
    let j := reconstructionDepth A P D t n
    let J := foldCutoff A P D t j n
    let Y := lowerCutoff A P D t n
    0<J ∧ 0<Y ∧ 0<countFilterError A P Y j J n d ∧ countFilterError A P Y j J n d≤t := by
  let D : ℝ := 2*d+2
  let n := newtonDepth A P D t
  let j := reconstructionDepth A P D t n
  let J := foldCutoff A P D t j n
  let Y := lowerCutoff A P D t n
  let P' := AsymptoticReconstructedCount.parameters A P
  let T := AsymptoticCertificateOperators.terminalConstant A P'
  let F := reconstructionFoldTailConstant A P' j
  let C := amplification n
  let B := countReconstructionBound A P
  have hD : 0<D := by dsimp [D]; positivity
  have hC : 0<C := amplification_pos n
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (countReconstructionBound_one_le A P)
  have hε : 0<P'.ε := P'.epsilon_pos
  have ht4 : 0<t/4 := by positivity
  have hJ : 0<J := by dsimp [J,foldCutoff]; omega
  have hY : 0<Y := by dsimp [Y,lowerCutoff]; exact div_pos (mul_pos (div_pos hε hB) ht4) (mul_pos hC hD)
  refine ⟨hJ,hY,countFilterError_pos A P hY j J n d,?_⟩
  have hf : (F*C*D)/(J:ℝ)≤t/4 := reciprocal_ceil_bound ht4
  have hn : (2*T*C*D)*(1/2:ℝ)^j≤t/4 := geometric_depth_bound ht4
  have hy : D*(Y/P'.ε*B*C)=t/4 := by
    change D*((P'.ε/B*(t/4)/(C*D))/P'.ε*B*C)=t/4
    field_simp [hε.ne',hB.ne',hC.ne',hD.ne']
  have hnew := newtonDepth_error A P hD ht
  change D*((F/(J:ℝ)+2*T*(1/2:ℝ)^j+Y/P'.ε*B)*(1+3*(3^n:ℕ))*(7:ℝ)^(4^n)+
    (1-countGramLower A P)^(2^n)/Real.sqrt (countGramLower A P))≤t
  have hfold : D*(F/(J:ℝ)*C)≤t/4 := by
    convert hf using 1
    ring
  dsimp only [C,amplification] at hfold hn hy
  nlinarith only [hfold,hn,hy,hnew]

#print axioms countFilterError_schedule

end QuantitativeHolomorphic.Schedule
