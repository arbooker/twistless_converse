module

public import QuantitativeArithmeticRetainedFiniteCostsV1
public import QuantitativeArithmeticExponentialEnvelopeV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedScheduleGrowth
open QuantitativeArithmeticEnvelope
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight
open QuantitativeArithmeticRetainedFiniteNormalization
open QuantitativeArithmeticRetainedCylinderNormalization (bound bound_one_le gramLower gramLower_pos gramLower_le_one)
open QuantitativeHolomorphic.Schedule (binaryDepth binaryDepth_complexity amplification amplification_binaryDepth_le)

variable {N Q : ℕ} {S : Finset ℕ} {hQ : 0<Q} (A : Certificate N S Q hQ) (P : Parameters A)

def accuracy (u : ℝ) : ℝ := Real.exp (-u)
def tolerance (u : ℝ) : ℝ := rawTolerance A P (accuracy u)
def height (u : ℝ) : ℝ := lowerHeight A P (accuracy u)
def iterations (u : ℝ) : ℕ := newtonDepth A P (accuracy u)
def depth (u : ℝ) : ℕ := QuantitativeArithmeticRetainedFiniteSchedule.depth A P (tolerance A P u)
def cutoff (u : ℝ) : ℕ := QuantitativeArithmeticRetainedFiniteSchedule.cutoff A P (tolerance A P u)

theorem tolerance_pos (u : ℝ) : 0<tolerance A P u := rawTolerance_pos A P (Real.exp_pos _)
theorem height_pos (u : ℝ) : 0<height A P u := lowerHeight_pos A P (Real.exp_pos _)

def threshold (u : ℝ) : ℝ := Real.log (4/(accuracy u*Real.sqrt (gramLower A P)))/gramLower A P

theorem threshold_bounds : ∃K : ℝ,0≤K ∧ ∀u : ℝ,1≤u → 0≤threshold A P u ∧ threshold A P u≤K*u := by
  let c := gramLower A P
  let B := |Real.log 4|+|Real.log (Real.sqrt c)|
  have hc : 0<c := gramLower_pos A P
  have hc1 : c≤1 := gramLower_le_one A P
  have hs : 0<Real.sqrt c := Real.sqrt_pos.mpr hc
  have hs1 : Real.sqrt c≤1 := by simpa using Real.sqrt_le_sqrt hc1
  have hB : 0≤B := by dsimp only [B]; positivity
  refine ⟨(B+1)/c,by positivity,fun u hu => ?_⟩
  have ht : 0<accuracy u := Real.exp_pos _
  have ht1 : accuracy u≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hden : 0<accuracy u*Real.sqrt c := mul_pos ht hs
  have hden1 : accuracy u*Real.sqrt c≤1 := (mul_le_mul ht1 hs1 hs.le zero_le_one).trans_eq (one_mul _)
  have harg : 1≤4/(accuracy u*Real.sqrt c) := (le_div_iff₀ hden).mpr (by linarith)
  have he : Real.log (4/(accuracy u*Real.sqrt c))=Real.log 4+u-Real.log (Real.sqrt c) := by
    rw [Real.log_div (by norm_num : (4:ℝ)≠0) hden.ne',Real.log_mul ht.ne' hs.ne']
    simp only [accuracy,Real.log_exp]
    ring
  refine ⟨div_nonneg (Real.log_nonneg harg) hc.le,?_⟩
  change Real.log (4/(accuracy u*Real.sqrt c))/c≤(B+1)/c*u
  rw [he,div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hc.le
  have hb := mul_le_mul_of_nonneg_left hu hB
  dsimp only [B] at *
  nlinarith [le_abs_self (Real.log 4),neg_le_abs (Real.log (Real.sqrt c))]

/-- Newton degree is polynomial in log(1/accuracy); its amplification
is only exponential in a quadratic polynomial. -/
theorem newton_growth : Poly 2 (fun u => (4:ℝ)^iterations A P u) ∧
    Exp 2 (fun u => amplification (iterations A P u)) := by
  obtain ⟨K,hK,hx⟩ := threshold_bounds A P
  have hx2 (u : ℝ) (hu : 1≤u) : (threshold A P u+2)^2≤(K+2)^2*u^2 := by
    have hh : threshold A P u+2≤(K+2)*u := by nlinarith [(hx u hu).2]
    have hp := mul_self_le_mul_self (by linarith [(hx u hu).1] : 0≤threshold A P u+2) hh
    nlinarith only [hp]
  have hlog : 0≤3+Real.log 7 := by have := Real.log_nonneg (by norm_num : (1:ℝ)≤7); linarith
  constructor
  · refine ⟨4*(K+2)^2,by positivity,fun u hu => ?_⟩
    exact (binaryDepth_complexity _ (hx u hu).1).trans (by nlinarith only [hx2 u hu])
  · refine ⟨4*(3+Real.log 7)*(K+2)^2,by positivity,fun u hu => ?_⟩
    apply (amplification_binaryDepth_le (hx u hu).1).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hx2 u hu) (by positivity : 0≤4*(3+Real.log 7))]

theorem tolerance_inverse_growth : Exp 2 (fun u => (tolerance A P u)⁻¹) := by
  have ha := (newton_growth A P).2
  have he : Exp 2 (fun u => Real.exp u) := (Poly.id.weaken (by omega : 1≤2)).exp
  have hp := ((Exp.const 4 2).mul ha (fun u _ => (QuantitativeHolomorphic.Schedule.amplification_pos _).le)).mul
    he (fun u _ => Real.exp_nonneg _)
  apply hp.mono
  intro u _
  apply le_of_eq
  simp only [tolerance,rawTolerance,iterations,accuracy,Real.exp_neg]
  field_simp

theorem height_inverse_growth : Exp 2 (fun u => (height A P u)⁻¹) := by
  have hh := (Exp.const (bound A P/P.ε) 2).mul (tolerance_inverse_growth A P)
    (fun u _ => (inv_pos.mpr (tolerance_pos A P u)).le)
  apply hh.mono
  intro u _
  apply le_of_eq
  unfold height lowerHeight tolerance
  field_simp

theorem depth_growth : Poly 2 (fun u => (depth A P u:ℝ)) := by
  have hp := (Exp.const (2*bound A P) 2).mul (tolerance_inverse_growth A P)
    (fun u _ => (inv_pos.mpr (tolerance_pos A P u)).le)
  have he : Exp 2 (fun u => bound A P/(tolerance A P u/2)) := hp.mono (fun u _ => by ring_nf; rfl)
  exact he.binaryDepth (fun u _ => div_nonneg (zero_le_one.trans (bound_one_le A P)) (div_nonneg (tolerance_pos A P u).le (by norm_num)))

open QuantitativeArithmeticRetainedFiniteExpressions
open QuantitativeArithmeticRetainedCertificateOperators (terminalConstant)
open QuantitativeArithmeticRetainedPreparedReconstruction (exponent)

theorem foldNumerator_nonneg (n : ℕ) :
    0≤QuantitativeArithmeticRetainedFiniteSchedule.foldNumerator A P n := by
  have hl : 0≤lowTailConstant A := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _)
    cases i <;> simp only [rowLowTailCost,primitiveLowTailCost] <;> positivity
  have ht : 0≤terminalTailConstant A P := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _)
    cases i <;> simp only [rowTerminalTailCost,primitiveTerminalTailCost] <;> positivity
  have hT : 0≤1+terminalConstant A P := by
    have hb := bound_one_le A P
    change 1≤2*(1+terminalConstant A P) at hb
    linarith
  have hρ := P.rho_pos
  unfold QuantitativeArithmeticRetainedFiniteSchedule.foldNumerator
  positivity

theorem foldNumerator_growth :
    Exp 2 (fun u => QuantitativeArithmeticRetainedFiniteSchedule.foldNumerator A P (depth A P u)) := by
  have hj := (depth_growth A P).toExp
  have h1 := (Exp.const (terminalTailConstant A P) 2).mul hj (fun u _ => Nat.cast_nonneg _)
  have h2 := ((Exp.const (P.ρ^(exponent A P+3-1)*lowTailConstant A*(1+terminalConstant A P)) 2).mul
    hj (fun u _ => Nat.cast_nonneg _)).mul hj (fun u _ => Nat.cast_nonneg _)
  exact (h1.add h2).mono (fun u _ => by unfold QuantitativeArithmeticRetainedFiniteSchedule.foldNumerator; ring_nf; rfl)

theorem cutoff_growth : Exp 2 (fun u => (cutoff A P u:ℝ)) := by
  have hp := ((Exp.const 2 2).mul (foldNumerator_growth A P)
    (fun u _ => foldNumerator_nonneg A P _)).mul (tolerance_inverse_growth A P)
      (fun u _ => (inv_pos.mpr (tolerance_pos A P u)).le)
  have he : Exp 2 (fun u => QuantitativeArithmeticRetainedFiniteSchedule.foldNumerator A P (depth A P u)/
      (tolerance A P u/2)) := hp.mono (fun u _ => by ring_nf; rfl)
  exact he.ceil (fun u _ => div_nonneg (foldNumerator_nonneg A P _) (div_nonneg (tolerance_pos A P u).le (by norm_num)))

open QuantitativeArithmeticRetainedFiniteTransport

private theorem geometricLength (M n : ℕ) :
    (∑j∈Finset.range n,M^j)*(1+M)≤(2+M)^(n+1) := by
  have hs : (∑j∈Finset.range n,M^j)≤(2+M)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,pow_succ]
      have hp : M^n≤(2+M)^n := Nat.pow_le_pow_left (by omega) _
      calc
        _ ≤ (2+M)^n+(2+M)^n := add_le_add ih hp
        _ = (2+M)^n*2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  rw [pow_succ]
  exact Nat.mul_le_mul hs (by omega)

theorem rowLength_growth : Exp 2 (fun u => (certificateLength A (cutoff A P u):ℝ)) := by
  have hp := (((Exp.const 2 2).mul (cutoff_growth A P) (fun u _ => Nat.cast_nonneg _)).add
    (Exp.const 1 2)).mul (Exp.const (certificateLength A 0:ℝ) 2) (fun _ _ => Nat.cast_nonneg _)
  apply hp.mono
  intro u _
  exact_mod_cast certificateLength_linear A (cutoff A P u)

theorem rawLength_growth : Exp 4 (fun u => (rawLength A P (tolerance A P u):ℝ)) := by
  have hbase := (Exp.const 2 2).add (rowLength_growth A P)
  have hn : Poly 2 (fun u => ((depth A P u+1:ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (depth_growth A P).add (Poly.const 1 2)
  have hp := hbase.natpow (fun u _ => by positivity) (fun u => depth A P u+1) hn
  apply hp.mono
  intro u _
  exact_mod_cast geometricLength (certificateLength A (cutoff A P u)) (depth A P u)

theorem normalizedMass_growth : Exp 2 (fun u => (4:ℝ)^(4^iterations A P u)) := by
  have hn : Poly 2 (fun u => ((4^iterations A P u:ℕ):ℝ)) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using (newton_growth A P).1
  exact (Exp.const 4 0).natpow (fun _ _ => by norm_num) _ hn

theorem normalizedLength_growth : Exp 6 (fun u =>
    (rawLength A P (tolerance A P u):ℝ)*
      (3+(rawLength A P (tolerance A P u):ℝ)^2)^(4^iterations A P u)) := by
  have hr := rawLength_growth A P
  have hsq := hr.mul hr (fun u _ => Nat.cast_nonneg _)
  have hb : Exp 4 (fun u => 3+(rawLength A P (tolerance A P u):ℝ)^2) := by
    simpa only [pow_two] using (Exp.const 3 4).add hsq
  have hn : Poly 2 (fun u => ((4^iterations A P u:ℕ):ℝ)) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using (newton_growth A P).1
  have hp := hb.natpow (fun u _ => by positivity) _ hn
  exact (hr.weaken (by omega : 4≤6)).mul hp (fun u _ => by positivity)

theorem rawMatrix_growth (C : ℝ) (hC : 0≤C) :
    Exp 4 (fun u => scaledMatrixHeight A P C (tolerance A P u)) := by
  have hj := (Exp.const 1 2).add (cutoff_growth A P)
  have hb := (Exp.const (4*C) 2).mul hj (fun u _ => by positivity)
  have hp := hb.natpow (fun u _ => by positivity) _ (depth_growth A P)
  have hl := (Exp.const (2*C) 2).mul hj (fun u _ => by positivity)
  have hh := ((Exp.const 16 4).mul hp (fun u _ => by positivity)).mul
    (hl.weaken (by omega : 2≤4)) (fun u _ => by positivity)
  apply hh.mono
  intro u _
  apply le_of_eq
  unfold scaledMatrixHeight depth cutoff
  ring

theorem normalizedMatrix_growth (C : ℝ) (hC : 0≤C) : Exp 6 (fun u =>
    2*scaledMatrixHeight A P C (tolerance A P u)*
      (16*scaledMatrixHeight A P C (tolerance A P u)^2)^(4^iterations A P u)) := by
  have hM0 (u : ℝ) : 0≤scaledMatrixHeight A P C (tolerance A P u) := by
    unfold scaledMatrixHeight
    positivity
  have hr := rawMatrix_growth A P C hC
  have hsq := hr.mul hr (fun u _ => hM0 u)
  have hb : Exp 4 (fun u => 16*scaledMatrixHeight A P C (tolerance A P u)^2) := by
    simpa only [pow_two] using (Exp.const 16 4).mul hsq (fun u _ => mul_nonneg (hM0 u) (hM0 u))
  have hn : Poly 2 (fun u => ((4^iterations A P u:ℕ):ℝ)) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using (newton_growth A P).1
  have hp := hb.natpow (fun u _ => by positivity) _ hn
  exact ((Exp.const 2 6).mul (hr.weaken (by omega : 4≤6)) (fun u _ => hM0 u)).mul hp
    (fun u _ => by positivity)

/-- All complexity bounds for the actual common approximation are uniform
in the sector and weight; only the fixed mixed certificate enters C. -/
theorem uniform_cost (hS : ∀p∈S,p.Prime) (hN : 0<N) :
    ∃C : ℝ,1≤C ∧ ∀ (u : ℝ),1≤u → ∀e : AsymptoticSectorSigns.Sector N,
      AsymptoticFiniteBranch.expressionBound (normalizedExpression A P hS hN (accuracy u) e)≤Real.exp (C*u^6) ∧
      ((normalizedExpression A P hS hN (accuracy u) e).length:ℝ)≤Real.exp (C*u^6) ∧
      QuantitativeHolomorphic.ExpressionMatrixBound
        (normalizedExpression A P hS hN (accuracy u) e) (Real.exp (C*u^6)) ∧
      (height A P u)⁻¹≤Real.exp (C*u^6) := by
  obtain ⟨B,hB,hmat⟩ := normalized_matrix_bound A P hS hN
  obtain ⟨c₁,h₁,b₁⟩ := (normalizedMass_growth A P).weaken (by omega : 2≤6)
  obtain ⟨c₂,h₂,b₂⟩ := normalizedLength_growth A P
  obtain ⟨c₃,h₃,b₃⟩ := normalizedMatrix_growth A P B (zero_le_one.trans hB)
  obtain ⟨c₄,h₄,b₄⟩ := (height_inverse_growth A P).weaken (by omega : 2≤6)
  let C := 1+c₁+c₂+c₃+c₄
  have hC : 1≤C := by dsimp only [C]; linarith
  refine ⟨C,hC,fun u hu e => ?_⟩
  have hpow : 0≤u^6 := pow_nonneg (zero_le_one.trans hu) _
  have hdom {c : ℝ} (hc : c≤C) : Real.exp (c*u^6)≤Real.exp (C*u^6) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc hpow)
  have hb₁ := (b₁ u hu).trans (hdom (by dsimp only [C]; linarith : c₁≤C))
  have hb₂ := (b₂ u hu).trans (hdom (by dsimp only [C]; linarith : c₂≤C))
  have hb₃ := (b₃ u hu).trans (hdom (by dsimp only [C]; linarith : c₃≤C))
  have hb₄ := (b₄ u hu).trans (hdom (by dsimp only [C]; linarith : c₄≤C))
  refine ⟨(normalized_mass A P hS hN _ e).trans hb₁,?_,(hmat _ e).mono hb₃,hb₄⟩
  have hl := normalized_length A P hS hN (accuracy u) e
  have hl' : ((normalizedExpression A P hS hN (accuracy u) e).length:ℝ)≤
      (rawLength A P (tolerance A P u):ℝ)*
        (3+(rawLength A P (tolerance A P u):ℝ)^2)^(4^iterations A P u) := by exact_mod_cast hl
  exact hl'.trans hb₂

#print axioms uniform_cost
#print axioms rawLength_growth
#print axioms normalizedMass_growth
#print axioms normalizedLength_growth
#print axioms normalizedMatrix_growth
#print axioms newton_growth
#print axioms tolerance_inverse_growth
#print axioms height_inverse_growth
#print axioms depth_growth
#print axioms cutoff_growth
end QuantitativeArithmeticRetainedScheduleGrowth
