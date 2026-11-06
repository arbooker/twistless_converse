module

public import QuantitativeEulerEndpointActualLogV1
public import QuantitativeEulerEndpointBaselineEnvelopeV1
public import QuantitativeEulerEndpointCombinedNormalizationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerEndpointNormalizedThreshold
open QuantitativeEulerEndpointPrimeBlocks
open scoped Classical MatrixGroups

/-- The actual baseline-plus-prime normalization has local logarithmic cost
O(4^j+n+1), including the baseline at EVERY block. -/
theorem exists_actual_combined_log_bound (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs ε : ℝ)
    (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀) (hG0 : 0≤G) (hC0 : 0≤C)
    (hK0 : 0≤Kobs) (hε : 0<ε) (t : ℕ) :
    ∃ Q : ℝ, 0≤Q ∧ ∀ n j : ℕ,
      let H := H₀*(4:ℝ)^n
      let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold₀ j
      let Y := min ε (1/4)
      let R := Bg*(D*H+2+1)/min 1 Y
      let Z := Y/wideDistortion Bg 2 (D*H)
      let L := (2*G*C)*X^4
      let height := L*(R+R+1)/min 1 Z
      let low := Z/wideDistortion L R R
      let O := sectorObservationCost N (NeZero.pos N) sector S hS W B H ε t
      let A := O*(Kobs*((wideDistortion L R R)^t)^2)
      let l := QuantitativeEulerEndpointPrimeBlocks.primes N hN excluded threshold₀ j
      let CB := prepend (wideDetectorBound N sector (height+1) low height t)
        (wideSequenceBound N (sign sector.1) (height+1) low height t l)
      Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor CB (l.length+1)*threshold A)^2)≤
        Q*((4:ℝ)^j+n+1) := by
  obtain ⟨Q₀,hQ₀,hprime⟩ := exists_actual_log_bound N hN excluded threshold₀ sector S hS W
    B Bg D H₀ G C Kobs ε (sign sector.1) hBg0 hD0 hH₀ hG0 hC0 hK0 hε t
  obtain ⟨Mbase,hMbase,hbase⟩ := exists_baseline_detector_envelope N sector
  let Y := min ε (1/4)
  have hY : 0<Y := lt_min hε (by norm_num)
  let f : Fin 8 → ℝ := ![4,Mbase,Bg,D,H₀,G,C,(min 1 Y)⁻¹]
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have hM4 : 4≤M := hf 0
  have hM1 : 1≤M := by linarith
  have hM0 : 0≤M := by linarith
  let a : ℝ := 2*Real.log (1+(36*9^t)^2)
  let b : ℝ := 4*(10+10*(t:ℝ))*36
  let Q := Q₀+a+b*envelopeConstant N hN excluded threshold₀ M
  have ha : 0≤a := mul_nonneg (by norm_num)
    (Real.log_nonneg (by nlinarith [sq_nonneg (36*9^t:ℝ)]))
  have hb : 0≤b := by dsimp only [b]; positivity
  have hQ : 0≤Q := by
    have hc := (QuantitativeEulerEndpointSparsePrefix.preparedPrefix N hN excluded threshold₀).constant_pos.le
    have hm := Real.log_nonneg hM1
    have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
    have h3 := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
    dsimp only [Q,envelopeConstant]
    exact add_nonneg (add_nonneg hQ₀ ha) (mul_nonneg hb (by positivity))
  refine ⟨Q,hQ,?_⟩
  intro n j H X Y' R Z L height low O A l CB
  let V := envelope N hN excluded threshold₀ M n j
  have hMV : M≤V := envelope_base N hN excluded threshold₀ hM0 n j
  have hV : 4≤V := hM4.trans hMV
  have hV1 : 1≤V := by linarith
  have hV0 : 0≤V := by linarith
  have hVU : V≤V^36 := by simpa only [pow_one] using pow_le_pow_right₀ hV1 (by norm_num : 1≤36)
  have hU : 1≤V^36 := one_le_pow₀ hV1
  have hX : X≤V := envelope_cutoff N hN excluded threshold₀ hM1 n j
  have hX0 : 0≤X := by linarith [bound_ge_three N hN excluded threshold₀ j]
  have hH : H≤V := envelope_height N hN excluded threshold₀ hM0 (hf 4) n j
  have hH0 : 0≤H := by dsimp only [H]; positivity
  obtain ⟨hh0,hh,hl,hlmin⟩ := wide_geometry_envelope Bg D H G C X Y V
    hV hBg0 ((hf 2).trans hMV) hD0 ((hf 3).trans hMV) hH0 hH
    hG0 ((hf 5).trans hMV) hC0 ((hf 6).trans hMV) hX0 hX hY ((hf 7).trans hMV)
  have hDbase := hbase (V^36) (((hf 1).trans hMV).trans hVU) (height+1) low height
    (by linarith) hh hh0 (by linarith) hl hlmin t
  have hDbase0 : 0≤wideDetectorBound N sector (height+1) low height t :=
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun i _ => wideBaselineRowBound_nonneg N sector _ _ _ t i))
  have hbaselog := log_square_polynomial (10+10*t) hDbase0
    (by positivity : (0:ℝ)≤36*9^t) hU hDbase
  rw [Real.log_pow] at hbaselog
  push_cast at hbaselog
  have hlogV : Real.log V≤envelopeConstant N hN excluded threshold₀ M*((4:ℝ)^j+n+1) :=
    envelope_log N hN excluded threshold₀ hM1 n j
  have he : 1≤(4:ℝ)^j+n+1 := by
    have hp : 0≤(4:ℝ)^j := by positivity
    have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
    linarith
  have hae := mul_le_mul_of_nonneg_left he ha
  have hbe := mul_le_mul_of_nonneg_left hlogV hb
  have hA0 : 0≤A := mul_nonneg
    (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W B H ε t)
    (mul_nonneg hK0 (sq_nonneg _))
  have hcombined := prepend_log_cost (wideDetectorBound N sector (height+1) low height t)
    (wideSequenceBound N (sign sector.1) (height+1) low height t l) l.length hA0
  have hpr := hprime n j
  change _≤Q₀*((4:ℝ)^j+n+1) at hpr
  dsimp only [Q,a,b] at *
  nlinarith only [hcombined,hpr,hbaselog,hae,hbe]

#print axioms exists_actual_combined_log_bound
end QuantitativeEulerEndpointPrepared
