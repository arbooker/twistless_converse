module

public import QuantitativeEulerEndpointPreparedGrowthV1
public import QuantitativeEulerEndpointCommonEnvelopeV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerEndpointNormalizedThreshold
open QuantitativeEulerEndpointPrimeBlocks
open scoped Classical MatrixGroups

/-- Actual prepared prime lists and their actual observation geometry
have logarithmic normalization cost O(4^j+n+1). No row-growth or
prime-product bound is an input. All constants are fixed before n,j. -/
theorem exists_actual_log_bound (N : ℕ) [NeZero N] (hN : 2≤N)
    (excluded : Finset ℕ) (threshold₀ : ℕ) (sector : Sector N)
    (S : Finset SL(2,ℤ)) (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs ε : ℝ) (w : ℂ)
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
      Real.log (2/(QuantitativeEulerEndpointBlockNormalization.factor
        (wideSequenceBound N w (height+1) low height t l) l.length*threshold A)^2)≤
        Q*((4:ℝ)^j+n+1) := by
  let Y := min ε (1/4)
  have hY : 0<Y := lt_min hε (by norm_num)
  obtain ⟨Mobs,hMobs,hobs⟩ := exists_sector_observation_envelope N (NeZero.pos N) sector S hS W B ε
  let f : Fin 11 → ℝ := ![4,Mobs,Bg,D,H₀,G,C,Kobs,(N:ℝ),‖w‖,(min 1 Y)⁻¹]
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have hM4 : 4≤M := hf 0
  have hM1 : 1≤M := by linarith
  have hM0 : 0≤M := by linarith
  let a : ℝ := Real.log 4+Real.log 3+2*Real.log (1+(72*9^t)^2)
  let b : ℝ := ((8+124*(t:ℝ))+2*(1+2*(9+10*t)))*36
  let Q := a+b*envelopeConstant N hN excluded threshold₀ M
  have ha : 0≤a := by
    dsimp only [a]
    exact add_nonneg (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num)))
      (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith [sq_nonneg (72*9^t:ℝ)])))
  have hb : 0≤b := by dsimp only [b]; positivity
  have hQ : 0≤Q := by
    have hc := (QuantitativeEulerEndpointSparsePrefix.preparedPrefix N hN excluded threshold₀).constant_pos.le
    have hm := Real.log_nonneg hM1
    have h4 := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
    have h3 := Real.log_nonneg (by norm_num : (1:ℝ)≤3)
    dsimp only [Q,envelopeConstant]
    exact add_nonneg ha (mul_nonneg hb (by positivity))
  refine ⟨Q,hQ,?_⟩
  intro n j H X Y' R Z L height low O A l
  let V := envelope N hN excluded threshold₀ M n j
  have hMV : M≤V := envelope_base N hN excluded threshold₀ hM0 n j
  have hV : 4≤V := hM4.trans hMV
  have hX : X≤V := envelope_cutoff N hN excluded threshold₀ hM1 n j
  have hX0 : 0≤X := by linarith [bound_ge_three N hN excluded threshold₀ j]
  have hH : H≤V := envelope_height N hN excluded threshold₀ hM0 (hf 4) n j
  have hH0 : 0≤H := by dsimp only [H]; positivity
  have hO := hobs V ((hf 1).trans hMV) H (by rwa [abs_of_nonneg hH0]) t
  have hlog := prepared_geometry_log_bound N w Bg D H G C X Y V O Kobs t l
    hV hBg0 ((hf 2).trans hMV) hD0 ((hf 3).trans hMV) hH0 hH
    hG0 ((hf 5).trans hMV) hC0 ((hf 6).trans hMV) hX0 hX hY ((hf 10).trans hMV)
    ((hf 8).trans hMV) ((hf 9).trans hMV)
    (fun p hp => (primes_good_bound N hN excluded threshold₀ j p hp).2.trans hX)
    ((primes_length N hN excluded threshold₀ j).trans hX)
    (sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W B H ε t) hO
    hK0 ((hf 7).trans hMV)
  have hlogV : Real.log V≤envelopeConstant N hN excluded threshold₀ M*((4:ℝ)^j+n+1) :=
    envelope_log N hN excluded threshold₀ hM1 n j
  have he : 1≤(4:ℝ)^j+n+1 := by
    have hh : (0:ℝ)≤n := Nat.cast_nonneg n
    have hj : 0≤(4:ℝ)^j := by positivity
    linarith
  have hae := mul_le_mul_of_nonneg_left he ha
  have hbe := mul_le_mul_of_nonneg_left hlogV hb
  change _≤a+b*Real.log V at hlog
  dsimp only [Q]
  nlinarith only [hlog,hae,hbe]

#print axioms exists_actual_log_bound
end QuantitativeEulerEndpointPrepared
