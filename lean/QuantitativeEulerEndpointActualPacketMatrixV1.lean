module

public import QuantitativeEulerEndpointPacketMatrixGrowthV1
public import QuantitativeEulerEndpointInitialExpressionLogV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerEndpointPrimeBlocks
open scoped Classical

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (Bg D H₀ G C ε : ℝ)

def actualPacketMatrixHeight (n j : ℕ) : ℝ :=
  let H := H₀*(4:ℝ)^n
  let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let L := (2*G*C)*(X j)^4
  let height := L*(R+R+1)/min 1 Z
  let low := Z/wideDistortion L R R
  8*(packetMatrixBound N (height+1) low height (primes N hN excluded threshold j))^2

theorem exists_actual_packet_matrix_bound (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hε : 0<ε) :
    ∃ M : ℝ, 4≤M ∧ ∀ n j : ℕ, j≤n →
      actualPacketMatrixHeight N hN excluded threshold Bg D H₀ G C ε n j≤
        (8*36^2)*(envelope N hN excluded threshold M n n)^792 := by
  let Y := min ε (1/4)
  have hY : 0<Y := lt_min hε (by norm_num)
  let f : Fin 8 → ℝ := ![4,(N:ℝ),Bg,D,H₀,G,C,(min 1 Y)⁻¹]
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have hM4 : 4≤M := hf 0
  have hM1 : 1≤M := by linarith
  have hM0 : 0≤M := by linarith
  refine ⟨M,hM4,?_⟩
  intro n j hj
  let V := envelope N hN excluded threshold M n n
  let H := H₀*(4:ℝ)^n
  let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let L := (2*G*C)*(X j)^4
  let height := L*(R+R+1)/min 1 Z
  let low := Z/wideDistortion L R R
  let l := primes N hN excluded threshold j
  have hMV : M≤V := envelope_base N hN excluded threshold hM0 n n
  have hV : 4≤V := hM4.trans hMV
  have hV1 : 1≤V := by linarith
  have hV0 : 0≤V := by linarith
  have hVU : V≤V^36 := by simpa only [pow_one] using pow_le_pow_right₀ hV1 (by norm_num : 1≤36)
  have hH : H≤V := envelope_height N hN excluded threshold hM0 (hf 4) n n
  have hH0 : 0≤H := by dsimp only [H]; positivity
  have hX : X j≤V := by
    have hmono : X j≤X n := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤3)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hj 1))
        (QuantitativeEulerEndpointSparsePrefix.preparedPrefix N hN excluded threshold).constant_pos.le
    exact hmono.trans (envelope_cutoff N hN excluded threshold hM1 n n)
  have hX0 : 0≤X j := by linarith [bound_ge_three N hN excluded threshold j]
  have hgeom : 0≤height ∧ height+1≤V^36 ∧ 0<low ∧ (min 1 low)⁻¹≤V^36 :=
    wide_geometry_envelope Bg D H G C (X j) Y V hV hBg0 ((hf 2).trans hMV)
      hD0 ((hf 3).trans hMV) hH0 hH hG0 ((hf 5).trans hMV) hC0 ((hf 6).trans hMV)
      hX0 hX hY ((hf 7).trans hMV)
  have hU1 : 1≤V^36 := one_le_pow₀ hV1
  have hlen : (l.length:ℝ)≤V^36 := ((primes_length N hN excluded threshold j).trans hX).trans hVU
  have hq : ∀ q∈l,(q.val:ℝ)≤V^36 := fun q hq =>
    (((primes_good_bound N hN excluded threshold j q hq).2).trans hX).trans hVU
  have hmat := packetMatrixBound_polynomial N (height+1) low height (V^36) l hU1
    (((hf 1).trans hMV).trans hVU) hlen hq (by linarith [hgeom.1]) hgeom.2.1 hgeom.1
      (by linarith [hgeom.2.1]) hgeom.2.2.1 hgeom.2.2.2
  have hmat' : packetMatrixBound N (height+1) low height l≤36*V^396 := by
    simpa only [←pow_mul] using hmat
  change 8*(packetMatrixBound N (height+1) low height l)^2≤_
  calc
    _ ≤ 8*(36*V^396)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (packetMatrixBound_nonneg N _ _ _ l) hmat' 2) (by norm_num)
    _ = _ := by ring

theorem exists_actual_packet_matrix_log (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hε : 0<ε) :
    ∃ Q : ℝ, 0≤Q ∧ ∀ n j : ℕ, j≤n →
      Real.log (max 1 (actualPacketMatrixHeight N hN excluded threshold Bg D H₀ G C ε n j))≤Q*(4:ℝ)^n := by
  obtain ⟨M,hM,hbound⟩ := exists_actual_packet_matrix_bound N hN excluded threshold Bg D H₀ G C ε
    hBg0 hD0 hH₀ hG0 hC0 hε
  have hM1 : 1≤M := by linarith
  let Q := Real.log (8*36^2)+2*(792:ℝ)*envelopeConstant N hN excluded threshold M
  have hQ : 0≤Q := add_nonneg (Real.log_nonneg (by norm_num))
    (mul_nonneg (by norm_num) (envelopeConstant_nonneg N hN excluded threshold hM1))
  exact ⟨Q,hQ,fun n j hj => log_max_polynomial_envelope N hN excluded threshold hM1
    (by norm_num : (1:ℝ)≤8*36^2) 792 n (hbound n j hj)⟩

#print axioms exists_actual_packet_matrix_bound
#print axioms exists_actual_packet_matrix_log
end QuantitativeEulerEndpointPrepared
