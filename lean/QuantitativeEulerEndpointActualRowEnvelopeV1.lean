module

public import QuantitativeEulerEndpointBaselineExpressionEnvelopeV1
public import QuantitativeEulerEndpointActualPacketMatrixV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerEndpointPrimeBlocks
open scoped Classical

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold : ℕ)
    (Bg D H₀ G C ε : ℝ)

/-- Height and lower height of the exact observation rectangle in actualBlock. -/
def actualRowRectangle (n j : ℕ) : ℝ × ℝ :=
  let H := H₀*(4:ℝ)^n
  let X := bound N hN excluded threshold j
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let L := (2*G*C)*X^4
  (L*(R+R+1)/min 1 Z,Z/wideDistortion L R R)

/-- Every original row, its integer representative and the row count have
one polynomial envelope on the actual growing rectangles. -/
theorem exists_actual_row_envelope (sector : Sector N)
    (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀) (hG0 : 0≤G) (hC0 : 0≤C) (hε : 0<ε) :
    ∃ M : ℝ,4≤M ∧ ∀ n j : ℕ,j≤n →
      let V := envelope N hN excluded threshold M n n
      let U := V^36
      let r := actualRowRectangle N hN excluded threshold Bg D H₀ G C ε n j
      let l := primes N hN excluded threshold j
      0≤r.1 ∧ 0<r.2 ∧
      (Fintype.card (NewBaselineIndex N):ℝ)+(l.length:ℝ)≤2*U ∧
      ∀ t : ℕ,
      (∀ i,wideBaselineRowBound N sector (r.1+1) r.2 r.1 t i≤72*9^t*U^(9+10*t) ∧
        baselineMatrixHeight N (r.1+1) r.2 r.1 i≤36*U^10) ∧
      (∀ i : Fin l.length,wideSequenceBound N (sign sector.1) (r.1+1) r.2 r.1 t l i≤72*9^t*U^(9+10*t) ∧
        4*(1+(wideCompactCutoff (N*l[i.val].val^3:ℕ) (r.1+1) r.2 r.1:ℝ))*(N*l[i.val].val^3:ℕ)≤36*U^10) := by
  let Y := min ε (1/4)
  have hY : 0<Y := lt_min hε (by norm_num)
  obtain ⟨Mbase,hMbase,hbase⟩ := exists_baseline_expression_envelope N sector
  let f : Fin 9 → ℝ := ![4,Mbase,(N:ℝ),Bg,D,H₀,G,C,(min 1 Y)⁻¹]
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have hM4 : 4≤M := hf 0
  have hM1 : 1≤M := by linarith
  have hM0 : 0≤M := by linarith
  refine ⟨M,hM4,?_⟩
  intro n j hj V U r l
  let H := H₀*(4:ℝ)^n
  let X := bound N hN excluded threshold j
  have hMV : M≤V := envelope_base N hN excluded threshold hM0 n n
  have hV : 4≤V := hM4.trans hMV
  have hV1 : 1≤V := by linarith
  have hVU : V≤U := by simpa only [U,pow_one] using pow_le_pow_right₀ hV1 (by norm_num : 1≤36)
  have hU : 1≤U := one_le_pow₀ hV1
  have hU0 : 0≤U := by linarith
  have hH : H≤V := envelope_height N hN excluded threshold hM0 (hf 5) n n
  have hH0 : 0≤H := by dsimp only [H]; positivity
  have hX : X≤V := by
    have hm : X≤bound N hN excluded threshold n := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤3)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hj 1))
        (QuantitativeEulerEndpointSparsePrefix.preparedPrefix N hN excluded threshold).constant_pos.le
    exact hm.trans (envelope_cutoff N hN excluded threshold hM1 n n)
  have hX0 : 0≤X := by linarith [bound_ge_three N hN excluded threshold j]
  have hgeom : 0≤r.1 ∧ r.1+1≤U ∧ 0<r.2 ∧ (min 1 r.2)⁻¹≤U :=
    wide_geometry_envelope Bg D H G C X Y V hV hBg0 ((hf 3).trans hMV)
      hD0 ((hf 4).trans hMV) hH0 hH hG0 ((hf 6).trans hMV) hC0 ((hf 7).trans hMV)
      hX0 hX hY ((hf 8).trans hMV)
  have hNU : (N:ℝ)≤U := ((hf 2).trans hMV).trans hVU
  have hbaseU := hbase U (((hf 1).trans hMV).trans hVU)
  have hlen : (l.length:ℝ)≤U := ((primes_length N hN excluded threshold j).trans hX).trans hVU
  have hq (i : Fin l.length) : (l[i.val].val:ℝ)≤U :=
    (((primes_good_bound N hN excluded threshold j _ (List.getElem_mem _)).2).trans hX).trans hVU
  refine ⟨hgeom.1,hgeom.2.2.1,by linarith [hbaseU.1],?_⟩
  intro t
  have hb := hbaseU.2 (r.1+1) r.2 r.1 (by linarith [hgeom.1]) hgeom.2.1
    hgeom.1 (by linarith [hgeom.2.1]) hgeom.2.2.1 hgeom.2.2.2 t
  constructor
  · intro i
    refine ⟨(hb i).1.trans ?_,(hb i).2⟩
    have hp : U^(8+10*t)≤U^(9+10*t) := pow_le_pow_right₀ hU (by omega)
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤36*9^t)
    nlinarith [mul_nonneg (by positivity : (0:ℝ)≤36*9^t) (pow_nonneg hU0 (9+10*t))]
  · intro i
    constructor
    · unfold wideSequenceBound
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using i.isLt)]
      simp only [List.getElem_map]
      exact widePacketBound_polynomial N l[i.val].val (sign sector.1) (r.1+1) r.2 r.1 U t
        hU hNU (hq i) (by simpa only [sign_norm] using hU)
        (by linarith [hgeom.1]) hgeom.2.1 hgeom.1 (by linarith [hgeom.2.1]) hgeom.2.2.1 hgeom.2.2.2
    · have hsize : ((N*l[i.val].val^3:ℕ):ℝ)≤U^4 := by
        push_cast
        calc
          _ ≤ U*U^3 := mul_le_mul hNU (pow_le_pow_left₀ (by positivity) (hq i) 3) (by positivity) hU0
          _ = _ := by ring
      exact wide_matrix_polynomial _ _ _ _ U hU (by positivity) hsize
        (by linarith [hgeom.1]) hgeom.2.1 hgeom.1 (by linarith [hgeom.2.1]) hgeom.2.2.1 hgeom.2.2.2

#print axioms exists_actual_row_envelope
end QuantitativeEulerEndpointPrepared
