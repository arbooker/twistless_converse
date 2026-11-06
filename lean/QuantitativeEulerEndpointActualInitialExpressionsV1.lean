module

public import QuantitativeEulerEndpointInitialGeometryV1
public import QuantitativeEulerEndpointInitialExpressionGrowthV1
public import QuantitativeEulerEndpointCommonEnvelopeV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open AsymptoticSectorSigns QuantitativeEulerEndpointPrimeBlocks QuantitativeEulerEndpointInitialExpression
open scoped Classical MatrixGroups

variable (N : ℕ) [NeZero N] (hN : 2≤N) (excluded : Finset ℕ) (threshold₀ : ℕ)
    (sector : Sector N) (S : Finset SL(2,ℤ))
    (hS : Subgroup.closure (S : Set SL(2,ℤ))=CongruenceSubgroup.Gamma0 N)
    (W : Finset (List SL(2,ℤ))) (B Bg D H₀ G C Kobs ε : ℝ) (t : ℕ)

def actualInitialRowCosts (n : ℕ) : ℝ × ℝ :=
  let H := H₀*(4:ℝ)^n
  let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold₀
  let Y := min ε (1/4)
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let L := fun j => (2*G*C)*(X j)^4
  let height := fun j => L j*(R+R+1)/min 1 Z
  let low := fun j => Z/wideDistortion (L j) R R
  let O := sectorObservationCost N (NeZero.pos N) sector S hS W B H ε t
  let cost := fun j => O*(Kobs*((wideDistortion (L j) R R)^t)^2)
  (rowSquareMass N sector (fun _ : Fin n => t)
    (fun i => height i+1) (fun i => low i) (fun i => height i)
    (fun i => (2*(1+2*cost i))⁻¹),
  rowMatrixHeight N (fun i : Fin n => height i+1) (fun i => low i) (fun i => height i))

/-- Explicit coefficient-mass and matrix-height inputs for the original
initial energy expression, on the ACTUAL growing observation rectangles. -/
theorem exists_actual_initial_row_costs (hBg0 : 0≤Bg) (hD0 : 0≤D) (hH₀ : 0≤H₀)
    (hG0 : 0≤G) (hC0 : 0≤C) (hK0 : 0≤Kobs) (hε : 0<ε) :
    ∃ M : ℝ, 4≤M ∧ ∀ n : ℕ,
      (actualInitialRowCosts N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t n).1≤
        (6*(36*9^t)^2)*(envelope N hN excluded threshold₀ M n n)^(936+5184*t) ∧
      (actualInitialRowCosts N hN excluded threshold₀ sector S hS W B Bg D H₀ G C Kobs ε t n).2≤
        36*(envelope N hN excluded threshold₀ M n n)^432 := by
  let Y := min ε (1/4)
  have hY : 0<Y := lt_min hε (by norm_num)
  obtain ⟨Mobs,hMobs,hobs⟩ := exists_sector_observation_envelope N (NeZero.pos N) sector S hS W B ε
  obtain ⟨Mbase,hMbase,hbase⟩ := exists_initial_expression_envelope N sector
  let f : Fin 10 → ℝ := ![4,Mobs,Mbase,Bg,D,H₀,G,C,Kobs,(min 1 Y)⁻¹]
  obtain ⟨M,hM⟩ := (Set.finite_range f).bddAbove
  have hf (i) : f i≤M := hM ⟨i,rfl⟩
  have hM4 : 4≤M := hf 0
  have hM1 : 1≤M := by linarith
  have hM0 : 0≤M := by linarith
  refine ⟨M,hM4,?_⟩
  intro n
  let V := envelope N hN excluded threshold₀ M n n
  let H := H₀*(4:ℝ)^n
  let X := QuantitativeEulerEndpointPrimeBlocks.bound N hN excluded threshold₀
  let R := Bg*(D*H+2+1)/min 1 Y
  let Z := Y/wideDistortion Bg 2 (D*H)
  let L := fun j => (2*G*C)*(X j)^4
  let height := fun j => L j*(R+R+1)/min 1 Z
  let low := fun j => Z/wideDistortion (L j) R R
  let O := sectorObservationCost N (NeZero.pos N) sector S hS W B H ε t
  let cost := fun j => O*(Kobs*((wideDistortion (L j) R R)^t)^2)
  have hMV : M≤V := envelope_base N hN excluded threshold₀ hM0 n n
  have hV : 4≤V := hM4.trans hMV
  have hV1 : 1≤V := by linarith
  have hV0 : 0≤V := by linarith
  have hVU : V≤V^36 := by simpa only [pow_one] using pow_le_pow_right₀ hV1 (by norm_num : 1≤36)
  have hH : H≤V := envelope_height N hN excluded threshold₀ hM0 (hf 5) n n
  have hH0 : 0≤H := by dsimp only [H]; positivity
  have hX (j : ℕ) (hj : j≤n) : X j≤V := by
    have hmono : X j≤X n := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤3)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hj 1))
        (QuantitativeEulerEndpointSparsePrefix.preparedPrefix N hN excluded threshold₀).constant_pos.le
    exact hmono.trans (envelope_cutoff N hN excluded threshold₀ hM1 n n)
  have hX0 (j : ℕ) : 0≤X j := by linarith [bound_ge_three N hN excluded threshold₀ j]
  have hgeom (j : ℕ) (hj : j≤n) :
      0≤height j ∧ height j+1≤V^36 ∧ 0<low j ∧ (min 1 (low j))⁻¹≤V^36 :=
    wide_geometry_envelope Bg D H G C (X j) Y V hV hBg0 ((hf 3).trans hMV)
      hD0 ((hf 4).trans hMV) hH0 hH hG0 ((hf 6).trans hMV) hC0 ((hf 7).trans hMV)
      (hX0 j) (hX j hj) hY ((hf 9).trans hMV)
  have hdist (j : ℕ) (hj : j≤n) : wideDistortion (L j) R R≤V^26 :=
    wide_geometry_transport_bound Bg D H G C (X j) Y V hV hBg0 ((hf 3).trans hMV)
      hD0 ((hf 4).trans hMV) hH0 hH hG0 ((hf 6).trans hMV) hC0 ((hf 7).trans hMV)
      (hX0 j) (hX j hj) hY ((hf 9).trans hMV)
  have hO0 : 0≤O := sectorObservationCost_nonneg N (NeZero.pos N) sector S hS W B H ε t
  have hO : O≤V^(7+72*t) := hobs V ((hf 1).trans hMV) H (by rwa [abs_of_nonneg hH0]) t
  have hc0 (i : Fin n) : 0≤cost i := by dsimp only [cost]; positivity
  have hc (i : Fin n) : cost i≤V^(8+124*t) := observation_transport_power t hV1 hO hK0
    ((hf 8).trans hMV) (wideDistortion_pos _ _ _).le (hdist i i.isLt.le)
  have hn : (n:ℝ)≤V := by
    have hn2 : (n:ℝ)≤(2:ℝ)^n := by exact_mod_cast (show n≤2^n from Nat.lt_two_pow_self.le)
    have hn4 := hn2.trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (2:ℝ)≤4) n)
    have hh : (4:ℝ)^n≤V := by simpa only [one_mul] using envelope_height N hN excluded threshold₀ hM0 hM1 n n
    exact hn4.trans hh
  have hU1 : 1≤V^36 := one_le_pow₀ hV1
  have ha (i : Fin n) : 0<(2*(1+2*cost i))⁻¹ := by have hh := hc0 i; positivity
  have hai (i : Fin n) : ((2*(1+2*cost i))⁻¹)⁻¹≤6*(V^36)^(8+124*t) :=
    inverse_budget_power _ hU1 ((hc i).trans (pow_le_pow_left₀ hV0 hVU _))
  obtain ⟨hmass,hheight⟩ := hbase (V^36) (((hf 2).trans hMV).trans hVU) n (hn.trans hVU)
    (fun i : Fin n => height i+1) (fun i => low i) (fun i => height i)
    (fun i => by have hh := (hgeom i i.isLt.le).1; linarith)
    (fun i => (hgeom i i.isLt.le).2.1)
    (fun i => (hgeom i i.isLt.le).1)
    (fun i => by have hh := (hgeom i i.isLt.le).2.1; linarith)
    (fun i => (hgeom i i.isLt.le).2.2.1)
    (fun i => (hgeom i i.isLt.le).2.2.2)
    t (fun i => (2*(1+2*cost i))⁻¹) ha 6 (by norm_num) (8+124*t) hai
  constructor
  · change rowSquareMass N sector (fun _ : Fin n => t)
      (fun i => height i+1) (fun i => low i) (fun i => height i)
      (fun i => (2*(1+2*cost i))⁻¹)≤_
    convert hmass using 1
    rw [←pow_mul]
    congr 2
    omega
  · change rowMatrixHeight N (fun i : Fin n => height i+1) (fun i => low i) (fun i => height i)≤_
    convert hheight using 1
    rw [←pow_mul]


#print axioms exists_actual_initial_row_costs
end QuantitativeEulerEndpointPrepared
