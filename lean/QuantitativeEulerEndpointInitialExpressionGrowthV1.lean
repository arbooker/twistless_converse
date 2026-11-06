module

public import QuantitativeEulerEndpointInitialFiniteExpressionV1
public import QuantitativeEulerEndpointBaselineExpressionEnvelopeV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointInitialExpression
open AsymptoticSectorSigns QuantitativeEulerEndpointPrepared
open scoped Classical

theorem sum_uniform {ι : Type*} [Fintype ι] (f : ι → ℝ) {U B : ℝ}
    (hcard : (Fintype.card ι:ℝ)≤U) (hB : 0≤B) (hf : ∀ i,f i≤B) :
    (∑ i,f i)≤U*B := by
  calc
    _ ≤ ∑ _i : ι,B := Finset.sum_le_sum (fun i _ => hf i)
    _ = (Fintype.card ι:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB

theorem rowSquareMass_polynomial (N : ℕ) [NeZero N] (sector : Sector N)
    {ι : Type*} [Fintype ι] (t : ι → ℕ) (R Y Hobs a : ι → ℝ) {U A D : ℝ} (r s : ℕ)
    (hU : 1≤U) (hA : 0≤A) (_hD : 0≤D) (hcard : (Fintype.card ι:ℝ)≤U)
    (hbase : (Fintype.card (NewBaselineIndex N):ℝ)≤U) (_ha : ∀ i,0<a i)
    (haBound : ∀ i,(a i)⁻¹≤A*U^s)
    (hrow : ∀ i j,wideBaselineRowBound N sector (R i) (Y i) (Hobs i) (t i) j≤D*U^r) :
    rowSquareMass N sector t R Y Hobs a≤A*D^2*U^(2+s+r*2) := by
  have hU0 : 0≤U := by linarith
  have hs (i : ι) : (∑ j,(wideBaselineRowBound N sector (R i) (Y i) (Hobs i) (t i) j)^2)≤U*(D*U^r)^2 :=
    sum_uniform _ hbase (sq_nonneg _) (fun j => pow_le_pow_left₀
      (wideBaselineRowBound_nonneg N sector (R i) (Y i) (Hobs i) (t i) j) (hrow i j) 2)
  have houter := sum_uniform
    (fun i => (a i)⁻¹*(∑ j,(wideBaselineRowBound N sector (R i) (Y i) (Hobs i) (t i) j)^2))
    hcard (by positivity : 0≤(A*U^s)*(U*(D*U^r)^2))
    (fun i => mul_le_mul (haBound i) (hs i)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity))
  apply houter.trans_eq
  calc
    _ = A*D^2*(U^2*U^s*(U^r)^2) := by ring
    _ = _ := by rw [←pow_mul,←pow_add,←pow_add]

theorem rowMatrixHeight_polynomial (N : ℕ) [NeZero N] {ι : Type*} [Fintype ι]
    (R Y Hobs : ι → ℝ) {U : ℝ} (hU : 1≤U) (hcard : (Fintype.card ι:ℝ)≤U)
    (hbase : (Fintype.card (NewBaselineIndex N):ℝ)≤U)
    (hrow : ∀ i j,baselineMatrixHeight N (R i) (Y i) (Hobs i) j≤36*U^10) :
    rowMatrixHeight N R Y Hobs≤36*U^12 := by
  have hU0 : 0≤U := by linarith
  have h := sum_uniform (fun i => ∑ j : NewBaselineIndex N,baselineMatrixHeight N (R i) (Y i) (Hobs i) j)
    hcard (by positivity : 0≤U*(36*U^10))
    (fun i => sum_uniform _ hbase (by positivity) (hrow i))
  apply h.trans_eq
  ring

/-- The raw initial expression costs have a single fixed-data polynomial
envelope before the finite horizon or any observation geometry is chosen. -/
theorem exists_initial_expression_envelope (N : ℕ) [NeZero N] (sector : Sector N) :
    ∃ M : ℝ, 4≤M ∧ ∀ U : ℝ, M≤U → ∀ n : ℕ, (n:ℝ)≤U →
      ∀ R Y Hobs : Fin n → ℝ,
      (∀ i,0≤R i) → (∀ i,R i≤U) → (∀ i,0≤Hobs i) → (∀ i,Hobs i≤U) →
      (∀ i,0<Y i) → (∀ i,(min 1 (Y i))⁻¹≤U) → ∀ t : ℕ,
      ∀ a : Fin n → ℝ, (∀ i,0<a i) → ∀ A : ℝ, 0≤A → ∀ s : ℕ,
      (∀ i,(a i)⁻¹≤A*U^s) →
      rowSquareMass N sector (fun _ => t) R Y Hobs a≤A*(36*9^t)^2*U^(18+s+20*t) ∧
      rowMatrixHeight N R Y Hobs≤36*U^12 := by
  obtain ⟨M,hM,hbound⟩ := exists_baseline_expression_envelope N sector
  refine ⟨M,hM,?_⟩
  intro U hU n hn R Y Hobs hR0 hR hH0 hH hY hYinv t a ha A hA s haBound
  obtain ⟨hcard,hrows⟩ := hbound U hU
  have hU1 : 1≤U := by linarith
  have hcardn : (Fintype.card (Fin n):ℝ)≤U := by simpa only [Fintype.card_fin] using hn
  have hm := rowSquareMass_polynomial N sector (fun _ : Fin n => t) R Y Hobs a (8+10*t) s
    hU1 hA (by positivity) hcardn hcard ha haBound
    (fun i j => (hrows (R i) (Y i) (Hobs i) (hR0 i) (hR i) (hH0 i) (hH i) (hY i) (hYinv i) t j).1)
  refine ⟨?_,rowMatrixHeight_polynomial N R Y Hobs hU1 hcardn hcard
    (fun i j => (hrows (R i) (Y i) (Hobs i) (hR0 i) (hR i) (hH0 i) (hH i) (hY i) (hYinv i) t j).2)⟩
  convert hm using 1
  congr 2
  omega

#print axioms rowSquareMass_polynomial
#print axioms rowMatrixHeight_polynomial
#print axioms exists_initial_expression_envelope
end QuantitativeEulerEndpointInitialExpression
