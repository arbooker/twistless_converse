module

public import QuantitativeMaassFiniteEnergyCompositionV1
public import QuantitativeMaassFiniteSourceEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open MeasureTheory ContinuousLinearMap
namespace QuantitativeMaass

variable {α E H ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]

/-- Finite-source energy controls the integrated error on actual columns
through their operator norm, rather than their total column energy. Thus
applying a compression estimate does not lose another spectral dimension. -/
theorem finiteSourceEnergy_column_bound (μ : Measure α) (c : α→E) (hc : MemLp c 2 μ)
    (b : OrthonormalBasis ι ℂ E) (A : E→L[ℂ]H) :
    (∫ x,‖A (c x)‖^2 ∂μ)≤‖finiteEnergyColumnOperator μ c hc‖^2*finiteSourceEnergy b A := by
  classical
  let : FiniteDimensional ℂ E := Module.Finite.of_basis b.toBasis
  let V := A.range
  let : FiniteDimensional ℂ V := LinearMap.finiteDimensional_range A.toLinearMap
  let d := stdOrthonormalBasis ℂ V
  let C := finiteEnergyColumnOperator μ c hc
  have hd (z : E) : ‖A z‖^2=∑ k,‖inner ℂ (d k:H) (A z)‖^2 :=
    (d.sum_sq_norm_inner_right ⟨A z,⟨z,rfl⟩⟩).symm
  have hadj : (∑ k,‖A.adjoint (d k:H)‖^2)=finiteSourceEnergy b A := by
    calc
      _ = ∑ k,∑ j,‖inner ℂ (A.adjoint (d k:H)) (b j)‖^2 :=
        Finset.sum_congr rfl (fun _ _ => (b.sum_sq_norm_inner_left _).symm)
      _ = ∑ j,∑ k,‖inner ℂ (d k:H) (A (b j))‖^2 := by
        rw [Finset.sum_comm]
        simp only [A.adjoint_inner_left]
      _ = _ := Finset.sum_congr rfl (fun j _ => (hd (b j)).symm)
  have hcoeff (v : E) :
      (∫ x,‖inner ℂ v (c x)‖^2 ∂μ)=‖C v‖^2 := by
    rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [finiteEnergyColumnOperator_coeFn μ c hc v] with x hx
    dsimp only [C]
    rw [hx,norm_inner_symm]
  have hint (v : E) : Integrable (fun x => ‖inner ℂ v (c x)‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (hc.const_inner v).aestronglyMeasurable).mp (hc.const_inner v)
  calc
    _ = ∫ x,∑ k,‖inner ℂ (A.adjoint (d k:H)) (c x)‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [A.adjoint_inner_left,hd]
    _ = ∑ k,∫ x,‖inner ℂ (A.adjoint (d k:H)) (c x)‖^2 ∂μ :=
      integral_finsetSum _ (fun _ _ => hint _)
    _ = ∑ k,‖C (A.adjoint (d k:H))‖^2 := by simp_rw [hcoeff]
    _ ≤ ‖C‖^2*∑ k,‖A.adjoint (d k:H)‖^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (C.le_opNorm (A.adjoint (d k:H))) 2
    _ = _ := by rw [hadj]

/-- The column operator of a bounded transfer is the actual source packet
composed with the adjoint transfer. The source column itself need not have
finite total energy. -/
theorem transferredColumnOperator_eq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (μ : Measure α) (K : Lp ℂ 2 μ→L[ℂ]Lp ℂ 2 μ)
    (c : α→Lp ℂ 2 μ)
    (hK : ∀ v : Lp ℂ 2 μ,K v=ᵐ[μ](fun x => inner ℂ (c x) v))
    (T : Lp ℂ 2 μ→L[ℂ]G) (hc : MemLp (fun x => T (c x)) 2 μ) :
    finiteEnergyColumnOperator μ (fun x => T (c x)) hc=K.comp T.adjoint := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [finiteEnergyColumnOperator_coeFn μ (fun x => T (c x)) hc v,
    hK (T.adjoint v)] with x h1 h2
  change finiteEnergyColumnOperator μ (fun x => T (c x)) hc v x=K (T.adjoint v) x
  rw [h1,h2,T.adjoint_inner_right]

/-- Packet-column version of the finite-source energy bound. Only the
bounded packet norm occurs, not the integral of the source spectral mass. -/
theorem finiteSourceEnergy_transferred_column_bound
    (μ : Measure α) (K : Lp ℂ 2 μ→L[ℂ]Lp ℂ 2 μ)
    (c : α→Lp ℂ 2 μ)
    (hK : ∀ v : Lp ℂ 2 μ,K v=ᵐ[μ](fun x => inner ℂ (c x) v))
    (T : Lp ℂ 2 μ→L[ℂ]E) (hc : MemLp (fun x => T (c x)) 2 μ)
    (b : OrthonormalBasis ι ℂ E) (A : E→L[ℂ]H) :
    (∫ x,‖A (T (c x))‖^2 ∂μ)≤(‖K‖*‖T‖)^2*finiteSourceEnergy b A := by
  have he := finiteSourceEnergy_column_bound μ (fun x => T (c x)) hc b A
  rw [transferredColumnOperator_eq μ K c hK T hc] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (finiteSourceEnergy_nonneg b A)
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa only [ContinuousLinearMap.adjoint.norm_map] using opNorm_comp_le K T.adjoint

#print axioms transferredColumnOperator_eq
#print axioms finiteSourceEnergy_transferred_column_bound
#print axioms finiteSourceEnergy_column_bound
end QuantitativeMaass
