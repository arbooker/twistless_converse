module

public import QuantitativeMaassCuspContinuousConstantV1
public import QuantitativeMaassWindowRawColumnV1
public import QuantitativeMaassCenteredColumnBesselV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The actual Hilbert-valued period average of a continuous kernel column. -/
def cuspColumnMean (N : ℕ) (c : ℍ → AutomorphicSpace N) (s : SL(2,ℤ)) (u : ℝ) :
    AutomorphicSpace N := ∫ x in Icc (0:ℝ) 1,c (cuspLogPoint N s u x)

theorem cuspColumnMean_inner (N : ℕ) (c : ℍ → AutomorphicSpace N)
    (hc : Continuous c) (s : SL(2,ℤ)) (u : ℝ) (v : AutomorphicSpace N) :
    inner ℂ (cuspColumnMean N c s u) v=
      cuspConstant N s (fun z => inner ℂ (c z) v) (Real.exp u) := by
  have hcont : Continuous (fun x => c (cuspLogPoint N s u x)) :=
    hc.comp ((cuspLogPoint_continuous N s).comp (continuous_const.prodMk continuous_id))
  have hint : IntegrableOn (fun x => c (cuspLogPoint N s u x)) (Icc (0:ℝ) 1) volume :=
    hcont.integrableOn_Icc
  have hh : inner ℂ (cuspColumnMean N c s u) v=
      ∫ x in Icc (0:ℝ) 1,inner ℂ (c (cuspLogPoint N s u x)) v := by
    unfold cuspColumnMean
    rw [←inner_conj_symm (∫ x in Icc (0:ℝ) 1,c (cuspLogPoint N s u x)) v,
      ←integral_inner hint v,←integral_conj]
    simp only [inner_conj_symm]
  rw [hh]
  unfold cuspConstant zeroFourier
  simp only [cuspProfile,dite_eq_left (Real.exp_pos u)]
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  rfl

/-- A kernel operator preserving the actual cusp space has period-average
columns orthogonal to every genuine cusp vector. -/
theorem cuspColumnMean_orthogonal (N : ℕ) (hN : 0<N)
    (A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (c : ℍ → AutomorphicSpace N) (hc : Continuous c)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z)
    (hrep : ∀ v,(A v).val=ᵐ[quotientMeasure N](fun x => inner ℂ (c x) v))
    (hpres : ∀ v∈localCuspidalSpace N hN,A v∈localCuspidalSpace N hN)
    (s : SL(2,ℤ)) (u : ℝ) (v : AutomorphicSpace N)
    (hv : v∈localCuspidalSpace N hN) : inner ℂ (cuspColumnMean N c s u) v=0 := by
  rw [cuspColumnMean_inner N c hc s u v]
  exact localCuspidalSpace_continuous_constant_zero N hN (A v) (hpres v hv)
    _ (hc.inner continuous_const) (fun γ z => by rw [hinv])
    (hrep v) s (Real.exp u) (Real.exp_pos u)

/-- Unconditional mean removal for the actual window packet and cusp space. -/
theorem windowAbelColumn_mean_orthogonal (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (s : SL(2,ℤ)) (u : ℝ)
    (v : AutomorphicSpace N) (hv : v∈localCuspidalSpace N hN) :
    inner ℂ (cuspColumnMean N (windowAbelColumn N K he hc R hR a b) s u) v=0 := by
  apply cuspColumnMean_orthogonal N hN (windowWavePacket N K hc R hR a b)
    _ (windowAbelColumn_continuous N K he hc R hR a b)
    (windowAbelColumn_invariant N K he hc R hR a b)
    (windowAbelColumn_packet_coeFn N K he hc R hR a b) _ s u v hv
  intro w hw
  exact shiftedQuotientWavePacket_mem_localCuspidalSpace N hN _ _ w hw

#print axioms cuspColumnMean_inner
#print axioms cuspColumnMean_orthogonal
#print axioms windowAbelColumn_mean_orthogonal

end QuantitativeMaass
