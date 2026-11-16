module

public import QuantitativeMaassLVParitySpectrumLowerV1
public import QuantitativeMaassPrincipalLeakageV1
public import QuantitativeMaassLogPowerExceptionalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip
open scoped Topology SchwartzMap FourierTransform InnerProductSpace

namespace QuantitativeMaass

/-- The scalar multiplier at every principal energy is exactly the real
smoothed symmetric interval, including the threshold energy. -/
theorem windowTimeSchwartz_principal_norm_square (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (e : ℝ) (he0 : 1/4≤e) :
    ‖smoothPacketMultiplier (windowTimeSchwartz K hc R hR a b) e‖^2=
      (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) (Real.sqrt (e-1/4)))^2 := by
  have heq : e=1/4+(Real.sqrt (e-1/4))^2 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr he0)]
    ring
  conv_lhs => rw [heq,smoothPacketMultiplier_principal]
  change ‖cosinePacket (symmetricWindowTimeTest K R a b) (Real.sqrt (e-1/4))‖^2=_
  rw [symmetricWindowTimeTest_cosinePacket K he hc R a b _ hR ha,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- On a unit genuine energy eigenvector the positive packet diagonal is
exactly the squared scalar multiplier, at principal and exceptional energies. -/
theorem windowWavePacket_diagonal_scalar (N : ℕ) (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (v : AutomorphicSpace N) (hn : ‖v‖=1)
    (e : ℝ) (he0 : 0≤e) (hgraph : FriedrichsGraph N v ((e:ℂ) • v)) :
    (inner ℂ v ((windowWavePacket N K hc R hR a b).comp
      (windowWavePacket N K hc R hR a b) v)).re=
      ‖smoothPacketMultiplier (windowTimeSchwartz K hc R hR a b) e‖^2 := by
  rw [windowWavePacket_square_diagonal N K he hc]
  unfold windowWavePacket
  rw [Wave.shiftedQuotientWavePacket_eigen N _ _ he0 hgraph,norm_smul,hn,mul_one]
  rfl

/-- The literal LV/parity weights on any unit cusp vector lie in [0,1]. -/
theorem actualLVFilter_parity_unit_weight (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ) (σ : ℝ) (hσ : σ^2=1)
    (v : AutomorphicSpace N) (hv : v∈localCuspidalSpace N hN) (hn : ‖v‖=1) :
    (inner ℂ (actualLVFilter N p hN hpN a b hab d (parityProjection N σ v))
      (parityProjection N σ v)).re∈Icc (0:ℝ) 1 := by
  have hh := actualLVFilter_parity_quadratic_bounds N p hN hpN hNp a b hab d σ hσ v
  exact ⟨hh.1,hh.2.trans (actualLVFilter_cusp_weight_bounds N p hN hpN hNp hpres a b hab d v hv hn).2⟩

/-- The exceptional scalar series is convergent without a separately assumed
finiteness assertion: actual cusp energy-band finiteness supplies it. -/
theorem exceptional_window_scalar_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    Summable (fun i : {i // e i≤1/4} =>
      ‖smoothPacketMultiplier (windowTimeSchwartz K hc R hR a b) (e i.val)‖^2) := by
  obtain ⟨C,hC,hcount⟩ := cuspidal_spectral_band_polynomial N hN
  have hfinite := (hcount ι v hv hcusp e he hgraph (1/4) (by norm_num)).1
  let : Fintype {i // e i≤1/4} := hfinite.fintype
  exact Summable.of_finite

#print axioms windowTimeSchwartz_principal_norm_square
#print axioms windowWavePacket_diagonal_scalar
#print axioms actualLVFilter_parity_unit_weight
#print axioms exceptional_window_scalar_summable

end QuantitativeMaass
