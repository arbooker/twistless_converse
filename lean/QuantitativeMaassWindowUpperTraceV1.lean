module

public import QuantitativeMaassWindowGlobalTraceV1
public import QuantitativeMaassWindowTailUniformV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand QuantitativeSpectralObservability
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Actual global window trace with the exact quotient-volume main term and
explicit core and tail errors. Constants precede all levels and parameters. -/
theorem windowWavePacket_global_upper_trace {ι : Type*} (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ H A B C D : ℝ,0<H ∧ 0<A ∧ 0<B ∧ 0<C ∧ 0<D ∧
      ∀ (N : ℕ) [NeZero N],∀ hN : 0<N,∀ R : ℝ,∀ hR : 1≤R,
      ∀ ε : ℝ,0≤ε → ε≤1 → ∀ t : ℝ,1≤t →
      ∀ (v : ι → AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ Y : ℝ,2≤Y → H*R<Real.log Y →
      let n : ℝ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
      (∑' i,ENNReal.ofReal (‖windowWavePacket N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (v i)‖^2))≤
        ENNReal.ofReal (windowIdentityContribution K hc R
          (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re*quotientMeasure N univ+
        ENNReal.ofReal (n*C*Real.sqrt t*ε^2*Real.exp (A*R)*(1+Real.sqrt Y))+
        ENNReal.ofReal (2*n*(N:ℝ)^2*D*R^3*ε^2*t*Real.sqrt t*Real.exp (B*R)/Y) := by
  obtain ⟨A,C,hA,hC,hcore⟩ := windowGeometricRemainder_exp_core_integral K he hc
  obtain ⟨H,B,D,hH,hB,hD,htail⟩ := windowWavePacket_tail_uniform (ι:=ι) K he hc
  refine ⟨H,A,B,C,D,hH,hA,hB,hC,hD,?_⟩
  intro N _ hN R hR ε hε hε1 t ht v hv hcus Y hY hhigh
  classical
  let := Fintype.ofFinite (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  let n : ℝ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  let E := (N:ℝ)^2*D*R^3*ε^2*t*Real.sqrt t*Real.exp (B*R)/Y
  have hE : 0≤E := by dsimp [E]; positivity
  apply ENNReal.summable.tsum_le_of_sum_le
  intro S
  apply (window_finite_packet_sharp_cover N K he hc R
    (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) v S hN hv Y hY).trans
  apply add_le_add
  · apply add_le_add le_rfl
    have hi : IntegrableOn (fun z => ‖windowGeometricRemainder N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) z‖) (wideCompactCover N Y) volume :=
      (windowGeometricRemainder_continuous N K he hc R _ (t-ε) (t+ε)).norm.continuousOn.integrableOn_compact
        (wideCompactCover_compact N hN Y)
    rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun z => norm_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    convert hcore R hR N hN ε t Y hε hε1 ht (by linarith) using 1
    ring
  · calc
      _ ≤ ∑' _q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,∑' _b : Bool,ENNReal.ofReal E := by
        apply ENNReal.tsum_le_tsum
        intro q
        apply ENNReal.tsum_le_tsum
        intro b
        exact (ENNReal.sum_le_tsum S).trans
          (htail N hN R hR ε hε hε1 t ht v hv hcus (globalCuspChart N q b) Y hY hhigh)
      _ = ENNReal.ofReal (2*n*E) := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤2*n),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
        simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_bool,
          nsmul_eq_mul,ENNReal.ofReal_ofNat,n,ENNReal.ofReal_natCast,Nat.card_eq_fintype_card]
        ring
      _ = _ := by congr 1; dsimp [E]; ring

#print axioms windowWavePacket_global_upper_trace

end QuantitativeMaass
