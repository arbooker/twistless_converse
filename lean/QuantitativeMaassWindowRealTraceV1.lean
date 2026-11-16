module

public import QuantitativeMaassWindowUpperTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The finite actual ENNReal trace bound supplies summability as well as its
real-valued inequality; no summability assumption is inserted. -/
theorem nonnegative_trace_real_bound {ι : Type*} (f : ι → ℝ) (hf : ∀ i,0≤f i)
    (I C D : ℝ) (hI : 0≤I) (hC : 0≤C) (hD : 0≤D)
    (V : ℝ≥0∞) (hV : V≠∞)
    (h : (∑' i,ENNReal.ofReal (f i))≤ENNReal.ofReal I*V+ENNReal.ofReal C+ENNReal.ofReal D) :
    Summable f ∧ (∑' i,f i)≤I*V.toReal+C+D := by
  have hfin : ENNReal.ofReal I*V+ENNReal.ofReal C+ENNReal.ofReal D≠∞ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV,ENNReal.ofReal_ne_top⟩,ENNReal.ofReal_ne_top⟩
  have hs := ENNReal.summable_toReal (ne_top_of_le_ne_top hfin h)
  have hb := ENNReal.toReal_mono hfin h
  simp only [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),ENNReal.toReal_ofReal (hf _)] at hb
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV,ENNReal.ofReal_ne_top⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal hI,ENNReal.toReal_ofReal hC,ENNReal.toReal_ofReal hD] at hb
  exact ⟨by simpa only [ENNReal.toReal_ofReal (hf _)] using hs,hb⟩

/-- The literal real squared-norm trace of any orthonormal cusp family is
summable and has the sharp quotient-volume coefficient. -/
theorem windowWavePacket_global_real_trace {ι : Type*} (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ H A B C D : ℝ,0<H ∧ 0<A ∧ 0<B ∧ 0<C ∧ 0<D ∧
      ∀ (N : ℕ) [NeZero N],∀ hN : 0<N,∀ R : ℝ,∀ hR : 1≤R,
      ∀ ε : ℝ,0≤ε → ε≤1 → ∀ t : ℝ,1≤t →
      ∀ (v : ι → AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ Y : ℝ,2≤Y → H*R<Real.log Y →
      let n : ℝ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
      Summable (fun i => ‖windowWavePacket N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (v i)‖^2) ∧
      (∑' i,‖windowWavePacket N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (v i)‖^2)≤
        (windowIdentityContribution K hc R
          (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε)).re*(quotientMeasure N).real univ+
        n*C*Real.sqrt t*ε^2*Real.exp (A*R)*(1+Real.sqrt Y)+
        2*n*(N:ℝ)^2*D*R^3*ε^2*t*Real.sqrt t*Real.exp (B*R)/Y := by
  obtain ⟨H,A,B,C,D,hH,hA,hB,hC,hD,hbound⟩ := windowWavePacket_global_upper_trace (ι:=ι) K he hc
  refine ⟨H,A,B,C,D,hH,hA,hB,hC,hD,?_⟩
  intro N _ hN R hR ε hε hε1 t ht v hv hcus Y hY hhigh
  apply nonnegative_trace_real_bound _ (fun _ => sq_nonneg _)
    _ _ _ (windowIdentityContribution_re_nonneg K he hc R _ _ _) (by positivity) (by positivity)
    _ (measure_ne_top _ _)
  exact hbound N hN R hR ε hε hε1 t ht v hv hcus Y hY hhigh

#print axioms nonnegative_trace_real_bound
#print axioms windowWavePacket_global_real_trace

end QuantitativeMaass
