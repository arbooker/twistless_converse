module

public import QuantitativeMaassWindowRealTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Upper trace for the enlarged literal interval, expressed at the original
centre and width so its asymptotic errors need no change of normalization. -/
theorem windowWavePacket_enlarged_upper_trace {ι : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ H A B C D : ℝ,0<H ∧ 0<A ∧ 0<B ∧ 0≤C ∧ 0≤D ∧
      ∀ R : ℝ,∀ hR : 1≤R,∀ ε δ t : ℝ,0≤ε → ε≤1 → 0≤δ → 2*δ≤ε → 1≤t →
      ∀ (v : ι → AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ Y : ℝ,2≤Y → H*R<Real.log Y →
      (∑' i,‖windowWavePacket N K hc R
        (lt_of_lt_of_le zero_lt_one hR) (t-δ) (t+ε+δ) (v i)‖^2)≤
        (windowIdentityContribution K hc R
          (lt_of_lt_of_le zero_lt_one hR) (t-δ) (t+ε+δ)).re*(quotientMeasure N).real univ+
        C*Real.sqrt t*ε^2*Real.exp (A*R)*(1+Real.sqrt Y)+
        D*R^3*ε^2*t*Real.sqrt t*Real.exp (B*R)/Y := by
  obtain ⟨H,A,B,C,D,hH,hA,hB,hC,hD,hbound⟩ := windowWavePacket_global_real_trace (ι:=ι) K he hc
  let n : ℝ := Nat.card (SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  have hn : 0≤n := Nat.cast_nonneg _
  refine ⟨H,A,B,2*n*C,8*n*(N:ℝ)^2*D,hH,hA,hB,by positivity,by positivity,?_⟩
  intro R hR ε δ t hε hε1 hδ hδε ht v hv hcus Y hY hhigh
  let w := ε/2+δ
  let s := t+ε/2
  have hw : 0≤w := by dsimp [w]; positivity
  have hwε : w≤ε := by dsimp [w]; linarith
  have hs : 1≤s := by dsimp [s]; linarith
  have hs0 : 0≤s := by linarith
  have hst : s≤2*t := by dsimp [s]; linarith
  have hsqrt : Real.sqrt s≤2*Real.sqrt t := by
    nlinarith [Real.sq_sqrt hs0,Real.sq_sqrt (by linarith : 0≤t),
      Real.sqrt_nonneg s,Real.sqrt_nonneg t]
  have hprod : s*Real.sqrt s≤4*t*Real.sqrt t := by
    calc
      _ ≤ (2*t)*(2*Real.sqrt t) := mul_le_mul hst hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hh := (hbound N hN R hR w hw (hwε.trans hε1) s hs v hv hcus Y hY hhigh).2
  have ha : s-w=t-δ := by dsimp [s,w]; ring
  have hb : s+w=t+ε+δ := by dsimp [s,w]; ring
  rw [ha,hb] at hh
  apply hh.trans
  apply add_le_add
  · apply add_le_add le_rfl
    calc
      _ ≤ n*C*(2*Real.sqrt t)*ε^2*Real.exp (A*R)*(1+Real.sqrt Y) := by gcongr
      _ = _ := by ring
  · calc
      _ = (2*n*(N:ℝ)^2*D)*R^3*w^2*(s*Real.sqrt s)*Real.exp (B*R)/Y := by ring
      _ ≤ (2*n*(N:ℝ)^2*D)*R^3*ε^2*(4*t*Real.sqrt t)*Real.exp (B*R)/Y := by gcongr
      _ = _ := by ring

#print axioms windowWavePacket_enlarged_upper_trace

end QuantitativeMaass
