module

public import QuantitativeMaassLVRealTraceV1
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal InnerProductSpace ContDiff

namespace QuantitativeMaass

/-- Disjoint balls of radius one half show that an orthonormal family in a
separable complex Hilbert space has countable index. -/
theorem orthonormal_countable_index {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H]
    (v : ι → H) (hv : Orthonormal ℂ v) : Countable ι := by
  have hd (i j : ι) (hij : i≠j) : 1≤dist (v i) (v j) := by
    rw [dist_eq_norm]
    have hs := norm_sub_sq (𝕜:=ℂ) (v i) (v j)
    rw [hv.norm_eq_one i,hv.norm_eq_one j,hv.inner_eq_zero hij] at hs
    simp only [one_pow,RCLike.zero_re,mul_zero,sub_zero] at hs
    nlinarith [norm_nonneg (v i-v j)]
  have hdis : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/2:ℝ))
      (Metric.ball (v j) (1/2:ℝ))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' := Metric.mem_ball.mp hx
    have hy' := Metric.mem_ball.mp hy
    have ht := dist_triangle (v i) x (v j)
    rw [dist_comm (v i) x] at ht
    linarith [hd i j hij]
  exact hdis.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i,Metric.mem_ball_self (by norm_num)⟩)

/-- The genuine quotient L2 automorphic space is separable: the quotient
measure is finite and the upper half-plane has a countably generated Borel
sigma algebra. This is not a spectral-discreteness premise. -/
instance automorphicSpace_secondCountable (N : ℕ) [NeZero N] :
    SecondCountableTopology (AutomorphicSpace N) := by
  let : Fact ((1:ℝ≥0∞)≤2) := ⟨by norm_num⟩
  let : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
  let : SecondCountableTopology (Lp ℂ 2 (quotientMeasure N)) := inferInstance
  infer_instance

/-- A countable full-space basis supplies the countability needed by the
local pretrace/Tonelli identities, independently of the cusp eigenbasis. -/
theorem exists_countable_automorphic_basis (N : ℕ) [NeZero N] :
    ∃ (ι : Type), Countable ι ∧ Nonempty (HilbertBasis ι ℂ (AutomorphicSpace N)) := by
  obtain ⟨w,b,_⟩ := exists_hilbertBasis ℂ (AutomorphicSpace N)
  exact ⟨w,orthonormal_countable_index b b.orthonormal,⟨b⟩⟩

/-- Every genuine cusp Hilbert basis also has countable index. -/
theorem cuspidal_basis_countable {κ : Type*} (N : ℕ) [NeZero N] (hN : 0<N)
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) : Countable κ :=
  orthonormal_countable_index c c.orthonormal

/-- The ambient countable Hilbert basis is constructed, not assumed. -/
theorem actualLVFilter_kernel_integrable_of_cusp_basis {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Integrable (fun x => (inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re) (quotientMeasure N) := by
  obtain ⟨ι,hι,⟨b⟩⟩ := exists_countable_automorphic_basis N
  let : Countable ι := hι
  exact actualLVFilter_kernel_integrable N p hN hpN hNp hpres a d had k b c e he hgraph
    F hF hc hr R hR hs

/-- The ambient countable Hilbert basis is constructed, not assumed. -/
theorem actualLVFilter_real_trace_eq_weighted_spectrum_of_cusp_basis {κ : Type*}
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a d : ℤ) (had : (p:ℤ)*a+(N:ℤ)*d=1) (k : ℕ)
    (c : HilbertBasis κ ℂ (localCuspidalSpace N hN)) (e : κ → ℝ)
    (he : ∀ j,0≤e j)
    (hgraph : ∀ j,FriedrichsGraph N (c j:AutomorphicSpace N) ((e j:ℂ) • (c j:AutomorphicSpace N)))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫ x, (inner ℂ
      (actualLVFilter N p hN hpN a d had k
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
      (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
        x R hR (abelProfile_support F _ hs)))).re ∂quotientMeasure N)=∑' j,‖smoothPacketMultiplier (coshTimeTest F) (e j)‖^2 *
        (inner ℂ (actualLVFilter N p hN hpN a d had k (c j:AutomorphicSpace N))
          (c j:AutomorphicSpace N)).re := by
  obtain ⟨ι,hι,⟨b⟩⟩ := exists_countable_automorphic_basis N
  let : Countable ι := hι
  exact actualLVFilter_real_trace_eq_weighted_spectrum N p hN hpN hNp hpres a d had k b c e he hgraph
    F hF hc hr R hR hs

#print axioms orthonormal_countable_index
#print axioms automorphicSpace_secondCountable
#print axioms exists_countable_automorphic_basis

#print axioms cuspidal_basis_countable
#print axioms actualLVFilter_kernel_integrable_of_cusp_basis
#print axioms actualLVFilter_real_trace_eq_weighted_spectrum_of_cusp_basis

end QuantitativeMaass
