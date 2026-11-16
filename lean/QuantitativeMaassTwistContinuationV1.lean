module

public import QuantitativeMaassEulerFrickeV1
public import FinitenessNormalizedTwistProductV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The Maass completion uses L^(s/2), so the existing normalized local
product needs this constant conductor correction. -/
def maassTwistCorrection (N q : ℕ) (b : ℕ → ℂ) (s : ℂ) : ℂ :=
  (FinitenessTwistConductor.ratio N q:ℂ)^(1/4:ℂ)*FinitenessNormalizedTwistProduct.product N b q s

theorem maassTwistCorrection_entire (N q : ℕ) (b : ℕ → ℂ) :
    Differentiable ℂ (maassTwistCorrection N q b) :=
  (FinitenessNormalizedTwistProduct.product_entire N b q).const_mul _

theorem maassTwistCorrection_bound (N q : ℕ) (b : ℕ → ℂ) :
    FinitenessFiniteOrder.Bound (maassTwistCorrection N q b) :=
  FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
    (FinitenessNormalizedTwistProduct.product_bound N b q)

theorem maassTwistCorrection_reciprocal {N : ℕ} {b : ℕ → ℂ}
    (hb : FinitenessOriginalInput.EulerData N b) (hN : 0<N) (q : ℕ) (s : ℂ) :
    maassTwistCorrection N q b s=FinitenessNormalizedTwistProduct.root N b q*
      maassTwistCorrection N q b (1-s) := by
  unfold maassTwistCorrection
  rw [FinitenessNormalizedTwistProduct.reciprocal hb hN]
  ring

theorem maassTwistCorrection_completed {N q : ℕ} {b : ℕ → ℂ} (hN : 0<N) (hq : 0<q)
    (p : MaassSpectral.Parameter) (σ : ℕ) (s : ℂ)
    (hDir : MaassOriginal.dirichlet (FinitenessRamanujanFourier.twisted b q) s=
      FinitenessTwistedEulerProduct.multiplier N b q s*MaassOriginal.dirichlet b s) :
    MaassOriginal.completed (Nat.lcm N (q^2):ℝ) p σ (FinitenessRamanujanFourier.twisted b q) s=
      maassTwistCorrection N q b s*MaassOriginal.completed (N:ℝ) p σ b s := by
  have hn : (FinitenessTwistConductor.ratio N q:ℂ)≠0 := by
    exact_mod_cast (FinitenessTwistConductor.ratio_pos hN hq).ne'
  have hp : (FinitenessTwistConductor.ratio N q:ℂ)^(s/2)=
      (FinitenessTwistConductor.ratio N q:ℂ)^(1/4:ℂ)*
        (FinitenessTwistConductor.ratio N q:ℂ)^((s-1/2)/2) := by
    rw [←Complex.cpow_add _ _ hn]
    congr 1
    ring
  unfold maassTwistCorrection MaassOriginal.completed
  rw [FinitenessNormalizedTwistProduct.product_eq hN hq]
  simp only [Complex.ofReal_natCast]
  rw [hDir,←FinitenessTwistConductor.mul_ratio N q,Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow,hp]
  ring

/-- Every positive literal Ramanujan twist obtains its Maass continuation and
coherent root number from the original Euler data and untwisted continuation. -/
theorem maass_twisted_continuation {N : ℕ} {b : ℕ → ℂ} (hN : 0<N)
    (hb : FinitenessOriginalInput.EulerData N b) (p : MaassSpectral.Parameter) (σ : ℕ) (ε : ℂ)
    (hcont : MaassOriginal.Continuation (N:ℝ) p σ b ε) {q : ℕ} (hq : 0<q) :
    MaassOriginal.Continuation (Nat.lcm N (q^2):ℝ) p σ (FinitenessRamanujanFourier.twisted b q)
      (FinitenessNormalizedTwistProduct.root N b q*ε) := by
  obtain ⟨F,hFd,hFo,⟨a,hFa⟩,hFE⟩ := hcont
  obtain ⟨c,hc⟩ := FinitenessTwistedEulerProduct.original_product hb
  refine ⟨fun s => maassTwistCorrection N q b s*F s,(maassTwistCorrection_entire N q b).mul hFd,?_,?_,?_⟩
  · exact FinitenessInputBounds.bound_finiteOrder (FinitenessFiniteOrder.mul
      (maassTwistCorrection_bound N q b) (FinitenessInputBounds.finiteOrder_bound hFd.continuous hFo))
  · refine ⟨max a c,fun s hs => ?_⟩
    dsimp only
    rw [hFa s (lt_of_le_of_lt (le_max_left _ _) hs)]
    exact (maassTwistCorrection_completed hN hq p σ s
      (hc s (lt_of_le_of_lt (le_max_right _ _) hs) q hq.ne')).symm
  · intro s
    dsimp only
    rw [maassTwistCorrection_reciprocal hb hN,hFE s]
    ring

#print axioms maassTwistCorrection_entire
#print axioms maassTwistCorrection_bound
#print axioms maassTwistCorrection_reciprocal
#print axioms maassTwistCorrection_completed
#print axioms maass_twisted_continuation

end QuantitativeMaass
