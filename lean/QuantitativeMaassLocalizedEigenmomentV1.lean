module

public import QuantitativeMaassCuspidalQuotientTailV1
public import QuantitativeArithmeticMaassPositiveCutoffV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- An actual finite cuspidal eigenmoment is bounded by its literal compact
column energy and the proved O_N(t/H) tail. Neither term is a trace hypothesis. -/
theorem cuspidal_unit_eigenmoment_localized (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ (R : ℝ) (hR : 0<R),1≤R →
      (∫ u,|u|^2*K u)/(R*(1/4))^2≤1 → ∀ t H : ℝ,1≤t → 0<H → B*R<Real.log H →
      ∀ {ι : Type*} [Fintype ι] (T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N),
      T.toLinearMap.IsSymmetric → ∀ (v : ι→AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ (r τ : ι→ℝ),
      (∀ i,r i∈Icc (t-1/2) (t+1/2)) →
      (∀ i,FriedrichsGraph N (v i) (((1/4+(r i)^2:ℝ):ℂ) • v i)) →
      (∀ i,T (v i)=(τ i:ℂ) • v i) → ∀ d : ℕ,
      ENNReal.ofReal ((1-(∫ u,|u|^2*K u)/(R*(1/4))^2)^2)*∑ i,ENNReal.ofReal ((τ i)^(2*d))≤
        (∫⁻ z in wideCompactCover N H,ENNReal.ofReal (‖(T^d)
          (localCuspidalProjection N hN (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) z))‖^2))+
        ENNReal.ofReal (‖T‖^(2*d))*ENNReal.ofReal (C*t/H) := by
  obtain ⟨B,C,hB,hC,htail⟩ := cuspidal_window_column_quotient_unit_tail N hN K he hc hK hm
  refine ⟨B,C,hB,hC,?_⟩
  intro R hR hR1 hmom t H ht hH hheight ι _ T hT v hv hcus r τ hr hgraph heigen d
  have hcut := QuantitativeArithmeticMaassPositiveCutoff.enlarged_window_eigenmoment_cutoff
    N K he hc R hR (t-1/2) (t+1/2) hK hm (1/4) (by norm_num) (by linarith)
    2 hmom (localCuspidalProjection N hN)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (localCuspidalProjection_selfAdjoint N hN))
    T hT v hv (fun i => Submodule.starProjection_eq_self_iff.mpr (hcus i)) r τ hr hgraph heigen d
    (orbitCore N (wideCompactCover N H))
    (orbitCore_measurable N _ (wideCompactCover_compact N hN H).measurableSet)
  rw [show (t-1/2)-1/4=t-3/4 by ring,show (t+1/2)+1/4=t+3/4 by ring] at hcut
  apply hcut.trans
  apply add_le_add
  · apply quotient_orbitCore_lintegral_le N _ (wideCompactCover_compact N hN H).measurableSet
    · exact ((((T^d).continuous.comp (localCuspidalProjection N hN).continuous).comp
        (windowAbelColumn_continuous N K he hc R hR _ _)).norm.pow 2).measurable.ennreal_ofReal
    · intro g z
      exact congrArg (fun v => ENNReal.ofReal (‖(T^d) (localCuspidalProjection N hN v)‖^2))
        (windowAbelColumn_invariant N K he hc R hR (t-3/4) (t+3/4) g z)
  · exact mul_le_mul' le_rfl (htail R hR hR1 t H ht hH hheight)

#print axioms cuspidal_unit_eigenmoment_localized

end QuantitativeMaass
