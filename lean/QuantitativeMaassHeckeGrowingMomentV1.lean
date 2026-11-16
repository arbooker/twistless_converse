module

public import QuantitativeMaassHeckeCoreMomentV1
public import QuantitativeMaassHeckeColumnMomentV1
public import QuantitativeMaassLocalizedEigenmomentV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- An actual cuspidal Hecke eigenmoment, with uniform growing-degree
geometric error and a proved cusp tail. All constants precede the prime,
degree, smoothing radius, window centre, cusp cutoff and finite eigenfamily. -/
theorem cuspidal_hecke_unit_eigenmoment_growing (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B J A C D E : ℝ,0<B ∧ 0<J ∧ 0<A ∧ 0<C ∧ 0<D ∧ 1≤E ∧
      ∀ (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (u v : ℤ) (huv : (p:ℤ)*u+(N:ℤ)*v=1)
      (R : ℝ) (_hR : 0<R),1≤R → (∫ x,|x|^2*K x)/(R*(1/4))^2≤1 →
      ∀ t H : ℝ,1≤t → 2≤H → B*R<Real.log H →
      ∀ {ι : Type*} [Fintype ι] (f : ι→AutomorphicSpace N),Orthonormal ℂ f →
      (∀ i,f i∈localCuspidalSpace N hN) → ∀ (r τ : ι→ℝ),
      (∀ i,r i∈Icc (t-1/2) (t+1/2)) →
      (∀ i,FriedrichsGraph N (f i) (((1/4+(r i)^2:ℝ):ℂ) • f i)) →
      (∀ i,HeckeL2.operator N p hN hpN u v huv (f i)=(τ i:ℂ) • f i) → ∀ d : ℕ,
      ENNReal.ofReal ((1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2)*∑ i,ENNReal.ofReal ((τ i)^(2*d))≤
        ENNReal.ofReal (D*t*(Real.sqrt (p:ℝ))⁻¹^(2*d)*(treeWalkCount (p+1) (2*d) 0:ℝ)+
          C*(heckeWordErrorGrowth p)^(2*d)*Real.sqrt t*
            Real.exp (A*R+30*Real.log (E*(H+3)^2)))+
        ENNReal.ofReal (‖HeckeL2.operator N p hN hpN u v huv‖^(2*d))*ENNReal.ofReal (J*t/H) := by
  obtain ⟨B,J,hB,hJ,hcut⟩ := cuspidal_unit_eigenmoment_localized N hN K he hc hK hm
  obtain ⟨A,C,D,E,hA,hC,hD,hE,hcore⟩ := upperWindowKernel_unit_core_growing N hN K he hc hK hm
  refine ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,?_⟩
  intro p _ hpN hNp u v huv R hR hR1 hmom t H ht hH hheight ι _ f hf hcus r τ hr hgraph heigen d
  have hT := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (HeckeL2.operator_selfAdjoint N p hN hpN u v huv)
  apply (hcut R hR hR1 hmom t H ht (by linarith only [hH]) hheight
    _ hT f hf hcus r τ hr hgraph heigen d).trans
  apply add_le_add _ le_rfl
  apply (hecke_cuspidal_column_compact_moment N p hN hpN hNp u v huv K he hc R hR
    (t-3/4) (t+3/4) d _).trans
  have hi : IntegrableOn (fun z =>
      (upperWindowKernel N p K hc R hR (t-3/4) (t+3/4) (2*d) HeckeUpper.root z).re)
      (wideCompactCover N H) :=
    (Complex.continuous_re.comp (upperWindowKernel_continuous N p K he hc R hR _ _ _ _)).continuousOn.integrableOn_compact
      (wideCompactCover_compact N hN H)
  have hpos (z : ℍ) : 0≤(upperWindowKernel N p K hc R hR (t-3/4) (t+3/4) (2*d) HeckeUpper.root z).re := by
    rw [←hecke_column_norm_square_kernel N p hN hpN hNp u v huv K he hc R hR _ _ d z]
    exact sq_nonneg _
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hpos)]
  exact ENNReal.ofReal_le_ofReal (hcore p R hR hR1 t H ht hH (2*d))

#print axioms cuspidal_hecke_unit_eigenmoment_growing

end QuantitativeMaass
