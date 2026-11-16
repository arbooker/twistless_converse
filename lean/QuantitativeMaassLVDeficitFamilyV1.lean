module

public import QuantitativeMaassLVDeficitCoreV1
public import QuantitativeMaassLVDeficitLocalizedV1
public import QuantitativeMaassLVDeficitEigenV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- The actual joint cuspidal eigenfamily has a uniform LV deficit bound.
Its main term is the spherical deficit; the other terms are the explicit
geometric error and cusp tail. No physical spectral gap is assumed. -/
theorem cuspidal_unit_LV_deficit_family (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B J A C D E : ℝ,0<B ∧ 0<J ∧ 0<A ∧ 0<C ∧ 0<D ∧ 1≤E ∧
      ∀ (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (_hpres : (p:ZMod N)=1) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (R : ℝ) (_hR : 0<R),1≤R → (∫ x,|x|^2*K x)/(R*(1/4))^2≤1 →
      ∀ t H : ℝ,2≤t → 2≤H → B*R<Real.log H → ∀ d : ℕ,0<d →
      ∀ {ι : Type*} [Fintype ι] (v : ι→AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ (r τ : ι→ℝ),
      (∀ i,r i∈Icc (t-1/2) (t+1/2)) →
      (∀ i,FriedrichsGraph N (v i) (((1/4+(r i)^2:ℝ):ℂ) • v i)) →
      (∀ i,HeckeL2.operator N p hN hpN a b hab (v i)=(τ i:ℂ) • v i) →
      (1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2*
        (∑ i,(lvDeficitMultiplier p d (r i) (τ i))^2)≤
      D*t*lvSphericalDeficit p (2*d)+C*Real.sqrt t*
        Real.exp (A*R+30*Real.log (E*(H+3)^2)+
          (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*((2*d:ℕ):ℝ))+J*t/H := by
  obtain ⟨B,J,hB,hJ,hcut⟩ := cuspidal_unit_LV_deficit_localized N hN K he hc hK hm
  obtain ⟨A,C,D,E,hA,hC,hD,hE,hcore⟩ := actualLVDeficit_unit_core_upper N hN K he hc hK hm
  refine ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,?_⟩
  intro p _ hpN hNp hpres a b hab R hR hR1 hmom t H ht hH hheight d hd ι _ v hv hcus r τ hr hgraph heigen
  have hh := hcut p hpN hNp hpres a b hab R hR hR1 hmom t H
    (by linarith) (by linarith) hheight d v hv hcus r
    (fun i => lvDeficitMultiplier p d (r i) (τ i)) hr hgraph
    (fun i => actualLVDeficit_eigen N p hN hpN a b hab (v i) (r i) (τ i) (hgraph i) (heigen i) d)
  have hi := windowVolumeOperatorTrace_integrable N K he hc R hR (t-3/4) (t+3/4)
    (wideCompactCover N H) (wideCompactCover_compact N hN H)
    (actualLVDeficit N p hN hpN a b hab (2*d))
  have hpos (z : ℍ) : 0≤(inner ℂ
      (actualLVDeficit N p hN hpN a b hab (2*d) (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) z))
      (windowAbelColumn N K he hc R hR (t-3/4) (t+3/4) z)).re := by
    rw [←actualLVDeficit_norm_square]
    exact sq_nonneg _
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hpos)] at hh
  have hc := hcore p hpN hNp a b hab R hR hR1 t H ht hH (2*d) (by omega)
  have hδ : 0≤lvSphericalDeficit p (2*d) :=
    (finitePlaceSymbol_deficit_bounds p (2*d) (by omega) 0).1.trans
      (finitePlaceSymbol_deficit_bounds p (2*d) (by omega) 0).2
  have hb := hh.trans (add_le_add (ENNReal.ofReal_le_ofReal hc) le_rfl)
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
    ←ENNReal.ofReal_mul (sq_nonneg _),←ENNReal.ofReal_add (by positivity) (by positivity)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

#print axioms cuspidal_unit_LV_deficit_family
end QuantitativeMaass
