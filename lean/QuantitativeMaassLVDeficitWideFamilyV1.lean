module

public import QuantitativeMaassLVDeficitFamilyV1
public import QuantitativeMaassWeightedBandCoverV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- A finite wide-band family obeys the same positive deficit estimate,
with the explicit number of unit windows. The degree is common to the
whole band, rather than being chosen separately at each spectral centre. -/
theorem cuspidal_wide_LV_deficit_family (N : ℕ) [NeZero N] (hN : 0<N)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ B J A C D E : ℝ,0<B ∧ 0<J ∧ 0<A ∧ 0<C ∧ 0<D ∧ 1≤E ∧
      ∀ (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N) (_hNp : (N:ZMod p)≠0)
      (_hpres : (p:ZMod N)=1) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (R : ℝ) (_hR : 0<R),1≤R → (∫ x,|x|^2*K x)/(R*(1/4))^2≤1 →
      ∀ t H L : ℝ,6≤t → 2≤H → 1≤L → L≤t/4 → B*R<Real.log H → ∀ d : ℕ,0<d →
      ∀ {ι : Type*} [Fintype ι] (v : ι→AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ (r τ : ι→ℝ),
      (∀ i,r i∈Icc (t-L) (t+L)) →
      (∀ i,FriedrichsGraph N (v i) (((1/4+(r i)^2:ℝ):ℂ) • v i)) →
      (∀ i,HeckeL2.operator N p hN hpN a b hab (v i)=(τ i:ℂ) • v i) →
      (1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2*
        (∑ i,(lvDeficitMultiplier p d (r i) (τ i))^2)≤
      4*L*(D*(2*t)*lvSphericalDeficit p (2*d)+C*Real.sqrt (2*t)*
        Real.exp (A*R+30*Real.log (E*(H+3)^2)+
          (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*((2*d:ℕ):ℝ))+J*(2*t)/H) := by
  obtain ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,hbound⟩ := cuspidal_unit_LV_deficit_family N hN K he hc hK hm
  refine ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,?_⟩
  intro p _ hpN hNp hpres a b hab R hR hR1 hmom t H L ht hH hL hLt hheight d hd ι _ v hv hcus r τ hr hgraph heigen
  classical
  obtain ⟨n,hn,s,hs,hcover⟩ := unit_band_cover t L ht hL hLt
  let P := fun j : Fin n => fun i : ι => r i∈Icc (s j-1/2) (s j+1/2)
  let w := fun i => (lvDeficitMultiplier p d (r i) (τ i))^2
  let c := (1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2
  let Q := D*(2*t)*lvSphericalDeficit p (2*d)+C*Real.sqrt (2*t)*
    Real.exp (A*R+30*Real.log (E*(H+3)^2)+
      (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*((2*d:ℕ):ℝ))+J*(2*t)/H
  have hδ : 0≤lvSphericalDeficit p (2*d) :=
    (finitePlaceSymbol_deficit_bounds p (2*d) (by omega) 0).1.trans
      (finitePlaceSymbol_deficit_bounds p (2*d) (by omega) 0).2
  have hQ : 0≤Q := by dsimp only [Q];positivity
  have hunit (j : Fin n) : c*(∑ i : {i // P j i},w i)≤Q := by
    have hj := hs j
    have hh := hbound p hpN hNp hpres a b hab R hR hR1 hmom (s j) H
      (by linarith) hH hheight d hd (fun i : {i // P j i} => v i)
      (hv.comp Subtype.val Subtype.val_injective) (fun i => hcus i)
      (fun i => r i) (fun i => τ i) (fun i => i.property)
      (fun i => hgraph i) (fun i => heigen i)
    apply hh.trans
    dsimp only [Q]
    gcongr <;> exact hj.2
  have hsum := finite_cover_weight_le P (fun i => hcover (r i) (hr i)) w (fun i => sq_nonneg _)
  calc
    _ ≤ c*(∑ j : Fin n,∑ i : {i // P j i},w i) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = ∑ j : Fin n,c*(∑ i : {i // P j i},w i) := Finset.mul_sum _ _ _
    _ ≤ ∑ _j : Fin n,Q := Finset.sum_le_sum (fun j _ => hunit j)
    _ = (n:ℝ)*Q := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ ≤ 4*L*Q := mul_le_mul_of_nonneg_right hn hQ

#print axioms cuspidal_wide_LV_deficit_family
end QuantitativeMaass
