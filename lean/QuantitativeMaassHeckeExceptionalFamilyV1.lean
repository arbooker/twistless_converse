module

public import QuantitativeMaassHeckeGrowingMomentV1
public import QuantitativeMaassTreeMomentBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- A quantitative exceptional-family count for actual joint Hecke and principal
eigenvectors, with an explicit growing degree and no physical gap assumption. -/
theorem cuspidal_hecke_exceptional_family_bound (N : ℕ) [NeZero N] (hN : 0<N)
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
      (∀ i,HeckeL2.operator N p hN hpN u v huv (f i)=(τ i:ℂ) • f i) → ∀ q : ℝ,0≤q → (∀ i,q≤|τ i|) → ∀ d : ℕ,
      (1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2*q^(2*d)*(Fintype.card ι:ℝ)≤
        D*t*(2:ℝ)^(2*d)+C*(heckeWordErrorGrowth p)^(2*d)*Real.sqrt t*
          Real.exp (A*R+30*Real.log (E*(H+3)^2))+
        (((p:ℝ)+1)/Real.sqrt (p:ℝ))^(2*d)*(J*t/H) := by
  obtain ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,hbound⟩ :=
    cuspidal_hecke_unit_eigenmoment_growing N hN K he hc hK hm
  refine ⟨B,J,A,C,D,E,hB,hJ,hA,hC,hD,hE,?_⟩
  intro p _ hpN hNp u v huv R hR hR1 hmom t H ht hH hheight ι _ f hf hcus r τ hr hgraph heigen q hq hτ d
  have hQ : 0≤heckeWordErrorGrowth p := by unfold heckeWordErrorGrowth;positivity
  have hh := hbound p hpN hNp u v huv R hR hR1 hmom t H ht hH hheight f hf hcus r τ hr hgraph heigen d
  have hpower (i : ι) : 0≤(τ i)^(2*d) := by rw [pow_mul];positivity
  rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => hpower i),
    ←ENNReal.ofReal_mul (sq_nonneg _),
    ←ENNReal.ofReal_mul (pow_nonneg (norm_nonneg (HeckeL2.operator N p hN hpN u v huv)) (2*d)),
    ←ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh
  have hcard : q^(2*d)*(Fintype.card ι:ℝ)≤∑ i,(τ i)^(2*d) := by
    classical
    calc
      _ = ∑ _i : ι,q^(2*d) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by
        have hi := pow_le_pow_left₀ hq (hτ i) (2*d)
        simpa only [pow_mul,sq_abs] using hi)
  calc
    _ = (1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2*(q^(2*d)*(Fintype.card ι:ℝ)) := by ring
    _ ≤ (1-(∫ x,|x|^2*K x)/(R*(1/4))^2)^2*(∑ i,(τ i)^(2*d)) :=
      mul_le_mul_of_nonneg_left hcard (sq_nonneg _)
    _ ≤ _ := hreal
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add _ le_rfl
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (normalized_treeWalkCount_bound p (2*d) (Fact.out : p.Prime).one_lt) (by positivity)
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [Nat.cast_add,Nat.cast_one] using HeckeL2.operator_norm_le N p hN hpN u v huv

#print axioms cuspidal_hecke_exceptional_family_bound

end QuantitativeMaass
