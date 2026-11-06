module
public import SmallLevelTaylorTheoryV4
public import SmallLevelAdditiveTheoryV4
public import QuantitativeArithmeticRamifiedFullTraceV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelRamifiedPrimeAdditive
open Complex SmallLevelAdditive SmallLevelTaylor

def heckeScalar (m : ℕ) (f : ℕ→ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  QuantitativeArithmeticRamifiedFullTrace.multiplier f m p*(p:ℂ)^(-s)

/-- The actual ramified-prime additive equation, uniformly in the translate. -/
theorem original_ramified_row {N p : ℕ} (hp : p.Prime) (hN : p∣N) (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range p, original (2*m) f (r+(j:ℝ)/p) s)=
        heckeScalar m f p s*original (2*m) f ((p:ℝ)*r) s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  obtain ⟨B,hB⟩:=SmallLevelTaylor.additive_convergence_halfplane
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m))
  refine ⟨B,fun r s hs => ?_⟩
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  let C:=QuantitativeArithmeticRamifiedFullTrace.multiplier f m p
  have h1:=SmallLevelTaylor.dilated_ray_hasMellin (by exact_mod_cast hp.pos : (0:ℝ)<p) r s (hB ((p:ℝ)*r) s hs).1
  have he : Set.EqOn
      (fun y : ℝ => ∑ j∈Finset.range p, FinitenessFourierConstruction.fourier a
        (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I))
      (fun y : ℝ => C*FinitenessFourierConstruction.fourier a ((p:ℂ)*((r:ℂ)+(y:ℂ)*I))) (Set.Ioi 0) := by
    intro y hy
    dsimp only
    have hh:=QuantitativeArithmeticRamifiedFullTrace.original_complete_even hf.toEulerData
      hp hN hm (z:=(r:ℂ)+(y:ℂ)*I) (by simpa using hy)
    change QuantitativeArithmeticRetainedReconstruction.completeTwist
      (FinitenessFourierConstruction.fourier a) p ((r:ℂ)+(y:ℂ)*I)=_ at hh
    have hsum : (∑ j∈Finset.range p, FinitenessFourierConstruction.fourier a
        (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I))=
        QuantitativeArithmeticRetainedReconstruction.completeTwist
          (FinitenessFourierConstruction.fourier a) p ((r:ℂ)+(y:ℂ)*I) := by
      unfold QuantitativeArithmeticRetainedReconstruction.completeTwist
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      push_cast
      ring
    rw [hsum,hh]
  have hsum : mellin
      (fun y : ℝ => ∑ j∈Finset.range p, FinitenessFourierConstruction.fourier a
        (((r+(j:ℝ)/p:ℝ):ℂ)+(y:ℂ)*I)) s=
      ∑ j∈Finset.range p, original (2*m) f (r+(j:ℝ)/p) s := by
    unfold mellin
    simp only [Finset.smul_sum]
    rw [MeasureTheory.integral_finsetSum (Finset.range p) (fun j _ => (hB (r+(j:ℝ)/p) s hs).1)]
    apply Finset.sum_congr rfl
    intro j _
    exact (hB (r+(j:ℝ)/p) s hs).2
  rw [← hsum,mellin_congr_positive he s]
  change mellin (fun y : ℝ => C • FinitenessFourierConstruction.fourier a
    ((p:ℂ)*((r:ℂ)+(y:ℂ)*I))) s=_
  have h1eq : mellin (fun y : ℝ => FinitenessFourierConstruction.fourier a
      ((p:ℂ)*((r:ℂ)+(y:ℂ)*I))) s=(p:ℂ)^(-s)*
      mellin (fun y : ℝ => FinitenessFourierConstruction.fourier a
        ((((p:ℝ)*r:ℝ):ℂ)+(y:ℂ)*I)) s := by
    simpa only [Complex.ofReal_natCast] using h1.2
  rw [mellin_const_smul,h1eq,(hB ((p:ℝ)*r) s hs).2]
  simp only [smul_eq_mul,heckeScalar,C,mul_assoc,original]


#print axioms original_ramified_row
end SmallLevelRamifiedPrimeAdditive
