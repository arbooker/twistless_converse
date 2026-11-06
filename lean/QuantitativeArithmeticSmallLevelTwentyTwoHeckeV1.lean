module

public import QuantitativeArithmeticSmallLevelTwentyTwoMellinV1
public import SmallLevelTaylorTheoryV4
public import SmallLevelAdditiveTheoryV4
public import QuantitativeArithmeticRamifiedFullTraceV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyTwo
open Complex SmallLevelAdditive SmallLevelTaylor

def evenOne (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  original k f (1/5) s+original k f (-1/5) s

def evenTwo (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  original k f (2/5) s+original k f (-2/5) s

def tenthSum (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  original k f (1/10) s+original k f (-1/10) s

def heckeScalar (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2*(2:ℂ)^(-s)

theorem original_add_int (k : ℕ) (f : ℕ → ℂ) (r : ℝ) (n : ℤ) (s : ℂ) :
    original k f (r+(n:ℝ)) s=original k f r s := transform_add_int _ r n s

theorem period_three_fifths (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    original k f (3/5) s=original k f (-2/5) s := by
  convert original_add_int k f (-2/5) 1 s using 1; norm_num

theorem period_four_fifths (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    original k f (4/5) s=original k f (-1/5) s := by
  convert original_add_int k f (-1/5) 1 s using 1; norm_num

/-- The ramified complete trace gives the actual additive Hecke2 row. -/
theorem original_ramified_row (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ B : ℝ, ∀ r : ℝ, ∀ s : ℂ, B<s.re →
      (∑ j∈Finset.range 2, original (2*m) f (r+(j:ℝ)/2) s)=
        heckeScalar m f s*original (2*m) f (2*r) s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  obtain ⟨B,hB⟩:=SmallLevelTaylor.additive_convergence_halfplane
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m))
  refine ⟨B,fun r s hs => ?_⟩
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  let C:=QuantitativeArithmeticRamifiedFullTrace.multiplier f m 2
  have h1:=SmallLevelTaylor.dilated_ray_hasMellin (by norm_num : (0:ℝ)<2) r s (hB (2*r) s hs).1
  have he : Set.EqOn
      (fun y : ℝ => ∑ j∈Finset.range 2, FinitenessFourierConstruction.fourier a
        (((r+(j:ℝ)/2:ℝ):ℂ)+(y:ℂ)*I))
      (fun y : ℝ => C*FinitenessFourierConstruction.fourier a ((2:ℂ)*((r:ℂ)+(y:ℂ)*I))) (Set.Ioi 0) := by
    intro y hy
    dsimp only
    have hh:=QuantitativeArithmeticRamifiedFullTrace.original_complete_even hf.toEulerData
      (by decide : Nat.Prime 2) (by decide : 2∣22) hm (z:=(r:ℂ)+(y:ℂ)*I) (by simpa using hy)
    change QuantitativeArithmeticRetainedReconstruction.completeTwist
      (FinitenessFourierConstruction.fourier a) 2 ((r:ℂ)+(y:ℂ)*I)=_ at hh
    have hsum : (∑ j∈Finset.range 2, FinitenessFourierConstruction.fourier a
        (((r+(j:ℝ)/2:ℝ):ℂ)+(y:ℂ)*I))=
        QuantitativeArithmeticRetainedReconstruction.completeTwist
          (FinitenessFourierConstruction.fourier a) 2 ((r:ℂ)+(y:ℂ)*I) := by
      unfold QuantitativeArithmeticRetainedReconstruction.completeTwist
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      push_cast
      ring
    rw [hsum,hh]
    rfl
  have hsum : mellin
      (fun y : ℝ => ∑ j∈Finset.range 2, FinitenessFourierConstruction.fourier a
        (((r+(j:ℝ)/2:ℝ):ℂ)+(y:ℂ)*I)) s=
      ∑ j∈Finset.range 2, original (2*m) f (r+(j:ℝ)/2) s := by
    unfold mellin
    simp only [Finset.smul_sum]
    rw [MeasureTheory.integral_finsetSum (Finset.range 2) (fun j _ => (hB (r+(j:ℝ)/2) s hs).1)]
    apply Finset.sum_congr rfl
    intro j _
    exact (hB (r+(j:ℝ)/2) s hs).2
  rw [← hsum,mellin_congr_positive he s]
  change mellin (fun y : ℝ => C • FinitenessFourierConstruction.fourier a
    ((2:ℂ)*((r:ℂ)+(y:ℂ)*I))) s=_
  have h1eq : mellin (fun y : ℝ => FinitenessFourierConstruction.fourier a
      ((2:ℂ)*((r:ℂ)+(y:ℂ)*I))) s=(2:ℂ)^(-s)*
      mellin (fun y : ℝ => FinitenessFourierConstruction.fourier a
        (((2*r:ℝ):ℂ)+(y:ℂ)*I)) s := by
    simpa only [Complex.ofReal_ofNat] using h1.2
  rw [mellin_const_smul,h1eq,(hB (2*r) s hs).2]
  simp only [smul_eq_mul,heckeScalar,C,mul_assoc,original]

/-- The ramified even-sum row has no quadratic local term. -/
theorem original_even_hecke (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 22 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      heckeScalar m f s*evenOne (2*m) f s=evenTwo (2*m) f s+tenthSum (2*m) f s := by
  obtain ⟨B,hB⟩:=original_ramified_row m hm hf
  refine ⟨B,fun s hs => ?_⟩
  have hp:=hB (1/10) s hs
  have hn:=hB (-1/10) s hs
  norm_num [Finset.sum_range_succ] at hp hn
  rw [period_three_fifths] at hp
  unfold evenOne evenTwo tenthSum
  simp only [neg_div] at hp hn ⊢
  linear_combination -hp-hn

/-- The actual modulus-five Ramanujan sum is the sum of the two even
classes; this identity holds even for the totalized Dirichlet series. -/
theorem ramanujan_five (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    SmallLevelTaylor.ramanujanAdditive k f 5 0 s=evenOne k f s+evenTwo k f s := by
  unfold SmallLevelTaylor.ramanujanAdditive FinitenessRamanujanSum.residues
  rw [show (Finset.range 5).filter (fun a => Nat.Coprime a 5)={1,2,3,4} by decide]
  norm_num
  rw [period_three_fifths,period_four_fifths]
  unfold evenOne evenTwo
  ring

#print axioms original_even_hecke
#print axioms ramanujan_five
end QuantitativeArithmeticSmallLevelTwentyTwo
