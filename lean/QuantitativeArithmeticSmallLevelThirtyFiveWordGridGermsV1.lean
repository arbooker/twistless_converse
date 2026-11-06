module

public import QuantitativeArithmeticSmallLevelThirtyFiveCoherentWordTaylorV1
public import QuantitativeArithmeticSmallLevelThirtyFiveGridAnalyticTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Set Filter SmallLevelAdditive SmallLevelTaylor
open FinitenessOriginalFourier
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

def wordDen (w : Word) (t : ℤ) : ℝ := coordC w*((t:ℝ)/210)+coordD w

def wordCoefficient (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ) (n : ℕ) (s : ℂ) : ℂ :=
  character χ w*(((wordDen w t)^2:ℝ):ℂ)^(s-(m:ℂ))*
    (I*((coordC w*wordDen w t:ℝ):ℂ))^n*
      Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

theorem wordCoefficient_analytic (m : ℕ) (χ : ℂ) (w : Word) (t : ℤ)
    (ht : wordDen w t≠0) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (wordCoefficient m χ w t n) z := by
  have hc : (((wordDen w t)^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ ht)
  have hp : AnalyticAt ℂ (fun s : ℂ => (((wordDen w t)^2:ℝ):ℂ)^(s-(m:ℂ))) z := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul
    (SmallLevelTaylor.binomial_shift_analytic (2*m) n z)

/-- Every word whose rational source and partner lie on the grid supplies
an actual row. The sign is the same one used for the Ramanujan rows. -/
theorem word_grid_rows_of_law {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (w : Word) (hC : coordC w≠0) (t u : ℤ) (ht : wordDen w t≠0)
    (hu : (coordA w*((t:ℝ)/210)+coordB w)/wordDen w t=(u:ℝ)/210) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector (2*m) f s (gridIndex t)-
          wordCoefficient m (ε*I^(2*m)) w t 0 s*gridVector (2*m) f s (gridIndex u)=
        error M s+∑ n∈Finset.range M,
          wordCoefficient m (ε*I^(2*m)) w t (n+1) s*
            gridVector (2*m) f (s+((n:ℂ)+1)) (gridIndex u) := by
  obtain ⟨B,error,hrow⟩ := word_taylor_of_law hm hf ε hε hlaw w hC ((t:ℝ)/210) ht
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrow (M+1)).1
  · intro s hs
    have he := (hrow (M+1)).2 s hs
    change _-character (ε*I^(2*m)) w*(((wordDen w t)^2:ℝ):ℂ)^(s-(m:ℂ))*
      (∑ n∈Finset.range (M+1), (I*((coordC w*wordDen w t:ℝ):ℂ))^n*
        Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
        transform (fullCoefficients f (2*m))
          ((coordA w*((t:ℝ)/210)+coordB w)/wordDen w t) (s+(n:ℂ)))=_ at he
    rw [hu,Finset.sum_range_succ'] at he
    simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,
      Nat.cast_add,Nat.cast_one] at he
    simp only [gridVector_index,grid,original,wordCoefficient,Nat.cast_zero,add_zero,
      pow_zero,Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
    rw [mul_add,Finset.mul_sum] at he
    simp only [mul_assoc,one_mul] at he ⊢
    linear_combination he

/-- The complete family of closed group-word rows holds as germs on the
continued grid. Neither grid continuation nor the original sign is re-chosen. -/
theorem word_grid_germs_of_law {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (w : Word) (hC : coordC w≠0) (t u : ℤ) (ht : wordDen w t≠0)
    (hu : (coordA w*((t:ℝ)/210)+coordB w)/wordDen w t=(u:ℝ)/210) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ x : ℂ, B-((M:ℝ)+1)<x.re →
        (fun s => G s (gridIndex t)-
          wordCoefficient m (ε*I^(2*m)) w t 0 s*G s (gridIndex u)) =ᶠ[𝓝[≠] x]
        (fun s => error M s+∑ n∈Finset.range M,
          wordCoefficient m (ε*I^(2*m)) w t (n+1) s*
            G (s+((n:ℂ)+1)) (gridIndex u)) := by
  obtain ⟨B,error,hrow⟩ := word_grid_rows_of_law hm hf ε hε hlaw w hC t u ht hu
  refine ⟨B,error,?_⟩
  intro M
  refine ⟨(hrow M).1,?_⟩
  intro x hx
  apply SmallLevelContinuation.halfplane_germ_identity
    (B-((M:ℝ)+1)) (max B BG) _ _ _ x hx
  · intro z _
    exact (hG (gridIndex t) z).meromorphicAt.sub
      ((wordCoefficient_analytic m _ w t ht 0 z).meromorphicAt.mul
        (hG (gridIndex u) z).meromorphicAt)
  · intro z hz
    apply ((hrow M).1 z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro n _
    exact (wordCoefficient_analytic m _ w t ht (n+1) z).meromorphicAt.mul
      ((hG (gridIndex u) (z+((n:ℂ)+1))).meromorphicAt.comp_analyticAt
        (g:=fun s : ℂ => s+((n:ℂ)+1)) (by fun_prop))
  · intro z hz
    have hzB : B<z.re := lt_of_le_of_lt (le_max_left B BG) hz
    have hzG : BG<z.re := lt_of_le_of_lt (le_max_right B BG) hz
    dsimp only
    rw [hGF z hzG,(hrow M).2 z hzB]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have hs : BG<(z+((n:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [hGF _ hs]

#print axioms wordCoefficient_analytic
#print axioms word_grid_rows_of_law
#print axioms word_grid_germs_of_law
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
