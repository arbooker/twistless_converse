module
public import SmallLevelTwentySixGridMatrixRowsV1
public import SmallLevelTwentySixGridRamanujanV1
public import SmallLevelTaylorRowCoefficientsV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Set SmallLevelAdditive SmallLevelTaylor
open scoped ModularForm

/-- Every coefficient of every positive shift is entire. -/
theorem gridMatrixScalar_analytic (m : ℕ) (f : ℕ→ℂ) (η : ℂ)
    (i : Fin 235) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (gridMatrixScalar m f η i n) s := by
  have hn : (gridGroupRate i:ℂ)≠0 := by exact_mod_cast (gridGroup_rate_pos i).ne'
  have hp : AnalyticAt ℂ (fun z : ℂ => (gridGroupRate i:ℂ)^(z-(m:ℂ))) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul
    (binomial_shift_analytic (2*m) n s)

theorem gridTaylorCoefficient_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (i : Fin 71) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (gridTaylorCoefficient m f ε i n) s := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/780≠0 := div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
  have hL : (0:ℝ)<gridTaylorL i := by
    exact_mod_cast (Nat.lcm_pos (by decide : 0<26) (pow_pos hv.1 2))
  exact taylorRowScalar_analytic (2*m) hL hr _ n s

/-- All235 word rows share one half-plane and the original coherent sign. -/
theorem grid_matrix_system_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ (B : ℝ) (error : Fin 235→ℕ→ℂ→ℂ), ∀ i : Fin 235, ∀ M : ℕ,
      AnalyticOnNhd ℂ (error i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        grid (2*m) f 780 ((gridGroupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m f (ε*I^(2*m)) i 0 s*
            grid (2*m) f 780 ((gridGroupTarget i:ℕ):ℤ) s=
        error i M s+∑ n∈Finset.range M,gridMatrixScalar m f (ε*I^(2*m)) i (n+1) s*
          grid (2*m) f 780 ((gridGroupTarget i:ℕ):ℤ) (s+((n:ℂ)+1)) := by
  choose b error hb using grid_matrix_rows_of_fricke m hf (grid_physical_sign m hε)
    (grid_fricke_of_laws m hε hlaw)
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 235) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,error,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms gridMatrixScalar_analytic
#print axioms gridTaylorCoefficient_analytic
#print axioms grid_matrix_system_of_laws
end SmallLevelTwentySixGrid
