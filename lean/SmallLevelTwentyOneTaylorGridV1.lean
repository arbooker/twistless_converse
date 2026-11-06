module

public import SmallLevelTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Set MeasureTheory SmallLevelTaylor FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct

/-- The 28 Taylor rows in the written 42 by 42 leading system, in order.
The four entire Ramanujan rows and ten exact Hecke rows are separate. -/
def taylorSpecs : Fin 28 → ℕ×ℤ :=
  ![(1,1),(1,-1),(1,2),(1,-2),(1,3),(1,-3),(1,4),(1,-4),(1,6),(1,-6),(1,7),(1,-7),
    (2,1),(2,-1),(2,3),(2,-3),(3,1),(3,-1),(3,2),(3,-2),(3,4),(3,-4),
    (6,1),(6,-1),(7,1),(7,-1),(7,2),(7,3)]

def rowQ (i : Fin 28) : ℕ := (taylorSpecs i).1
def rowT (i : Fin 28) : ℤ := (taylorSpecs i).2
def rowL (i : Fin 28) : ℕ := Nat.lcm 21 ((rowQ i)^2)
def rowD (i : Fin 28) : ℤ := (42:ℤ)^2/(rowL i:ℤ)
def rowPartner (i : Fin 28) : ℤ := -(rowD i/rowT i)

/-- Kernel-checked finite arithmetic certificate; no native evaluation. -/
theorem taylorSpecs_valid : ∀ i : Fin 28,
    0<rowQ i ∧ rowQ i∣42 ∧ rowT i≠0 ∧
      (rowL i:ℤ)*rowD i=(42:ℤ)^2 ∧ rowT i∣rowD i := by decide

def rowCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 28) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (rowL i) ((rowT i:ℝ)/42) (root 21 f (rowQ i)*ε*I^k) n s

def rowError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 28) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f (rowQ i)) k)
    (rowL i) ((rowT i:ℝ)/42) (root 21 f (rowQ i)*ε*I^k) (M+1)) s

/-- All 28 actual Taylor rows of the level-21 system, with one sign and one
common initial half-plane for all rows and all Taylor orders. This is the
analytic closed-grid input, not yet the determinant or pole-removal proof. -/
theorem original_taylor_system {k : ℕ} (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ, ∀ i : Fin 28, ∀ M : ℕ,
      AnalyticOnNhd ℂ (rowError k f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum k f 42 (rowQ i) (rowT i) s-
          rowCoefficient k f ε i 0 s*gridSum k f 42 (rowQ i) (rowPartner i) s=
        rowError k f ε i M s+
          ∑ n∈Finset.range M, rowCoefficient k f ε i (n+1) s*
            gridSum k f 42 (rowQ i) (rowPartner i) (s+((n:ℂ)+1)) := by
  obtain ⟨ε,hε,hrows⟩ := original_closed_grid_taylor_rows (by decide : 0<21) hk hf
  have hi (i : Fin 28) := hrows 42 (rowQ i) (by decide) (taylorSpecs_valid i).1
    (taylorSpecs_valid i).2.1 (rowT i) (rowD i) (taylorSpecs_valid i).2.2.1
    (taylorSpecs_valid i).2.2.2.1 (taylorSpecs_valid i).2.2.2.2
  choose b hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 28) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨ε,hε,B,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

theorem rowCoefficient_analytic (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (i : Fin 28) (n : ℕ) (s : ℂ) : AnalyticAt ℂ (rowCoefficient k f ε i n) s := by
  apply taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<21) (pow_pos (taylorSpecs_valid i).1 2)
  · exact div_ne_zero (by exact_mod_cast (taylorSpecs_valid i).2.2.1) (by norm_num)

#print axioms taylorSpecs_valid
#print axioms original_taylor_system
#print axioms rowCoefficient_analytic
end SmallLevelTwentyOne
