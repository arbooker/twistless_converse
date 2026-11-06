module

public import SmallLevelTwentyOneIntegerWordGridGermsV1
public import QuantitativeArithmeticSmallLevelFirstShiftKernelV2

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Matrix Filter Set
open SmallLevelTwentyOne
open scoped Topology

/-- Exact data for a closed nonaffine word row. The conditions are integral,
so concrete rows can be supplied by kernel-checked arithmetic certificates. -/
structure ClosedWordRow where
  word : Word
  source : ℤ
  target : ℤ
  nonaffine : integerRaw word 1 0≠0
  denominator : integerDen word source≠0
  closed : 42*integerNumer word source=target*integerDen word source

def wordLeadingRow (m : ℕ) (χ : ℂ) (r : ClosedWordRow) (s : ℂ) (j : Fin 42) : ℂ :=
  (if j=gridIndex r.source then 1 else 0)-
    rationalWordCoefficient m χ r.word r.source 0 s*
      (if j=gridIndex r.target then 1 else 0)

def wordShiftRow (m : ℕ) (χ : ℂ) (r : ClosedWordRow) (n : ℕ)
    (s : ℂ) (j : Fin 42) : ℂ :=
  rationalWordCoefficient m χ r.word r.source (n+1) s*
    (if j=gridIndex r.target then 1 else 0)

theorem wordLeadingRow_apply (m : ℕ) (χ : ℂ) (r : ClosedWordRow)
    (s : ℂ) (v : Fin 42 → ℂ) :
    (∑ j, wordLeadingRow m χ r s j*v j)=v (gridIndex r.source)-
      rationalWordCoefficient m χ r.word r.source 0 s*v (gridIndex r.target) := by
  simp [wordLeadingRow,sub_mul,Finset.sum_sub_distrib]

theorem wordShiftRow_apply (m : ℕ) (χ : ℂ) (r : ClosedWordRow) (n : ℕ)
    (s : ℂ) (v : Fin 42 → ℂ) :
    (∑ j, wordShiftRow m χ r n s j*v j)=
      rationalWordCoefficient m χ r.word r.source (n+1) s*v (gridIndex r.target) := by
  simp [wordShiftRow]

theorem rationalWordCoefficient_analytic (m : ℕ) (χ : ℂ) (r : ClosedWordRow)
    (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z => rationalWordCoefficient m χ r.word r.source n z) s := by
  have he : wordCoefficient m χ r.word r.source n =
      (fun z => rationalWordCoefficient m χ r.word r.source n z) := by
    funext z
    exact wordCoefficient_rational m χ r.word r.source n z
  rw [← he]
  exact wordCoefficient_analytic m χ r.word r.source
    ((word_den_integer r.word r.source).mpr r.denominator) n s

theorem wordLeadingRow_analytic (m : ℕ) (χ : ℂ) (r : ClosedWordRow)
    (s : ℂ) (j : Fin 42) : AnalyticAt ℂ (fun z => wordLeadingRow m χ r z j) s :=
  analyticAt_const.sub ((rationalWordCoefficient_analytic m χ r 0 s).mul analyticAt_const)

theorem wordShiftRow_analytic (m : ℕ) (χ : ℂ) (r : ClosedWordRow)
    (n : ℕ) (s : ℂ) (j : Fin 42) :
    AnalyticAt ℂ (fun z => wordShiftRow m χ r n z j) s :=
  (rationalWordCoefficient_analytic m χ r (n+1) s).mul analyticAt_const

/-- All members of any finite word family have a common half-plane schedule
and their actual continued germs have exactly the rectangular matrix form
required by the first-shift elimination theorem. -/
theorem finite_word_matrix_germs {κ : Type*} [Fintype κ]
    (rows : κ → ClosedWordRow) {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) :
    ∃ (B : ℝ) (H : ℕ → ℂ → κ → ℂ),
      (∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => H n w i) z) ∧
      ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
        (fun z => ∑ j, wordLeadingRow m (ε*I^(2*m)) (rows i) z j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => H n z i+∑ a∈Finset.range n,
            ∑ j, wordShiftRow m (ε*I^(2*m)) (rows i) a z j*G (z+((a:ℂ)+1)) j) := by
  classical
  have hr (i : κ) := integer_word_grid_germs hf ε hε hlaw BG G hG hGF
    (rows i).word (rows i).nonaffine (rows i).source (rows i).target
    (rows i).denominator (rows i).closed
  choose bounds errors he using hr
  obtain ⟨B,hB⟩ := (Set.finite_range bounds).bddAbove
  have hb (i : κ) : bounds i≤B := hB (Set.mem_range_self i)
  refine ⟨B,fun n z i => errors i n z,?_,?_⟩
  · intro n i z hz
    exact (he i n).1 z (by change bounds i-((n:ℝ)+1)<z.re; linarith [hb i])
  · intro n i x hx
    simpa only [wordLeadingRow_apply,wordShiftRow_apply] using
      (he i n).2 x (by linarith [hb i])

#print axioms wordLeadingRow_apply
#print axioms finite_word_matrix_germs
end SmallLevelTwentyOneKnownWords
