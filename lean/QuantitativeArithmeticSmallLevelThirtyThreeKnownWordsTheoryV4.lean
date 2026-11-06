module

public import QuantitativeArithmeticRectangularContinuationTheoryV4
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeFullMatricesV1
public import QuantitativeArithmeticSmallLevelThirtyThreeGridOriginalRowsV1
public import QuantitativeArithmeticSmallLevelThirtyThreeLaurentRowsV1
public import QuantitativeArithmeticSmallLevelThirtyThreeLaurentTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusFirstSyzygyV1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusFirstSyzygyV1
public import SmallLevelTwentyOneThirdShiftScaleV1
public import SmallLevelUniversalPoleFirstShiftV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyThreeKnownWords. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeInitialSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Set SmallLevelAdditive

/-- The original source system with a prescribed coherent sign and a common
half-plane that also provides analyticity of every original additive transform. -/
theorem initial_system_of_laws (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ (B : ℝ) (error : GridSource→ℕ→ℂ→ℂ),
      (∀ i : Fin 66,∀ z : ℂ,B<z.re → AnalyticAt ℂ (fun s => gridVector (2*m) f s i) z) ∧
      (∀ M : ℕ,∀ i : GridSource,∀ z : ℂ,B-((M:ℝ)+1)<z.re → AnalyticAt ℂ (error i M) z) ∧
      ∀ M : ℕ,∀ s : ℂ,B<s.re → ∀ i : GridSource,
        gridLeadingRows m f ε s (gridVector (2*m) f s) i=error i M s+
          ∑ n∈Finset.range M,gridShiftRows m f ε n s
            (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  choose b error hb using original_source_row m hm hf hε hlaw
  have : Nonempty GridSource := ⟨.word 0⟩
  let BS : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbS (i : GridSource) : b i≤BS:=Finset.le_sup' b (Finset.mem_univ i)
  obtain ⟨BF,hF⟩:=original_common_halfplane hf
  let B : ℝ:=max BS BF
  have hBS : BS≤B:=le_max_left _ _
  have hBF : BF≤B:=le_max_right _ _
  refine ⟨B,error,?_,?_,?_⟩
  · intro i z hz
    exact (hF (((i:ℕ):ℝ)/66) z (lt_of_le_of_lt hBF hz)).1
  · intro M i z hz
    apply (hb i M).1 z
    change b i-((M:ℝ)+1)<z.re
    linarith [hbS i]
  · intro M s hs i
    exact (hb i M).2 s (lt_of_le_of_lt ((hbS i).trans hBS) hs)

#print axioms initial_system_of_laws
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeGridContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix

theorem grid_continuation_of_laws (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ,∃ G : ℂ→Fin 66→ℂ,
      (∀ i z,MeromorphicNFAt (fun s => G s i) z) ∧
      ∀ z,B<z.re → G z=gridVector (2*m) f z := by
  obtain ⟨B,E,hF,hE,hrow⟩ := initial_system_of_laws m hm hf hε hlaw
  refine ⟨B,?_⟩
  apply QuantitativeArithmeticRectangularContinuation.meromorphic_continuation
    B (gridVector (2*m) f) (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε)
    (fun n s i => E i n s) hF
    (fun x i j => fullLeadingMatrix_analytic m f ε i j x)
    (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.original_full_rank m hf ε hε)
    (fun n x i j => fullShiftMatrix_analytic m f ε n i j x)
    (fun n i z hz => (hE n i z hz).meromorphicAt)
  intro n s hs
  rw [fullLeadingMatrix_mulVec]
  simp_rw [fullShiftMatrix_mulVec]
  funext i
  simp only [Pi.add_apply,Finset.sum_apply]
  exact hrow n s hs i

/-- All66 additive transforms continue from the original hypotheses, with
no exclusion of auxiliary eigenvalues and with their original coherent sign. -/
theorem original_grid_continuation (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ (ε : ℂ) (B : ℝ) (G : ℂ→Fin 66→ℂ),
      (ε=1 ∨ ε= -1) ∧ GridFrickeLaws (2*m) f ε ∧
      (∀ i z,MeromorphicNFAt (fun s => G s i) z) ∧
      ∀ z,B<z.re → G z=gridVector (2*m) f z := by
  obtain ⟨ε,hε,hlaw⟩ := original_grid_fricke_laws hf
  obtain ⟨B,G,hG,hGF⟩ := grid_continuation_of_laws m hm hf ε hε hlaw
  exact ⟨ε,B,G,hε,hlaw,hG,hGF⟩

#print axioms original_grid_continuation
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreePoleSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix Filter
open scoped Topology

/-- The original grid and all original Taylor equations on one half-plane.
This records meromorphic continuation only, with no pole-removability claim. -/
structure PoleSystem (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) where
  B : ℝ
  G : ℂ→Fin 66→ℂ
  E : ℕ→ℂ→GridSource→ℂ
  meromorphic : ∀ i x,MeromorphicNFAt (fun z => G z i) x
  agreement : ∀ z,B<z.re → G z=gridVector (2*m) f z
  error : ∀ (n : ℕ) (i : GridSource) (z : ℂ),B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z
  rows : ∀ n z,B<z.re →
    fullLeadingMatrix m f ε z *ᵥ gridVector (2*m) f z=E n z+
      ∑ j∈Finset.range n,fullShiftMatrix m f ε j z *ᵥ gridVector (2*m) f (z+((j:ℂ)+1))

/-- No continuation or Taylor-row hypotheses are assumed: both follow
from the original solution at level33. -/
theorem original_pole_system (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧ Nonempty (PoleSystem m f ε) := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  obtain ⟨B,E,_hF,hE,hrow⟩:=initial_system_of_laws m hm hf hε hlaw
  obtain ⟨BG,G,hG,hGF⟩:=grid_continuation_of_laws m hm hf ε hε hlaw
  refine ⟨ε,hε,⟨{
    B := max B BG
    G := G
    E := fun n s i => E i n s
    meromorphic := hG
    agreement := ?_
    error := ?_
    rows := ?_
  }⟩⟩
  · intro z hz
    exact hGF z (lt_of_le_of_lt (le_max_right B BG) hz)
  · intro n i z hz
    apply hE n i z
    linarith [le_max_left B BG]
  · intro n s hs
    have hb : B<s.re:=lt_of_le_of_lt (le_max_left B BG) hs
    rw [fullLeadingMatrix_mulVec]
    simp_rw [fullShiftMatrix_mulVec]
    funext i
    simpa only [Pi.add_apply,Finset.sum_apply] using hrow n s hb i

/-- Every original row persists as a punctured identity wherever its
analytic remainder is defined; this includes arbitrary Taylor orders. -/
theorem PoleSystem.continued_rows {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (n : ℕ) (i : GridSource) (x : ℂ)
    (hx : S.B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j,fullLeadingMatrix m f ε z i j*S.G z j)=ᶠ[𝓝[≠] x]
      (fun z => S.E n z i+∑ a∈Finset.range n,
        ∑ j,fullShiftMatrix m f ε a z i j*S.G (z+((a:ℂ)+1)) j) :=
  QuantitativeArithmeticRectangularContinuation.continued_meromorphic_rows S.B (gridVector (2*m) f) S.G
    (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε) S.E
    (fun i z => (S.meromorphic i z).meromorphicAt) S.agreement
    (fun z i j => fullLeadingMatrix_analytic m f ε i j z)
    (fun n z i j => fullShiftMatrix_analytic m f ε n i j z)
    (fun n i z hz => (S.error n i z hz).meromorphicAt) S.rows n i x hx

#print axioms original_pole_system
#print axioms PoleSystem.continued_rows
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeFirstShiftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix QuantitativeArithmeticUniversalPoleVector

/-- A certified analytic relation among lower-point rows constrains the
same upper principal vector as the leading system. No assumption about
pole orders at the lower point is required. -/
theorem PoleSystem.first_shift {ρ : Type*} {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (L : ℂ→Matrix ρ GridSource ℂ)
    (hL : ∀ x r i,AnalyticAt ℂ (fun z => L z r i) x)
    (hLA : ∀ z,L z*fullLeadingMatrix m f ε z=0)
    (x : ℂ) (v : Fin 66→ℂ) (hv : IsLeadingVector S.G x v)
    (hshift : ∀ n : ℕ,0 < n → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (x+n)) :
    (L (x-1)*fullShiftMatrix m f ε 0 (x-1))*ᵥv=0 := by
  exact hv.first_shift S.B S.G (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε) S.E L
    S.meromorphic (fun n x i j => fullShiftMatrix_analytic m f ε n i j x)
    S.error hL hLA (fun n i x hx => S.continued_rows n i x hx) x v hshift

#print axioms PoleSystem.first_shift
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeSyzygyMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent QuantitativeArithmeticUniversalPoleVector

def sourceIndex (j : ℕ) : GridSource :=
  if h : j<775 then sourceKind ⟨j,h⟩ else .hecke 0

def syzygyMatrix (p : Poly) (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : Matrix (Fin 1) GridSource ℂ :=
  rowMatrix sourceIndex p (parameter 2 m s) (badParameter f 3*parameter 3 m s)
    (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1

theorem scaled_base_physical (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε s : ℂ) (hε : ε=1 ∨ ε= -1) (σ : ℚ)
    (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11)
    (w : Fin 66→ℂ) (j : ℕ) (hj : j<775) :
    eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
      (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
      (fun i => w (gridIndex (i:ℤ))) (baseRows σ j)=
      gridLeadingRows m f ε s w (sourceIndex j) := by
  have hh := baseRows_eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
    (badParameter f 11*parameter 11 m s) (badParameter f 2) σ
    (fun i => w (gridIndex (i:ℤ))) ⟨j,hj⟩
  rw [hσ,← source_sign_covariance _ _ _ _ _ _ _ _
    (badParameter_three_sign hf.toEulerData) (badParameter_eleven_sign hf.toEulerData)] at hh
  rw [physical_source_match m hf ε s hε w] at hh
  simpa only [sourceIndex,dite_eq_left hj] using hh

theorem syzygyMatrix_analytic (p : Poly) (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (s : ℂ) (i : Fin 1) (j : GridSource) :
    AnalyticAt ℂ (fun t => syzygyMatrix p m f t i j) s := by
  have hu : badParameter f 3≠0 := by
    rcases badParameter_three_sign hf.toEulerData with h|h <;> simp [h]
  have hv : badParameter f 11≠0 := by
    rcases badParameter_eleven_sign hf.toEulerData with h|h <;> simp [h]
  exact rowMatrix_analytic sourceIndex p _ _ _ _ _ _ _ s
    (parameter_analytic 2 m (by decide) s)
    (analyticAt_const.mul (parameter_analytic 3 m (by decide) s))
    (analyticAt_const.mul (parameter_analytic 11 m (by decide) s)) analyticAt_const
    (parameter_ne_zero 2 m (by decide) s)
    (mul_ne_zero hu (parameter_ne_zero 3 m (by decide) s))
    (mul_ne_zero hv (parameter_ne_zero 11 m (by decide) s)) (by norm_num) i j

theorem syzygyMatrix_annihilates (p : Poly) (σ : ℚ)
    (hp : ∀ t∈p,t.2.1<775) (hc : substitute (baseRows σ) p=[])
    (m : ℕ) {f : ℕ→ℂ} (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11) (s : ℂ) :
    syzygyMatrix p m f s*fullLeadingMatrix m f ε s=0 := by
  have hu : badParameter f 3≠0 := by
    rcases badParameter_three_sign hf.toEulerData with h|h <;> simp [h]
  have hv : badParameter f 11≠0 := by
    rcases badParameter_eleven_sign hf.toEulerData with h|h <;> simp [h]
  apply rowMatrix_mul_zero
  intro w
  rw [fullLeadingMatrix_mulVec]
  have he := substitution_zero (parameter 2 m s) (badParameter f 3*parameter 3 m s)
    (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
    (fun i => w (gridIndex (i:ℤ))) (parameter_ne_zero 2 m (by decide) s)
    (mul_ne_zero hu (parameter_ne_zero 3 m (by decide) s))
    (mul_ne_zero hv (parameter_ne_zero 11 m (by decide) s)) (by norm_num) (baseRows σ) p hc
  have heq : eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
      (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
      (fun j => eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
        (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
        (fun i => w (gridIndex (i:ℤ))) (baseRows σ j)) p=
      eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
        (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
        (fun j => gridLeadingRows m f ε s w (sourceIndex j)) p := by
    unfold eval
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    exact congrArg (fun q : ℂ => (t.1:ℂ)*QuantitativeArithmeticSevenLaurentRows.monomial
      (parameter 2 m s) (badParameter f 3*parameter 3 m s)
      (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1 t.2.2*q)
      (scaled_base_physical m hf ε s hε σ hσ w t.2.1 (hp t ht))
  exact heq.symm.trans he

#print axioms syzygyMatrix_annihilates
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeCertifiedFirstShiftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent QuantitativeArithmeticUniversalPoleVector

theorem scaled_phase_sign (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    phase m ε*badParameter f 3*badParameter f 11=1 ∨
      phase m ε*badParameter f 3*badParameter f 11= -1 := by
  have he := grid_physical_sign m hε
  have hu := badParameter_three_sign hf.toEulerData
  have hv := badParameter_eleven_sign hf.toEulerData
  change phase m ε=1 ∨ phase m ε= -1 at he
  rcases he with he|he <;> rcases hu with hu|hu <;> rcases hv with hv|hv <;> simp [he,hu,hv]

def selectedOperations (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) : Poly := by
  classical
  exact if phase m ε*badParameter f 3*badParameter f 11=1
    then QuantitativeArithmeticSmallLevelThirtyThreePlusFirstSyzygy.operations
    else QuantitativeArithmeticSmallLevelThirtyThreeMinusFirstSyzygy.operations

theorem selected_annihilator (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1) (s : ℂ) :
    syzygyMatrix (selectedOperations m f ε) m f s*fullLeadingMatrix m f ε s=0 := by
  classical
  by_cases hp : phase m ε*badParameter f 3*badParameter f 11=1
  · rw [selectedOperations,ite_eq_left hp]
    apply syzygyMatrix_annihilates _ 1 _ _ m hf ε hε _ s
    · decide +kernel
    · rw [← substituteCompute_eq]
      exact QuantitativeArithmeticSmallLevelThirtyThreePlusFirstSyzygy.certificate
    · simpa only [Rat.cast_one] using hp.symm
  · rw [selectedOperations,ite_eq_right hp]
    apply syzygyMatrix_annihilates _ (-1) _ _ m hf ε hε _ s
    · decide +kernel
    · rw [← substituteCompute_eq]
      exact QuantitativeArithmeticSmallLevelThirtyThreeMinusFirstSyzygy.certificate
    · simpa only [Rat.cast_neg,Rat.cast_one] using
        ((scaled_phase_sign m hf hε).resolve_left hp).symm

/-- The concrete checked zero-row certificate gives an additional equation
on the original grid's principal vector, for every original sign choice. -/
theorem PoleSystem.certified_first_shift {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε)
    (x : ℂ) (v : Fin 66→ℂ) (hv : IsLeadingVector S.G x v)
    (hshift : ∀ n : ℕ,0 < n → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (x+n)) :
    (syzygyMatrix (selectedOperations m f ε) m f (x-1)*fullShiftMatrix m f ε 0 (x-1))*ᵥv=0 :=
  S.first_shift (syzygyMatrix (selectedOperations m f ε) m f)
    (syzygyMatrix_analytic _ m hf) (selected_annihilator m hf ε hε) x v hv hshift

#print axioms selected_annihilator
#print axioms PoleSystem.certified_first_shift
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeFirstEvaluationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex SmallLevelPrimeRates

theorem first_scalar (μ r d s : ℂ) (m : ℕ) (hr : r≠0) :
    μ*r^((s-1)-(m:ℂ))*(I*d)^1*Ring.choose ((s-1)+1-((2*m:ℕ):ℂ)) 1=
      I*(s-((2*m:ℕ):ℂ))*(μ*r^(s-(m:ℂ))*d/r) := by
  rw [show (s-1)-(m:ℂ)=(s-(m:ℂ))-1 by ring,
    show (s-1)+1-((2*m:ℕ):ℂ)=s-((2*m:ℕ):ℂ) by ring,
    Complex.cpow_sub _ _ hr,Complex.cpow_one]
  simp only [pow_one,Ring.choose_one_right]
  ring

def rowSlope : GridSource→ℚ
  | .word i => groupDerivative i/groupRate i
  | .taylor i => 66/(gridTaylorT i:ℚ)
  | _ => 0

def rowHead (w : Fin 66→ℂ) : GridSource→ℂ
  | .word i => w (groupIndex i)
  | .taylor i => gridSample (gridTaylorQ i) (gridTaylorT i) w
  | _ => 0

theorem matrixScalar_first (m : ℕ) (f : ℕ→ℂ) (η s : ℂ) (i : Fin 588) :
    gridMatrixScalar m f η i 1 (s-1)=
      I*(s-((2*m:ℕ):ℂ))*(groupDerivative i/groupRate i:ℚ)*gridMatrixScalar m f η i 0 s := by
  have hr : (groupRate i:ℂ)≠0 := by exact_mod_cast (group_geometry_real i).2.2.2.2.ne'
  unfold gridMatrixScalar
  simp only [Nat.cast_one,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  rw [first_scalar _ _ _ _ _ hr]
  push_cast
  ring

theorem taylorScalar_first (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 72) :
    gridTaylorCoefficient m f ε i 1 (s-1)=
      I*(s-((2*m:ℕ):ℂ))*(66/(gridTaylorT i:ℚ):ℚ)*gridTaylorCoefficient m f ε i 0 s := by
  have ht : (gridTaylorT i:ℂ)≠0 := by exact_mod_cast (gridTaylorSpecs_valid i).2.2.1
  have hL : (gridTaylorL i:ℂ)≠0 := by
    exact_mod_cast (Nat.lcm_pos (by decide : 0<33) (pow_pos (gridTaylorSpecs_valid i).1 2)).ne'
  have hr : ((gridTaylorL i:ℂ)*((gridTaylorT i:ℂ)/66)^2)≠0 :=
    mul_ne_zero hL (pow_ne_zero _ (div_ne_zero ht (by norm_num)))
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
  simp only [hm,Nat.cast_one,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  push_cast
  rw [show I*(gridTaylorL i:ℂ)*((gridTaylorT i:ℂ)/66)=
    I*((gridTaylorL i:ℂ)*((gridTaylorT i:ℂ)/66)) by ring]
  have he := first_scalar
    (FinitenessNormalizedTwistProduct.root 33 f (gridTaylorQ i)*ε*I^(2*m))
    ((gridTaylorL i:ℂ)*((gridTaylorT i:ℂ)/66)^2)
    ((gridTaylorL i:ℂ)*((gridTaylorT i:ℂ)/66)) s m hr
  push_cast at he
  rw [he]
  field_simp

/-- Retain the common first-Taylor factor, including its zero at s=k. -/
theorem first_shift_from_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (w : Fin 66→ℂ) (i : GridSource) :
    gridShiftRows m f ε 0 (s-1) w i=
      I*(s-((2*m:ℕ):ℂ))*(rowSlope i:ℂ)*(rowHead w i-gridLeadingRows m f ε s w i) := by
  cases i with
  | word i =>
    simp only [gridShiftRows,Nat.zero_add,matrixScalar_first,rowSlope,rowHead,
      gridLeadingRows,gridGroupLeading]
    ring
  | taylor i =>
    simp only [gridShiftRows,Nat.zero_add,taylorScalar_first,rowSlope,rowHead,
      gridLeadingRows,gridRamanujanLeading]
    ring
  | entire i => simp [gridShiftRows,rowSlope]
  | hecke i => simp [gridShiftRows,rowSlope]
  | infinity i => simp [gridShiftRows,rowSlope]

#print axioms first_shift_from_leading
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeFirstDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent
open FinitenessRamanujanSum

def firstIndices : Fin 23→ℕ := ![1,2,7,9,10,12,43,48,53,57,65,66,69,72,668,672,674,686,723,734,741,755,756]
def firstHeadData : ℕ→Poly
  | 1 => [(1,0,(0,0,0,0,0,0,0))]
  | 2 => []
  | 7 => [(1,6,(0,0,0,0,0,0,0))]
  | 9 => [(1,12,(0,0,0,0,0,0,0))]
  | 10 => [(1,22,(0,0,0,0,0,0,0))]
  | 12 => [(1,44,(0,0,0,0,0,0,0))]
  | 43 => [(1,33,(0,0,0,0,0,0,0))]
  | 48 => [(1,30,(0,0,0,0,0,0,0))]
  | 53 => [(1,36,(0,0,0,0,0,0,0))]
  | 57 => [(1,31,(0,0,0,0,0,0,0))]
  | 65 => [(1,54,(0,0,0,0,0,0,0))]
  | 66 => [(1,55,(0,0,0,0,0,0,0))]
  | 69 => [(1,48,(0,0,0,0,0,0,0))]
  | 72 => [(1,52,(0,0,0,0,0,0,0))]
  | 668 => []
  | 672 => [(1,20,(0,0,0,0,0,0,0)),(1,42,(0,0,0,0,0,0,0))]
  | 674 => [(1,18,(0,0,0,0,0,0,0)),(1,40,(0,0,0,0,0,0,0))]
  | 686 => []
  | 723 => []
  | 734 => []
  | 741 => []
  | 755 => []
  | 756 => []
  | _ => []
def firstSlopeData : ℕ→ℚ
  | 1 => (1/1:ℚ)
  | 2 => (0/1:ℚ)
  | 7 => (11/1:ℚ)
  | 9 => (11/2:ℚ)
  | 10 => (3/1:ℚ)
  | 12 => (3/2:ℚ)
  | 43 => (-330/1:ℚ)
  | 48 => (-33/2:ℚ)
  | 53 => (33/1:ℚ)
  | 57 => (-66/1:ℚ)
  | 65 => (-55/1:ℚ)
  | 66 => (-330/1:ℚ)
  | 69 => (-11/1:ℚ)
  | 72 => (-33/1:ℚ)
  | 668 => (0/1:ℚ)
  | 672 => (-33/1:ℚ)
  | 674 => (-33/2:ℚ)
  | 686 => (0/1:ℚ)
  | 723 => (0/1:ℚ)
  | 734 => (0/1:ℚ)
  | 741 => (0/1:ℚ)
  | 755 => (0/1:ℚ)
  | 756 => (0/1:ℚ)
  | _ => 0

def firstRows (σ : ℚ) (j : ℕ) : Poly :=
  normalizeLaurent (shift (firstSlopeData j) (0,0,0,0,0,0,0)
    (firstHeadData j++shift (-1) (0,0,0,0,0,0,0) (baseRows σ j)))
theorem firstSlope_match (i : Fin 23) : firstSlopeData (firstIndices i)=rowSlope (sourceIndex (firstIndices i)) := by
  fin_cases i <;> decide +kernel
theorem firstHead_cached_1 : firstHeadData 1=[(1,0,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_1 (w : Fin 66→ℂ) : rowHead w (sourceIndex 1)=w 0 := rfl
theorem firstHead_eval_1 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 1)=rowHead w (sourceIndex 1) := by
  rw [firstHead_cached_1,firstHead_formal_1]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_2 : firstHeadData 2=[] := rfl
theorem firstHead_formal_2 (w : Fin 66→ℂ) : rowHead w (sourceIndex 2)=0 := rfl
theorem firstHead_eval_2 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 2)=rowHead w (sourceIndex 2) := by
  rw [firstHead_cached_2,firstHead_formal_2]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_7 : firstHeadData 7=[(1,6,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_7 (w : Fin 66→ℂ) : rowHead w (sourceIndex 7)=w 6 := rfl
theorem firstHead_eval_7 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 7)=rowHead w (sourceIndex 7) := by
  rw [firstHead_cached_7,firstHead_formal_7]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_9 : firstHeadData 9=[(1,12,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_9 (w : Fin 66→ℂ) : rowHead w (sourceIndex 9)=w 12 := rfl
theorem firstHead_eval_9 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 9)=rowHead w (sourceIndex 9) := by
  rw [firstHead_cached_9,firstHead_formal_9]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_10 : firstHeadData 10=[(1,22,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_10 (w : Fin 66→ℂ) : rowHead w (sourceIndex 10)=w 22 := rfl
theorem firstHead_eval_10 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 10)=rowHead w (sourceIndex 10) := by
  rw [firstHead_cached_10,firstHead_formal_10]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_12 : firstHeadData 12=[(1,44,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_12 (w : Fin 66→ℂ) : rowHead w (sourceIndex 12)=w 44 := rfl
theorem firstHead_eval_12 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 12)=rowHead w (sourceIndex 12) := by
  rw [firstHead_cached_12,firstHead_formal_12]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_43 : firstHeadData 43=[(1,33,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_43 (w : Fin 66→ℂ) : rowHead w (sourceIndex 43)=w 33 := rfl
theorem firstHead_eval_43 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 43)=rowHead w (sourceIndex 43) := by
  rw [firstHead_cached_43,firstHead_formal_43]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_48 : firstHeadData 48=[(1,30,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_48 (w : Fin 66→ℂ) : rowHead w (sourceIndex 48)=w 30 := rfl
theorem firstHead_eval_48 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 48)=rowHead w (sourceIndex 48) := by
  rw [firstHead_cached_48,firstHead_formal_48]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_53 : firstHeadData 53=[(1,36,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_53 (w : Fin 66→ℂ) : rowHead w (sourceIndex 53)=w 36 := rfl
theorem firstHead_eval_53 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 53)=rowHead w (sourceIndex 53) := by
  rw [firstHead_cached_53,firstHead_formal_53]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_57 : firstHeadData 57=[(1,31,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_57 (w : Fin 66→ℂ) : rowHead w (sourceIndex 57)=w 31 := rfl
theorem firstHead_eval_57 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 57)=rowHead w (sourceIndex 57) := by
  rw [firstHead_cached_57,firstHead_formal_57]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_65 : firstHeadData 65=[(1,54,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_65 (w : Fin 66→ℂ) : rowHead w (sourceIndex 65)=w 54 := rfl
theorem firstHead_eval_65 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 65)=rowHead w (sourceIndex 65) := by
  rw [firstHead_cached_65,firstHead_formal_65]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_66 : firstHeadData 66=[(1,55,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_66 (w : Fin 66→ℂ) : rowHead w (sourceIndex 66)=w 55 := rfl
theorem firstHead_eval_66 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 66)=rowHead w (sourceIndex 66) := by
  rw [firstHead_cached_66,firstHead_formal_66]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_69 : firstHeadData 69=[(1,48,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_69 (w : Fin 66→ℂ) : rowHead w (sourceIndex 69)=w 48 := rfl
theorem firstHead_eval_69 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 69)=rowHead w (sourceIndex 69) := by
  rw [firstHead_cached_69,firstHead_formal_69]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_72 : firstHeadData 72=[(1,52,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_72 (w : Fin 66→ℂ) : rowHead w (sourceIndex 72)=w 52 := rfl
theorem firstHead_eval_72 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 72)=rowHead w (sourceIndex 72) := by
  rw [firstHead_cached_72,firstHead_formal_72]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_668 : firstHeadData 668=[] := rfl
theorem firstHead_formal_668 (w : Fin 66→ℂ) : rowHead w (sourceIndex 668)=0 := rfl
theorem firstHead_eval_668 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 668)=rowHead w (sourceIndex 668) := by
  rw [firstHead_cached_668,firstHead_formal_668]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_672 : firstHeadData 672=[(1,20,(0,0,0,0,0,0,0)),(1,42,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_672 (w : Fin 66→ℂ) : rowHead w (sourceIndex 672)=gridSample 3 (-2) w := rfl
theorem firstHead_eval_672 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 672)=rowHead w (sourceIndex 672) := by
  rw [firstHead_cached_672,firstHead_formal_672]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_674 : firstHeadData 674=[(1,18,(0,0,0,0,0,0,0)),(1,40,(0,0,0,0,0,0,0))] := rfl
theorem firstHead_formal_674 (w : Fin 66→ℂ) : rowHead w (sourceIndex 674)=gridSample 3 (-4) w := rfl
theorem firstHead_eval_674 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 674)=rowHead w (sourceIndex 674) := by
  rw [firstHead_cached_674,firstHead_formal_674]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_686 : firstHeadData 686=[] := rfl
theorem firstHead_formal_686 (w : Fin 66→ℂ) : rowHead w (sourceIndex 686)=0 := rfl
theorem firstHead_eval_686 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 686)=rowHead w (sourceIndex 686) := by
  rw [firstHead_cached_686,firstHead_formal_686]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_723 : firstHeadData 723=[] := rfl
theorem firstHead_formal_723 (w : Fin 66→ℂ) : rowHead w (sourceIndex 723)=0 := rfl
theorem firstHead_eval_723 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 723)=rowHead w (sourceIndex 723) := by
  rw [firstHead_cached_723,firstHead_formal_723]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_734 : firstHeadData 734=[] := rfl
theorem firstHead_formal_734 (w : Fin 66→ℂ) : rowHead w (sourceIndex 734)=0 := rfl
theorem firstHead_eval_734 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 734)=rowHead w (sourceIndex 734) := by
  rw [firstHead_cached_734,firstHead_formal_734]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_741 : firstHeadData 741=[] := rfl
theorem firstHead_formal_741 (w : Fin 66→ℂ) : rowHead w (sourceIndex 741)=0 := rfl
theorem firstHead_eval_741 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 741)=rowHead w (sourceIndex 741) := by
  rw [firstHead_cached_741,firstHead_formal_741]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_755 : firstHeadData 755=[] := rfl
theorem firstHead_formal_755 (w : Fin 66→ℂ) : rowHead w (sourceIndex 755)=0 := rfl
theorem firstHead_eval_755 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 755)=rowHead w (sourceIndex 755) := by
  rw [firstHead_cached_755,firstHead_formal_755]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_cached_756 : firstHeadData 756=[] := rfl
theorem firstHead_formal_756 (w : Fin 66→ℂ) : rowHead w (sourceIndex 756)=0 := rfl
theorem firstHead_eval_756 (x y z a : ℂ) (w : Fin 66→ℂ) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData 756)=rowHead w (sourceIndex 756) := by
  rw [firstHead_cached_756,firstHead_formal_756]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,gridSample,residues,
    Finset.sum_filter,Finset.sum_range_succ,gridIndex]
theorem firstHead_eval (x y z a : ℂ) (w : Fin 66→ℂ) (i : Fin 23) :
    eval x y z 1 a 1 1 (fun n => w (gridIndex (n:ℤ))) (firstHeadData (firstIndices i))=
      rowHead w (sourceIndex (firstIndices i)) := by
  fin_cases i
  · exact firstHead_eval_1 x y z a w
  · exact firstHead_eval_2 x y z a w
  · exact firstHead_eval_7 x y z a w
  · exact firstHead_eval_9 x y z a w
  · exact firstHead_eval_10 x y z a w
  · exact firstHead_eval_12 x y z a w
  · exact firstHead_eval_43 x y z a w
  · exact firstHead_eval_48 x y z a w
  · exact firstHead_eval_53 x y z a w
  · exact firstHead_eval_57 x y z a w
  · exact firstHead_eval_65 x y z a w
  · exact firstHead_eval_66 x y z a w
  · exact firstHead_eval_69 x y z a w
  · exact firstHead_eval_72 x y z a w
  · exact firstHead_eval_668 x y z a w
  · exact firstHead_eval_672 x y z a w
  · exact firstHead_eval_674 x y z a w
  · exact firstHead_eval_686 x y z a w
  · exact firstHead_eval_723 x y z a w
  · exact firstHead_eval_734 x y z a w
  · exact firstHead_eval_741 x y z a w
  · exact firstHead_eval_755 x y z a w
  · exact firstHead_eval_756 x y z a w

#print axioms firstHead_eval
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeFirstPolynomialV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem firstRows_physical (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε s : ℂ) (hε : ε=1 ∨ ε= -1) (σ : ℚ)
    (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11)
    (v : Fin 66→ℂ) (i : Fin 23) :
    eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
      (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
      (fun j => v (gridIndex (j:ℤ))) (firstRows σ (firstIndices i))=
      (rowSlope (sourceIndex (firstIndices i)):ℂ)*
        (rowHead v (sourceIndex (firstIndices i))-gridLeadingRows m f ε s v (sourceIndex (firstIndices i))) := by
  have hx := parameter_ne_zero 2 m (by decide) s
  have hu : badParameter f 3≠0 := by
    rcases badParameter_three_sign hf.toEulerData with h|h <;> simp [h]
  have hv : badParameter f 11≠0 := by
    rcases badParameter_eleven_sign hf.toEulerData with h|h <;> simp [h]
  have hy := mul_ne_zero hu (parameter_ne_zero 3 m (by decide) s)
  have hz := mul_ne_zero hv (parameter_ne_zero 11 m (by decide) s)
  have hi : firstIndices i<775 := by fin_cases i <;> decide
  unfold firstRows
  rw [eval_normalizeLaurent,eval_shift _ _ _ _ _ _ _ _ hx hy hz (by norm_num),eval_append,
    eval_shift _ _ _ _ _ _ _ _ hx hy hz (by norm_num),firstHead_eval,
    scaled_base_physical m hf ε s hε σ hσ v _ hi,firstSlope_match]
  simp only [QuantitativeArithmeticSevenLaurentRows.monomial,zpow_zero,pow_zero,mul_one,
    Rat.cast_neg,Rat.cast_one]
  ring

theorem firstShift_polynomial (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε s : ℂ) (hε : ε=1 ∨ ε= -1) (σ : ℚ)
    (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11)
    (v : Fin 66→ℂ) (i : Fin 23) :
    gridShiftRows m f ε 0 (s-1) v (sourceIndex (firstIndices i))=
      I*(s-((2*m:ℕ):ℂ))*eval (parameter 2 m s)
        (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s)
        1 (badParameter f 2) 1 1 (fun j => v (gridIndex (j:ℤ))) (firstRows σ (firstIndices i)) := by
  rw [firstRows_physical m hf ε s hε σ hσ v i,first_shift_from_leading]
  ring

#print axioms firstShift_polynomial
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeHigherEvaluationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex SmallLevelPrimeRates

def rowDerivative : GridSource→ℚ
  | .word i => groupDerivative i
  | .taylor i => (gridTaylorL i:ℚ)*(gridTaylorT i:ℚ)/66
  | _ => 0

theorem matrixScalar_higher (m : ℕ) (f : ℕ→ℂ) (η s : ℂ) (i : Fin 588) (n : ℕ) :
    gridMatrixScalar m f η i n s=
      I^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
        (groupDerivative i:ℂ)^n*gridMatrixScalar m f η i 0 s := by
  simp only [gridMatrixScalar,Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,mul_pow]
  ring

theorem taylorScalar_higher (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 72) (n : ℕ) :
    gridTaylorCoefficient m f ε i n s=
      I^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
        ((gridTaylorL i:ℂ)*(gridTaylorT i:ℂ)/66)^n*gridTaylorCoefficient m f ε i 0 s := by
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
  simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  push_cast
  rw [show I*(gridTaylorL i:ℂ)*((gridTaylorT i:ℂ)/66)=
      I*((gridTaylorL i:ℂ)*(gridTaylorT i:ℂ)/66) by ring,mul_pow]
  ring

/-- The whole Taylor tail factors into its common archimedean binomial
and a rational derivative power times the original leading-row difference. -/
theorem higher_shift_from_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ)
    (n : ℕ) (w : Fin 66→ℂ) (i : GridSource) :
    gridShiftRows m f ε n s w i=
      I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*
        (rowDerivative i:ℂ)^(n+1)*(rowHead w i-gridLeadingRows m f ε s w i) := by
  cases i with
  | word i =>
    simp only [gridShiftRows,rowDerivative,rowHead,gridLeadingRows,gridGroupLeading]
    rw [matrixScalar_higher m f (ε*I^(2*m)) s i (n+1)]
    ring
  | taylor i =>
    simp only [gridShiftRows,rowDerivative,rowHead,gridLeadingRows,gridRamanujanLeading]
    rw [taylorScalar_higher m f ε s i (n+1)]
    push_cast
    ring
  | entire i => simp [gridShiftRows,rowDerivative]
  | hecke i => simp [gridShiftRows,rowDerivative]
  | infinity i => simp [gridShiftRows,rowDerivative]

#print axioms higher_shift_from_leading
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeJetPolynomialV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent QuantitativeArithmeticUniversalPoleVector

def firstJetPolynomial (σ : ℚ) (p : Poly) : Poly :=
  substitute (firstRows σ) (rescaleThree (1/2) (1/3) (1/11) p)

theorem first_jet_evaluation (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε s : ℂ) (hε : ε=1 ∨ ε= -1) (σ : ℚ)
    (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11)
    (v : Fin 66→ℂ) (p : Poly)
    (hp : ∀ t∈p,∃ i : Fin 23,firstIndices i=t.2.1) :
    ((syzygyMatrix p m f (s-1)*fullShiftMatrix m f ε 0 (s-1))*ᵥv) 0=
      I*(s-((2*m:ℕ):ℂ))*eval (parameter 2 m s)
        (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s)
        1 (badParameter f 2) 1 1 (fun j => v (gridIndex (j:ℤ))) (firstJetPolynomial σ p) := by
  have hu : badParameter f 3≠0 := by
    rcases badParameter_three_sign hf.toEulerData with h|h <;> simp [h]
  have hv : badParameter f 11≠0 := by
    rcases badParameter_eleven_sign hf.toEulerData with h|h <;> simp [h]
  rw [← Matrix.mulVec_mulVec,syzygyMatrix,rowMatrix_mulVec,fullShiftMatrix_mulVec]
  rw [firstJetPolynomial,eval_substitute _ _ _ _ _ _ _ _
    (parameter_ne_zero 2 m (by decide) s)
    (mul_ne_zero hu (parameter_ne_zero 3 m (by decide) s))
    (mul_ne_zero hv (parameter_ne_zero 11 m (by decide) s)) (by norm_num),eval_rescaleThree]
  have h2 := parameter_shift 2 m (by decide) s
  have h3 := parameter_shift 3 m (by decide) s
  have h11 := parameter_shift 11 m (by decide) s
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at *
  rw [show (1/2:ℂ)*parameter 2 m s=parameter 2 m (s-1) by rw [h2]; ring,
    show (1/3:ℂ)*(badParameter f 3*parameter 3 m s)=badParameter f 3*parameter 3 m (s-1) by rw [h3]; ring,
    show (1/11:ℂ)*(badParameter f 11*parameter 11 m s)=badParameter f 11*parameter 11 m (s-1) by rw [h11]; ring,
    ← eval_smul]
  unfold eval
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  obtain ⟨i,hi⟩ := hp t ht
  exact congrArg (fun q : ℂ => (t.1:ℂ)*QuantitativeArithmeticSevenLaurentRows.monomial
    (parameter 2 m (s-1)) (badParameter f 3*parameter 3 m (s-1))
    (badParameter f 11*parameter 11 m (s-1)) 1 (badParameter f 2) 1 1 t.2.2*q)
    (by simpa only [hi,eval] using firstShift_polynomial m hf ε s hε σ hσ v i)

theorem selected_support (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) :
    ∀ t∈selectedOperations m f ε,∃ i : Fin 23,firstIndices i=t.2.1 := by
  classical
  unfold selectedOperations
  split <;> decide +kernel

/-- An equation on the actual principal vector, with the weight zero explicitly
excluded only when cancelling the Taylor prefactor. -/
theorem PoleSystem.first_jet_polynomial {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε)
    (s : ℂ) (v : Fin 66→ℂ) (hv : IsLeadingVector S.G s v)
    (hshift : ∀ n : ℕ,0 < n → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (s+n))
    (σ : ℚ) (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11)
    (hs : s≠((2*m:ℕ):ℂ)) :
    eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
      (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
      (fun j => v (gridIndex (j:ℤ))) (firstJetPolynomial σ (selectedOperations m f ε))=0 := by
  have h := congrFun (S.certified_first_shift hf hε s v hv hshift) 0
  rw [first_jet_evaluation m hf ε s hε σ hσ v _ (selected_support m f ε)] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero I_ne_zero (sub_ne_zero.mpr hs))

#print axioms first_jet_evaluation
#print axioms PoleSystem.first_jet_polynomial
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftModelV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates SmallLevelFiniteShift
open SmallLevelTwentyOneKnownWords (jetScale jetScale_binomial jetScale_ne_zero)

def jetLead (n : Fin 4) (w : Fin 66→ℂ) : GridSource→ℂ :=
  laurentRows (2/2^n.val) (3/3^n.val) (11/11^n.val) (-1) (-5/2) 1 (-1) w

def jetSlice (w : Fin 264→ℂ) (n : Fin 4) (j : Fin 66) : ℂ := w (finProdFinEquiv (n,j))

/-- Four layers of the exceptional pole system after removing the common
falling factorials. Its coefficients are all rational. -/
def jetBlockRow (n : Fin 4) (r : GridSource) (w : Fin 264→ℂ) : ℂ :=
  jetLead n (jetSlice w n) r-
    ∑ a∈Finset.range n.val, (1/((a+1).factorial:ℂ))*(rowDerivative r:ℂ)^(a+1)*
      (rowHead (jetSlice w (lowerIndex n a)) r-jetLead n (jetSlice w (lowerIndex n a)) r)

def scaledJetStack (m : ℕ) (w : Fin 264→ℂ) (b : Fin 4×Fin 66) : ℂ :=
  jetScale (1-(m:ℂ)) b.1*w (finProdFinEquiv b)

theorem parameter_candidate_lower (p m n : ℕ) (hp : p≠0) :
    parameter p m ((m:ℂ)+1-(n:ℂ))=(p:ℂ)/(p:ℂ)^n := by
  unfold parameter
  rw [show (m:ℂ)+1-(n:ℂ)-(m:ℂ)=1-(n:ℂ) by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one,Complex.cpow_natCast]

theorem physical_jetLead (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hE : phase m ε= -1)
    (hu : badParameter f 3=1) (hv : badParameter f 11= -1)
    (ha : badParameter f 2= -5/2) (n : Fin 4) (w : Fin 66→ℂ) (r : GridSource) :
    gridLeadingRows m f ε ((m:ℂ)+1-(n.val:ℂ)) w r=jetLead n w r := by
  rw [leadingRows_laurent m hf ε _ hε]
  simp only [parameter_candidate_lower 2 m n.val (by decide),
    parameter_candidate_lower 3 m n.val (by decide),
    parameter_candidate_lower 11 m n.val (by decide),hE,hu,hv,ha,Nat.cast_ofNat,jetLead]

theorem leading_rows_scale (m : ℕ) (f : ℕ→ℂ) (ε s c : ℂ) (w : Fin 66→ℂ) (r : GridSource) :
    gridLeadingRows m f ε s (fun j => c*w j) r=c*gridLeadingRows m f ε s w r := by
  exact congrFun ((leadingLinearMap m f ε s).map_smul c w) r

theorem shift_rows_scale (m : ℕ) (f : ℕ→ℂ) (ε s c : ℂ) (n : ℕ)
    (w : Fin 66→ℂ) (r : GridSource) :
    gridShiftRows m f ε n s (fun j => c*w j) r=c*gridShiftRows m f ε n s w r := by
  exact congrFun ((shiftLinearMap m f ε n s).map_smul c w) r

theorem actual_jetBlockRow (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hE : phase m ε= -1)
    (hu : badParameter f 3=1) (hv : badParameter f 11= -1)
    (ha : badParameter f 2= -5/2) (n : Fin 4) (r : GridSource) (w : Fin 264→ℂ) :
    (∑ b,blockLeading 3 (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε)
      ((m:ℂ)+1) (n,r) b*scaledJetStack m w b)=
        jetScale (1-(m:ℂ)) n*jetBlockRow n r w := by
  rw [blockLeading_apply]
  change (fullLeadingMatrix m f ε ((m:ℂ)+1-n.val)*ᵥ
      (fun j => scaledJetStack m w (n,j))) r-
    ∑ a∈Finset.range n.val,(fullShiftMatrix m f ε a ((m:ℂ)+1-n.val)*ᵥ
      (fun j => scaledJetStack m w (lowerIndex n a,j))) r= _
  simp only [fullLeadingMatrix_mulVec,fullShiftMatrix_mulVec,scaledJetStack,
    leading_rows_scale,shift_rows_scale]
  rw [physical_jetLead m hf ε hε hE hu hv ha]
  unfold jetBlockRow jetSlice
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha'
  rw [higher_shift_from_leading,physical_jetLead m hf ε hε hE hu hv ha]
  have he : (m:ℂ)+1-(n.val:ℂ)+((a+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=
      (1-(m:ℂ))-(n.val:ℂ)+((a+1:ℕ):ℂ) := by push_cast; ring
  rw [he]
  have hc := jetScale_binomial (1-(m:ℂ)) n a (Finset.mem_range.mp ha')
  linear_combination (rowDerivative r:ℂ)^(a+1)*
    (rowHead (fun j => w (finProdFinEquiv (lowerIndex n a,j))) r-
      jetLead n (fun j => w (finProdFinEquiv (lowerIndex n a,j))) r)*hc

#print axioms actual_jetBlockRow
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end
