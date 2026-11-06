module

public import QuantitativeArithmeticRectangularContinuationTheoryV4
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxAugmentedSystemV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridRowSourcesV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxGridSourceRowV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSparseGaugeV1
public import QuantitativeArithmeticSmallLevelTwentyFiveAuxSymbolicRowsV1
public import QuantitativeArithmeticSmallLevelTwentyFiveSelectedWordsTheoryV4
public import QuantitativeArithmeticUniversalPoleAllowedFirstShiftV1
public import QuantitativeArithmeticUniversalPoleBlockRowsV1
public import QuantitativeArithmeticUniversalPoleRegularBlockRowsV1
public import SmallLevelAllowedSimplePoleTailV1
public import SmallLevelUniversalPoleFirstShiftV1

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxFirstJetRowsV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSevenLaurentRows

/-- Polynomial row at s-1, with x,y,z,w denoting prime powers at s. -/
def lowerPoly (p : Poly) : Poly := p.map fun t =>
  (t.1 / ((2:ℚ)^t.2.2.1*(3:ℚ)^t.2.2.2.1*(5:ℚ)^t.2.2.2.2.1*(7:ℚ)^t.2.2.2.2.2.1),t.2.1,t.2.2)

/-- First Taylor shift at s-1 with its common factor I*(s-k) removed. -/
def rawFirstJetPoly (χ : ℚ) : SourceRow → Poly
  | .physical (.word r) => shift (χ^r.count*r.slope/r.rate)
      (primeExponent r.powers) (gridPoly r.target)
  | .physical (.taylor r) => shift (χ*r.slope/r.rate)
      (primeExponent r.powers) (samplePoly r.q r.target)
  | _ => []

end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxFirstJetEvaluationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData

theorem first_jet_scalar (μ r d s : ℂ) (m : ℕ) (hr : r≠0) :
    μ*r^((s-1)-(m:ℂ))*(I*d)^1*
      Ring.choose ((s-1)+(1:ℂ)-((2*m:ℕ):ℂ)) 1=
      I*(s-((2*m:ℕ):ℂ))*(μ*d/r*r^(s-(m:ℂ))) := by
  have he : (s-1)-(m:ℂ)=(s-(m:ℂ))-1 := by ring
  have hs : (s-1)+(1:ℂ)-((2*m:ℕ):ℂ)=s-((2*m:ℕ):ℂ) := by ring
  rw [he,hs,Complex.cpow_sub _ _ hr,Complex.cpow_one]
  simp only [pow_one,Ring.choose_one_right]
  ring

/-- Exact first-shift polynomial evaluation on the physical exponential
curve. The common I*(s-k) factor is retained, including at s=k. -/
theorem eval_rawFirstJetPoly (r : SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε s : ℂ) (χ : ℚ) (hχ : ε*I^(2*m)=(χ:ℂ)) (v : Fin 1050 → ℂ) :
    sourceShifted r m f ε 0 (s-1) v=
      I*(s-((2*m:ℕ):ℂ))*eval
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s)
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
        (periodicVector v) (rawFirstJetPoly χ r) := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p m s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  cases r with
  | old j => simp [sourceShifted,rawFirstJetPoly]
  | physical r =>
    cases r with
    | word r =>
      have hr : r.rate≠0 := by rw [r.powers_eq]; positivity
      have hrc : (r.rate:ℂ)≠0 := by exact_mod_cast hr
      simp only [sourceShifted,shifted,Nat.zero_add,QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.coefficient,rawFirstJetPoly,Nat.cast_one]
      rw [first_jet_scalar _ _ _ _ _ hrc,
        eval_shift _ _ _ _ _ _ _ _ (hp 2 (by decide)) (hp 3 (by decide))
          (hp 5 (by decide)) (hp 7 (by decide)),eval_gridPoly]
      simp only [monomial,primeExponent,pow_zero,mul_one,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,hχ]
      have he := rational_four_prime_power r.rate r.powers r.powers_eq (s-(m:ℂ))
      change (r.rate:ℂ)^(s-(m:ℂ))=fourPrimeMonomial r.powers
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) at he
      rw [he]
      simp only [fourPrimeMonomial]
      ring
    | taylor r =>
      have hr : r.rate≠0 := by rw [r.powers_eq]; positivity
      have hrc : (r.rate:ℂ)≠0 := by exact_mod_cast hr
      simp only [sourceShifted,shifted,Nat.zero_add,rawFirstJetPoly]
      rw [taylorCoefficient_rational m f ε r.divides,r.rate_eq,r.slope_eq]
      simp only [Nat.cast_one]
      rw [first_jet_scalar _ _ _ _ _ hrc,
        eval_shift _ _ _ _ _ _ _ _ (hp 2 (by decide)) (hp 3 (by decide))
          (hp 5 (by decide)) (hp 7 (by decide)),eval_samplePoly]
      simp only [monomial,primeExponent,pow_zero,mul_one,Rat.cast_div,Rat.cast_mul,
        QuantitativeArithmeticSmallLevelTwentyFive.GridSystem.phaseRoot,hχ]
      have he := rational_four_prime_power r.rate r.powers r.powers_eq (s-(m:ℂ))
      change (r.rate:ℂ)^(s-(m:ℂ))=fourPrimeMonomial r.powers
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) at he
      rw [he]
      simp only [fourPrimeMonomial]
      ring
    | entire q hq hd => simp [sourceShifted,shifted,rawFirstJetPoly]
    | hecke p hp hd j => simp [sourceShifted,shifted,rawFirstJetPoly]
    | infinity w j hn hd => simp [sourceShifted,shifted,rawFirstJetPoly]

#print axioms first_jet_scalar
#print axioms eval_rawFirstJetPoly
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxHigherJetV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticSmallLevelTwentyFiveAuxGridData

/-- Taylor row with its common binomial and power of I removed. -/
def rawHigherJetPoly (χ : ℚ) (n : ℕ) : SourceRow → Poly
  | .physical (.word r) => shift (χ^r.count*r.slope^n)
      (primeExponent r.powers) (gridPoly r.target)
  | .physical (.taylor r) => shift (χ*r.slope^n)
      (primeExponent r.powers) (samplePoly r.q r.target)
  | _ => []

theorem eval_rawHigherJetPoly (r : SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε s : ℂ) (χ : ℚ) (hχ : ε*I^(2*m)=(χ:ℂ)) (a : ℕ) (v : Fin 1050 → ℂ) :
    sourceShifted r m f ε a s v=
      (I^(a+1)*Ring.choose (s+((a+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (a+1))*eval
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s)
        ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) ((Real.sqrt 7:ℂ)*f 7)
        (periodicVector v) (rawHigherJetPoly χ (a+1) r) := by
  have hp (p : ℕ) (hp : p≠0) : primeParameter p m s≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp))
  cases r with
  | old j => simp [sourceShifted,rawHigherJetPoly]
  | physical r =>
    cases r with
    | word r =>
      simp only [sourceShifted,shifted,QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid.coefficient,rawHigherJetPoly]
      rw [eval_shift _ _ _ _ _ _ _ _ (hp 2 (by decide)) (hp 3 (by decide))
          (hp 5 (by decide)) (hp 7 (by decide)),eval_gridPoly]
      simp only [monomial,primeExponent,pow_zero,mul_one,Rat.cast_mul,Rat.cast_pow,hχ]
      have he := rational_four_prime_power r.rate r.powers r.powers_eq (s-(m:ℂ))
      change (r.rate:ℂ)^(s-(m:ℂ))=fourPrimeMonomial r.powers
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) at he
      rw [he]
      simp only [fourPrimeMonomial,mul_pow]
      ring
    | taylor r =>
      simp only [sourceShifted,shifted,rawHigherJetPoly]
      rw [taylorCoefficient_rational m f ε r.divides,r.rate_eq,r.slope_eq,
        eval_shift _ _ _ _ _ _ _ _ (hp 2 (by decide)) (hp 3 (by decide))
          (hp 5 (by decide)) (hp 7 (by decide)),eval_samplePoly]
      simp only [monomial,primeExponent,pow_zero,mul_one,Rat.cast_mul,Rat.cast_pow,
        QuantitativeArithmeticSmallLevelTwentyFive.GridSystem.phaseRoot,hχ]
      have he := rational_four_prime_power r.rate r.powers r.powers_eq (s-(m:ℂ))
      change (r.rate:ℂ)^(s-(m:ℂ))=fourPrimeMonomial r.powers
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) at he
      rw [he]
      simp only [fourPrimeMonomial,mul_pow]
      ring
    | entire q hq hd => simp [sourceShifted,shifted,rawHigherJetPoly]
    | hecke p hp hd j => simp [sourceShifted,shifted,rawHigherJetPoly]
    | infinity w j hn hd => simp [sourceShifted,shifted,rawHigherJetPoly]

#print axioms eval_rawHigherJetPoly
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAllowedTailV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix Filter SmallLevelFiniteShift
open scoped Topology

theorem sourceShifted_zero_at_weight (r : SourceRow) (m : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (χ : ℚ) (hχ : ε*I^(2*m)=(χ:ℂ)) (n : ℕ) (s : ℂ)
    (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (v : Fin 1050 → ℂ) :
    sourceShifted r m f ε n s v=0 := by
  rw [eval_rawHigherJetPoly r m f ε s χ hχ]
  have he : s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using sub_eq_zero.mpr hs
  rw [he,Ring.choose_zero_succ,mul_zero,zero_mul]

theorem augmentedShift_zero_at_weight {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    (rows : ρ → SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (χ : ℚ)
    (hχ : ε*I^(2*m)=(χ:ℂ)) (n : ℕ) (s : ℂ)
    (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (i : ρ ⊕ κ) (j : Fin 1050) :
    augmentedShiftMatrix (κ := κ) rows m f ε n s i j=0 := by
  change augmentedShifted rows m f ε n s (Pi.single j 1) i=0
  cases i with
  | inl i => exact sourceShifted_zero_at_weight (rows i) m f ε χ hχ n s hs _
  | inr i => simp [augmentedShifted]

/-- Positive Taylor sources cancel any permitted simple pole at the weight.
The upper translated points need only be regular away from that point. -/
theorem augmented_allowed_tail {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    (rows : ρ → SourceRow) (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (χ : ℚ)
    (hχ : ε*I^(2*m)=(χ:ℂ))
    (G : ℂ → Fin 1050 → ℂ) (hG : ∀ j z, MeromorphicNFAt (fun s => G s j) z)
    (x : ℂ) (d : ℕ)
    (hshift : ∀ n : ℕ, 0<n → x+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (hk : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ))
    (a : ℕ) (ha : d≤a) (i : ρ ⊕ κ) (j : Fin 1050) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => augmentedShiftMatrix rows m f ε a z i j*G (z+((a:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R := by
  classical
  exact allowed_simple_pole_tail (augmentedShiftMatrix (κ := κ) rows m f ε) ((2*m:ℕ):ℂ)
    (augmentedShiftMatrix_analytic rows m f ε)
    (augmentedShift_zero_at_weight rows m f ε χ hχ) G hG x d hshift hk a ha i j

#print axioms sourceShifted_zero_at_weight
#print axioms augmentedShift_zero_at_weight
#print axioms augmented_allowed_tail
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxOldGridV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

/-- The original 150-grid is an exact subgrid of the auxiliary 1050-grid. -/
theorem old_grid_embedding (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (j : Fin 150) :
    gridVector 1050 k f s ⟨7*j.val,by omega⟩=
      QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector k f s j := by
  unfold gridVector QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector grid
  congr 1
  push_cast
  ring

end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxSourceRemaindersV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Set SmallLevelAdditive
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

/-- Physical rows have analytic remainders. Old-grid coordinate rows use only
the already proved meromorphic continuation of that smaller grid. -/
theorem original_source_remainders {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 150 → ℂ)
    (hG : ∀ j z, MeromorphicAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=
      QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z)
    (r : SourceRow) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ℂ),
      (∀ (M : ℕ) s, B-((M:ℝ)+1)<s.re → MeromorphicAt (H M) s) ∧
      ∀ (M : ℕ) s, B<s.re →
        sourceLeading r m f ε s (gridVector 1050 (2*m) f s)=H M s+
          ∑ n∈Finset.range M, sourceShifted r m f ε n s
            (gridVector 1050 (2*m) f (s+((n:ℂ)+1))) := by
  cases r with
  | physical r =>
    obtain ⟨B,H,hH,hrow⟩ := original_row_sources hm hf ε hε hlaw r
    exact ⟨B,H,fun M s hs => (hH M s hs).meromorphicAt,hrow⟩
  | old j =>
    refine ⟨BG,fun _ s => G s j,fun _ s _ => hG j s,?_⟩
    intro M s hs
    simp only [sourceLeading,sourceShifted,Finset.sum_const_zero,add_zero,
      old_grid_embedding,hGF s hs]

/-- A finite collection of source rows admits one common initial half-plane. -/
theorem original_source_family {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 150 → ℂ)
    (hG : ∀ j z, MeromorphicAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=
      QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z)
    (rows : ρ → SourceRow) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ρ → ℂ),
      (∀ j z, B<z.re → AnalyticAt ℂ (fun s => gridVector 1050 (2*m) f s j) z) ∧
      (∀ (M : ℕ) i s, B-((M:ℝ)+1)<s.re → MeromorphicAt (fun z => H M z i) s) ∧
      ∀ (M : ℕ) i s, B<s.re →
        sourceLeading (rows i) m f ε s (gridVector 1050 (2*m) f s)=H M s i+
          ∑ n∈Finset.range M, sourceShifted (rows i) m f ε n s
            (gridVector 1050 (2*m) f (s+((n:ℂ)+1))) := by
  classical
  choose B H hH hrow using fun i => original_source_remainders hm hf ε hε hlaw BG G hG hGF (rows i)
  obtain ⟨BF,hF⟩ := original_common_halfplane hf
  let B0 : ℝ := max BF (Finset.univ.sup' Finset.univ_nonempty B)
  have hb (i : ρ) : B i≤B0 := le_trans
    (Finset.le_sup' B (Finset.mem_univ i)) (le_max_right _ _)
  refine ⟨B0,fun M s i => H i M s,?_,?_,?_⟩
  · intro j z hz
    exact (hF ((j.val:ℝ)/1050) z (lt_of_le_of_lt (le_max_left _ _) hz)).1
  · intro M i s hs
    exact hH i M s (by have := hb i; linarith)
  · intro M i s hs
    exact hrow i M s (lt_of_le_of_lt (hb i) hs)

#print axioms original_source_remainders
#print axioms original_source_family
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxQuotientContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

/-- Relative continuation on the augmented grid. All certificate hypotheses
are finite polynomial identities or finite-dimensional linear algebra; no
continuation of the discarded free coordinates is assumed. -/
theorem quotient_continuation_of_certificates
    (rows : Fin 4600 → SourceRow) (free : Fin 68 → Fin 1050) (basis : ℕ → Poly)
    (source tail : Fin 4600 → Poly) (χ : ℚ)
    (hperiodic : ∀ j, basis (j%1050)=basis j)
    (hfree : ∀ j, basis (free j).val=unitPoly j.val)
    (hold : ∀ j : Fin 150, basis (7*j.val)=[])
    (hsource : ∀ i, normalizedPoly (rawSourcePoly χ (rows i))=source i)
    (htail : ∀ i, normalizedPoly (rawTailPoly (rows i))=tail i)
    (hszero : ∀ i, substitute basis (source i)=[])
    (htzero : ∀ i, substitute basis (tail i)=[])
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(χ:ℂ))
    (hkernel : ∀ s : ℂ, ∀ v : Fin 1050 → ℂ,
      (∀ i, sourceLeading (rows i) m f ε s v=0) →
      (∀ j, v (free j)=0) → v=0)
    (BG : ℝ) (G0 : ℂ → Fin 150 → ℂ)
    (hG0 : ∀ j z, MeromorphicAt (fun w => G0 w j) z)
    (hG0F : ∀ z, BG<z.re → G0 z=
      QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z) :
    ∃ (B : ℝ) (G : ℂ → Fin 1050 → ℂ),
      (∀ j z, MeromorphicNFAt (fun w => G w j) z) ∧
      (∀ z, B<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z)) ∧
      ∀ z, B<z.re → ∀ j : Fin 150, G z ⟨7*j.val,by omega⟩=
        QuantitativeArithmeticSmallLevelTwentyFive.SelectedWords.gridVector (2*m) f z j := by
  classical
  obtain ⟨B,H,hF,hH,hrow⟩ := original_source_family hm hf ε hε hlaw BG G0 hG0 hG0F rows
  let F := gridVector 1050 (2*m) f
  let FG := fun s => physicalGauge basis free m f s (F s)
  let A := augmentedMatrix rows free m f ε
  let C := augmentedShiftMatrix (κ := Fin 68) rows m f ε
  let HH := fun M s => Sum.elim (H M s) (fun _ : Fin 68 => (0:ℂ))
  have hFG (j : Fin 1050) (z : ℂ) (hz : B<z.re) :
      AnalyticAt ℂ (fun w => FG w j) z :=
    physicalGauge_analytic basis free m f z F (fun i => hF i z hz) j
  have hker : ∃ s : ℂ, ∀ v : Fin 1050 → ℂ, A s *ᵥ v=0 → v=0 := by
    refine ⟨0,?_⟩
    intro v hv
    rw [augmentedMatrix_mulVec] at hv
    apply hkernel 0 v
    · intro i
      exact congrFun hv (Sum.inl i)
    · intro j
      exact congrFun hv (Sum.inr j)
  have hHH (M : ℕ) (i : Fin 4600 ⊕ Fin 68) (z : ℂ)
      (hz : B-((M:ℝ)+1)<z.re) : MeromorphicAt (fun w => HH M w i) z := by
    cases i with
    | inl i => exact hH M i z hz
    | inr j => exact analyticAt_const.meromorphicAt
  have hsystem (M : ℕ) (s : ℂ) (hs : B<s.re) :
      A s *ᵥ FG s=HH M s+∑ n∈Finset.range M, C n s *ᵥ FG (s+((n:ℂ)+1)) := by
    simp only [A,C,augmentedMatrix_mulVec,augmentedShiftMatrix_mulVec]
    funext i
    cases i with
    | inl i =>
      simp only [augmentedLeading,augmentedShifted,Sum.elim_inl,Pi.add_apply,
        Finset.sum_apply,HH,FG,F]
      rw [physicalGauge_leading basis hperiodic free (rows i) hf ε s χ hχ _
        (source i) (hsource i) (hszero i)]
      have hshift (n : ℕ) := physicalGauge_shifted basis hperiodic free (rows i) m f ε
        n s (s+((n:ℂ)+1)) (gridVector 1050 (2*m) f (s+((n:ℂ)+1)))
        (tail i) (htail i) (htzero i)
      simp_rw [hshift]
      exact hrow M i s hs
    | inr j =>
      simp only [augmentedLeading,augmentedShifted,Sum.elim_inr,Pi.add_apply,
        Finset.sum_apply,HH,FG,physicalGauge,sparseGauge_free basis free hfree,
        Finset.sum_const_zero,add_zero]
  obtain ⟨G,hG,hGF⟩ := QuantitativeArithmeticRectangularContinuation.meromorphic_continuation
    B FG A C HH hFG (augmentedMatrix_analytic rows free m f ε)
    hker (augmentedShiftMatrix_analytic rows m f ε) hHH hsystem
  refine ⟨B,G,hG,hGF,?_⟩
  intro s hs j
  rw [hGF s hs]
  change sparseGauge basis free _ _ _ _ _ _ _ (F s) ⟨7*j.val,by omega⟩=_
  rw [sparseGauge_old basis free hold]
  exact old_grid_embedding (2*m) f s j

#print axioms quotient_continuation_of_certificates
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxContinuedRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix Filter Set QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open scoped Topology

/-- Every certified physical row survives continuation of the quotient. Its
remainder is analytic, even though the old-grid source in the reconstruction
system is only meromorphic. -/
theorem physical_row_continues (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hperiodic : ∀ j, basis (j%1050)=basis j)
    (r : Row) (χ : ℚ) (p q : Poly)
    (hp : normalizedPoly (rawSourcePoly χ (.physical r))=p)
    (hq : normalizedPoly (rawTailPoly (.physical r))=q)
    (hpzero : substitute basis p=[]) (hqzero : substitute basis q=[])
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(χ:ℂ)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z)) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ℂ),
      (∀ (M : ℕ) s, B-((M:ℝ)+1)<s.re → AnalyticAt ℂ (H M) s) ∧
      ∀ (M : ℕ) x, B-((M:ℝ)+1)<x.re →
        (fun z => leading r m f ε z (G z))=ᶠ[𝓝[≠] x]
          (fun z => H M z+∑ n∈Finset.range M,
            shifted r m f ε n z (G (z+((n:ℂ)+1)))) := by
  obtain ⟨BR,H,hH,hrow⟩ := original_row_sources hm hf ε hε hlaw r
  let B : ℝ := max BG BR
  let rows : Unit → SourceRow := fun _ => .physical r
  let frees : Empty → Fin 1050 := Empty.elim
  let A := augmentedMatrix rows frees m f ε
  let C := augmentedShiftMatrix (κ := Empty) rows m f ε
  have hlead (s : ℂ) (v : Fin 1050 → ℂ) :
      ∑ j, A s (Sum.inl ()) j*v j=leading r m f ε s v := by
    exact congrFun (augmentedMatrix_mulVec rows frees m f ε s v) (Sum.inl ())
  have hshift (n : ℕ) (s : ℂ) (v : Fin 1050 → ℂ) :
      ∑ j, C n s (Sum.inl ()) j*v j=shifted r m f ε n s v := by
    exact congrFun (augmentedShiftMatrix_mulVec (κ := Empty) rows m f ε n s v) (Sum.inl ())
  refine ⟨B,H,?_,?_⟩
  · intro M s hs
    apply hH M s
    have hb : BR≤B := le_max_right _ _
    linarith
  · intro M x hx
    apply SmallLevelContinuation.halfplane_germ_identity (B-((M:ℝ)+1)) B _ _ _ x hx
    · intro z _
      have hh := MeromorphicAt.fun_sum (fun j (_ : j∈Finset.univ) =>
        (augmentedMatrix_analytic rows frees m f ε z (Sum.inl ()) j).meromorphicAt.mul (hG j z))
      simpa only [A,Pi.mul_apply,hlead] using hh
    · intro z hz
      change B-((M:ℝ)+1)<z.re at hz
      have hHz : AnalyticAt ℂ (H M) z := hH M z (by
        have hb : BR≤B := le_max_right _ _
        linarith)
      apply hHz.meromorphicAt.add
      apply MeromorphicAt.fun_sum
      intro n _
      have hh := MeromorphicAt.fun_sum (fun j (_ : j∈Finset.univ) =>
        (augmentedShiftMatrix_analytic (κ := Empty) rows m f ε n z (Sum.inl ()) j).meromorphicAt.mul
          ((hG j (z+((n:ℂ)+1))).comp_analyticAt (g := fun w : ℂ => w+((n:ℂ)+1)) (by fun_prop)))
      simpa only [C,Pi.mul_apply,Function.comp_apply,hshift] using hh
    · intro s hs
      dsimp only
      change B<s.re at hs
      rw [hGF s (lt_of_le_of_lt (le_max_left _ _) hs)]
      have hl := physicalGauge_leading basis hperiodic free (.physical r) hf ε s χ hχ
        (gridVector 1050 (2*m) f s) p hp hpzero
      change leading r m f ε s (physicalGauge basis free m f s (gridVector 1050 (2*m) f s))=
        leading r m f ε s (gridVector 1050 (2*m) f s) at hl
      rw [hl,hrow M s (lt_of_le_of_lt (le_max_right _ _) hs)]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      have hn : BG<(s+((n:ℂ)+1)).re := by
        have hb : BG≤B := le_max_left _ _
        simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      rw [hGF _ hn]
      exact (physicalGauge_shifted basis hperiodic free (.physical r) m f ε n s
        (s+((n:ℂ)+1)) (gridVector 1050 (2*m) f (s+((n:ℂ)+1))) q hq hqzero).symm

/-- Old coordinates retain the original continuation as punctured germs;
this is enough to lift any old-grid pole to the auxiliary quotient. -/
theorem old_coordinate_germ (BG : ℝ) (G : ℂ → Fin 1050 → ℂ) (G0 : ℂ → Fin 150 → ℂ)
    (hG : ∀ j z, MeromorphicAt (fun w => G w j) z)
    (hG0 : ∀ j z, MeromorphicAt (fun w => G0 w j) z)
    (hinitial : ∀ z, BG<z.re → ∀ j : Fin 150, G z ⟨7*j.val,by omega⟩=G0 z j)
    (j : Fin 150) (x : ℂ) :
    (fun z => G z ⟨7*j.val,by omega⟩)=ᶠ[𝓝[≠] x] (fun z => G0 z j) := by
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) BG
    (fun z _ => hG _ z) (fun z _ => hG0 _ z) (fun z hz => hinitial z hz j) x
  linarith

#print axioms physical_row_continues
#print axioms old_coordinate_germ
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxFirstJetScalingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

theorem eval_lowerPoly (x y z w a b c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval x y z w a b c v (lowerPoly p)=eval (x/2) (y/3) (z/5) (w/7) a b c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [lowerPoly,List.map_cons,eval_cons] at *
    rw [ih]
    congr 1
    simp only [monomial,Rat.cast_div,Rat.cast_mul,Rat.cast_zpow,Rat.cast_ofNat,div_zpow]
    ring

theorem primeParameter_sub_one (p m : ℕ) (hp : p≠0) (s : ℂ) :
    primeParameter p m (s-1)=primeParameter p m s/(p:ℂ) := by
  have he : (s-1)-(m:ℂ)=(s-(m:ℂ))-1 := by ring
  simp only [primeParameter,he]
  rw [Complex.cpow_sub _ _ (by exact_mod_cast hp : (p:ℂ)≠0),Complex.cpow_one]

theorem eval_lowerPoly_physical (p : Poly) (m : ℕ) (s a b c : ℂ) (v : ℕ → ℂ) :
    eval (primeParameter 2 m s) (primeParameter 3 m s)
      (primeParameter 5 m s) (primeParameter 7 m s) a b c v (lowerPoly p)=
    eval (primeParameter 2 m (s-1)) (primeParameter 3 m (s-1))
      (primeParameter 5 m (s-1)) (primeParameter 7 m (s-1)) a b c v p := by
  rw [eval_lowerPoly]
  simp only [primeParameter_sub_one 2 m (by decide),primeParameter_sub_one 3 m (by decide),
    primeParameter_sub_one 5 m (by decide),primeParameter_sub_one 7 m (by decide),Nat.cast_ofNat]

#print axioms eval_lowerPoly
#print axioms primeParameter_sub_one
#print axioms eval_lowerPoly_physical
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxGaugePoleV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Filter Set QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector SmallLevelFiniteShift
open scoped Topology

/-- The discarded free coordinates stay zero after normal-form continuation,
including at poles. This follows from initial agreement, not a new gauge
assumption on the continued family. -/
theorem continued_free_zero (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hfree : ∀ j, basis (free j).val=unitPoly j.val)
    (m : ℕ) (f : ℕ → ℂ) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z)) :
    ∀ z j, G z (free j)=0 := by
  intro x j
  have he : (fun z => G z (free j))=ᶠ[𝓝[≠] x] (fun _ => (0:ℂ)) := by
    apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) BG
      (fun z _ => (hG (free j) z).meromorphicAt)
      (fun _ _ => analyticAt_const.meromorphicAt) _ x (by linarith)
    intro z hz
    change G z (free j)=0
    rw [hGF z hz]
    exact sparseGauge_free basis free hfree _ _ _ _ _ _ _ _ j
  exact (((hG (free j) x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    analyticAt_const.meromorphicNFAt).mp he).eq_of_nhds

/-- Every principal vector of a finite stack retains all the gauge zeros. -/
theorem stack_free_zero (free : Fin 68 → Fin 1050) (G : ℂ → Fin 1050 → ℂ)
    (hfree : ∀ z j, G z (free j)=0) (d : ℕ) (s : ℂ)
    (v : Fin (d+1) × Fin 1050 → ℂ) (hv : IsLeadingVector (stackGrid d G) s v) :
    ∀ n j, v (n,free j)=0 := by
  classical
  intro n j
  have h := hv.2 (fun _ b => if b=(n,free j) then 1 else 0) (fun _ => 0)
    (fun _ => analyticAt_const) analyticAt_const (by
      filter_upwards [] with z
      simp [stackGrid,hfree])
  simpa using h

#print axioms continued_free_zero
#print axioms stack_free_zero
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxSelectedFirstShiftV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix Filter Set QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- A finite family of certified physical rows has a common analytic
remainder domain after continuation of the auxiliary quotient. -/
theorem selected_physical_germs {ι : Type*} [Fintype ι] [Nonempty ι]
    (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hperiodic : ∀ j, basis (j%1050)=basis j)
    (rows : ι → Row) (χ : ℚ) (p q : ι → Poly)
    (hp : ∀ i, normalizedPoly (rawSourcePoly χ (.physical (rows i)))=p i)
    (hq : ∀ i, normalizedPoly (rawTailPoly (.physical (rows i)))=q i)
    (hpzero : ∀ i, substitute basis (p i)=[]) (hqzero : ∀ i, substitute basis (q i)=[])
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(χ:ℂ)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z)) :
    ∃ (B : ℝ) (H : ℕ → ℂ → ι → ℂ),
      (∀ (M : ℕ) i s, B-((M:ℝ)+1)<s.re → AnalyticAt ℂ (fun z => H M z i) s) ∧
      ∀ (M : ℕ) i x, B-((M:ℝ)+1)<x.re →
        (fun z => leading (rows i) m f ε z (G z))=ᶠ[𝓝[≠] x]
          (fun z => H M z i+∑ n∈Finset.range M,
            shifted (rows i) m f ε n z (G (z+((n:ℂ)+1)))) := by
  classical
  choose bs Hs hHs hrs using fun i => physical_row_continues basis free hperiodic
    (rows i) χ (p i) (q i) (hp i) (hq i) (hpzero i) (hqzero i)
    hm hf ε hε hlaw hχ BG G hG hGF
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty bs
  have hb (i : ι) : bs i≤B := Finset.le_sup' bs (Finset.mem_univ i)
  refine ⟨B,(fun M z i => Hs i M z),?_,?_⟩
  · intro M i s hs
    apply hHs i M s
    linarith [hb i]
  · intro M i s hs
    apply hrs i M s
    linarith [hb i]

/-- Weil--Taylor first-shift syzygies for the actual continued auxiliary
quotient. No pole-order comparison with the lower point is assumed. -/
theorem selected_first_shift {ι : Type*} [Fintype ι] [Nonempty ι]
    (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hperiodic : ∀ j, basis (j%1050)=basis j)
    (rows : ι → Row) (χ : ℚ) (p q : ι → Poly)
    (hp : ∀ i, normalizedPoly (rawSourcePoly χ (.physical (rows i)))=p i)
    (hq : ∀ i, normalizedPoly (rawTailPoly (.physical (rows i)))=q i)
    (hpzero : ∀ i, substitute basis (p i)=[]) (hqzero : ∀ i, substitute basis (q i)=[])
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(χ:ℂ)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z))
    (x : ℂ) (v : Fin 1050 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (K : ℂ → ι → ℂ)
    (hK : ∀ z i, AnalyticAt ℂ (fun w => K w i) z)
    (hKA : ∀ z (w : Fin 1050 → ℂ), ∑ i, K z i*leading (rows i) m f ε z w=0) :
    ∑ i, K (x-1) i*shifted (rows i) m f ε 0 (x-1) v=0 := by
  classical
  obtain ⟨B,H,hH,hrow⟩ := selected_physical_germs basis free hperiodic rows χ p q
    hp hq hpzero hqzero hm hf ε hε hlaw hχ BG G (fun i z => (hG i z).meromorphicAt) hGF
  let frees : Empty → Fin 1050 := Empty.elim
  let sources : ι → SourceRow := fun i => .physical (rows i)
  let A : ℂ → Matrix ι (Fin 1050) ℂ := fun z i => augmentedMatrix sources frees m f ε z (Sum.inl i)
  let C : ℕ → ℂ → Matrix ι (Fin 1050) ℂ := fun n z i =>
    augmentedShiftMatrix (κ := Empty) sources m f ε n z (Sum.inl i)
  let L : ℂ → Matrix Unit ι ℂ := fun z _ i => K z i
  have ha (z : ℂ) (w : Fin 1050 → ℂ) (i : ι) :
      (∑ j, A z i j*w j)=leading (rows i) m f ε z w := by
    exact congrFun (augmentedMatrix_mulVec sources frees m f ε z w) (Sum.inl i)
  have hc (n : ℕ) (z : ℂ) (w : Fin 1050 → ℂ) (i : ι) :
      (∑ j, C n z i j*w j)=shifted (rows i) m f ε n z w := by
    exact congrFun (augmentedShiftMatrix_mulVec (κ := Empty) sources m f ε n z w) (Sum.inl i)
  have hLA (z : ℂ) : L z*A z=0 := by
    ext r j
    have hh := hKA z (Pi.single j 1)
    simp_rw [← ha z (Pi.single j 1)] at hh
    simpa [Matrix.mul_apply,L,Pi.single_apply] using hh
  have h := IsLeadingVector.first_shift B G A C H L hG
    (fun n z i j => augmentedShiftMatrix_analytic (κ := Empty) sources m f ε n z (Sum.inl i) j)
    hH (fun z _ i => hK z i) hLA (by
      intro n i z hz
      simpa only [ha,hc] using hrow n i z hz) x v hv hshift
  have hh : (L (x-1) *ᵥ (C 0 (x-1) *ᵥ v)) ()=0 := by
    rw [Matrix.mulVec_mulVec]
    exact congrFun h ()
  change (∑ i, K (x-1) i*(∑ j, C 0 (x-1) i j*v j))=0 at hh
  simpa only [hc] using hh

#print axioms selected_physical_germs
#print axioms selected_first_shift
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxLeadingPoleV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix Filter Set QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- Any certified physical row annihilates the universal leading vector at
an active pole. External old-grid sources are deliberately not included. -/
theorem physical_leading_pole (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hperiodic : ∀ j, basis (j%1050)=basis j)
    (r : Row) (χ : ℚ) (p q : Poly)
    (hp : normalizedPoly (rawSourcePoly χ (.physical r))=p)
    (hq : normalizedPoly (rawTailPoly (.physical r))=q)
    (hpzero : substitute basis p=[]) (hqzero : substitute basis q=[])
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(χ:ℂ)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z))
    (x : ℂ) (v : Fin 1050 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n)) :
    leading r m f ε x v=0 := by
  obtain ⟨B,H,hH,hrow⟩ := physical_row_continues basis free hperiodic r χ p q
    hp hq hpzero hqzero hm hf ε hε hlaw hχ BG G (fun i z => (hG i z).meromorphicAt) hGF
  let rows : Unit → SourceRow := fun _ => .physical r
  let frees : Empty → Fin 1050 := Empty.elim
  let A : ℂ → Fin 1050 → ℂ := fun z => augmentedMatrix rows frees m f ε z (Sum.inl ())
  let C : ℕ → ℂ → Fin 1050 → ℂ := fun n z =>
    augmentedShiftMatrix (κ := Empty) rows m f ε n z (Sum.inl ())
  have ha (z : ℂ) (w : Fin 1050 → ℂ) : (∑ j, A z j*w j)=leading r m f ε z w :=
    congrFun (augmentedMatrix_mulVec rows frees m f ε z w) (Sum.inl ())
  have hc (n : ℕ) (z : ℂ) (w : Fin 1050 → ℂ) : (∑ j, C n z j*w j)=shifted r m f ε n z w :=
    congrFun (augmentedShiftMatrix_mulVec (κ := Empty) rows m f ε n z w) (Sum.inl ())
  rw [← ha x v]
  apply hv.taylor hG hshift B A C H
    (fun j => augmentedMatrix_analytic rows frees m f ε x (Sum.inl ()) j)
    (fun n j => augmentedShiftMatrix_analytic (κ := Empty) rows m f ε n x (Sum.inl ()) j) hH
  intro n hn
  simpa only [ha,hc] using hrow n x hn

#print axioms physical_leading_pole
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxSelectedFirstShiftAllowedV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix Filter Set QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem selected_first_shift_allowed {ι : Type*} [Fintype ι] [Nonempty ι]
    (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hperiodic : ∀ j, basis (j%1050)=basis j)
    (rows : ι → Row) (χ : ℚ) (p q : ι → Poly)
    (hp : ∀ i, normalizedPoly (rawSourcePoly χ (.physical (rows i)))=p i)
    (hq : ∀ i, normalizedPoly (rawTailPoly (.physical (rows i)))=q i)
    (hpzero : ∀ i, substitute basis (p i)=[]) (hqzero : ∀ i, substitute basis (q i)=[])
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(χ:ℂ)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z))
    (x : ℂ) (v : Fin 1050 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → (x+n)≠((2*m:ℕ):ℂ) → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (hweight : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ))
    (K : ℂ → ι → ℂ)
    (hK : ∀ z i, AnalyticAt ℂ (fun w => K w i) z)
    (hKA : ∀ z (w : Fin 1050 → ℂ), ∑ i, K z i*leading (rows i) m f ε z w=0) :
    ∑ i, K (x-1) i*shifted (rows i) m f ε 0 (x-1) v=0 := by
  classical
  obtain ⟨B,H,hH,hrow⟩ := selected_physical_germs basis free hperiodic rows χ p q
    hp hq hpzero hqzero hm hf ε hε hlaw hχ BG G (fun i z => (hG i z).meromorphicAt) hGF
  let frees : Empty → Fin 1050 := Empty.elim
  let sources : ι → SourceRow := fun i => .physical (rows i)
  let A : ℂ → Matrix ι (Fin 1050) ℂ := fun z i => augmentedMatrix sources frees m f ε z (Sum.inl i)
  let C : ℕ → ℂ → Matrix ι (Fin 1050) ℂ := fun n z i =>
    augmentedShiftMatrix (κ := Empty) sources m f ε n z (Sum.inl i)
  let L : ℂ → Matrix Unit ι ℂ := fun z _ i => K z i
  have ha (z : ℂ) (w : Fin 1050 → ℂ) (i : ι) :
      (∑ j, A z i j*w j)=leading (rows i) m f ε z w := by
    exact congrFun (augmentedMatrix_mulVec sources frees m f ε z w) (Sum.inl i)
  have hc (n : ℕ) (z : ℂ) (w : Fin 1050 → ℂ) (i : ι) :
      (∑ j, C n z i j*w j)=shifted (rows i) m f ε n z w := by
    exact congrFun (augmentedShiftMatrix_mulVec (κ := Empty) sources m f ε n z w) (Sum.inl i)
  have hLA (z : ℂ) : L z*A z=0 := by
    ext r j
    have hh := hKA z (Pi.single j 1)
    simp_rw [← ha z (Pi.single j 1)] at hh
    simpa [Matrix.mul_apply,L,Pi.single_apply] using hh
  have h := IsLeadingVector.allowed_first_shift B G A C H L hG
    (fun n z i j => augmentedShiftMatrix_analytic (κ := Empty) sources m f ε n z (Sum.inl i) j)
    hH (fun z _ i => hK z i) hLA (by
      intro n i z hz
      simpa only [ha,hc] using hrow n i z hz) x ((2*m:ℕ):ℂ) v hv hshift hweight
    (fun n z hz i j => augmentedShift_zero_at_weight (κ := Empty) sources m f ε χ hχ n z hz (Sum.inl i) j)
  have hh : (L (x-1) *ᵥ (C 0 (x-1) *ᵥ v)) ()=0 := by
    rw [Matrix.mulVec_mulVec]
    exact congrFun h ()
  change (∑ i, K (x-1) i*(∑ j, C 0 (x-1) i j*v j))=0 at hh
  simpa only [hc] using hh


#print axioms selected_first_shift_allowed
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveAuxLeadingPoleAllowedV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex Matrix Filter Set QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem physical_leading_pole_allowed (basis : ℕ → Poly) (free : Fin 68 → Fin 1050)
    (hperiodic : ∀ j, basis (j%1050)=basis j)
    (r : Row) (χ : ℚ) (p q : Poly)
    (hp : normalizedPoly (rawSourcePoly χ (.physical r))=p)
    (hq : normalizedPoly (rawTailPoly (.physical r))=q)
    (hpzero : substitute basis p=[]) (hqzero : substitute basis q=[])
    {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 25 (2*m) f)
    (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 25 (2*m) f ε)
    (hχ : ε*I^(2*m)=(χ:ℂ)) (BG : ℝ) (G : ℂ → Fin 1050 → ℂ)
    (hG : ∀ j z, MeromorphicNFAt (fun w => G w j) z)
    (hGF : ∀ z, BG<z.re → G z=physicalGauge basis free m f z (gridVector 1050 (2*m) f z))
    (x : ℂ) (v : Fin 1050 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → (x+n)≠((2*m:ℕ):ℂ) → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (hweight : ∀ j, (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z j) ((2*m:ℕ):ℂ)) :
    leading r m f ε x v=0 := by
  obtain ⟨B,H,hH,hrow⟩ := physical_row_continues basis free hperiodic r χ p q
    hp hq hpzero hqzero hm hf ε hε hlaw hχ BG G (fun i z => (hG i z).meromorphicAt) hGF
  let rows : Unit → SourceRow := fun _ => .physical r
  let frees : Empty → Fin 1050 := Empty.elim
  let A : ℂ → Fin 1050 → ℂ := fun z => augmentedMatrix rows frees m f ε z (Sum.inl ())
  let C : ℕ → ℂ → Fin 1050 → ℂ := fun n z =>
    augmentedShiftMatrix (κ := Empty) rows m f ε n z (Sum.inl ())
  have ha (z : ℂ) (w : Fin 1050 → ℂ) : (∑ j, A z j*w j)=leading r m f ε z w :=
    congrFun (augmentedMatrix_mulVec rows frees m f ε z w) (Sum.inl ())
  have hc (n : ℕ) (z : ℂ) (w : Fin 1050 → ℂ) : (∑ j, C n z j*w j)=shifted r m f ε n z w :=
    congrFun (augmentedShiftMatrix_mulVec (κ := Empty) rows m f ε n z w) (Sum.inl ())
  obtain ⟨R,hR,he⟩ := SmallLevelFiniteShift.continued_regular_tail B G
    (fun z _ => A z) (fun n z _ => C n z) (fun n z _ => H n z) x 0
    (fun n (_ : Unit) z hz => hH n z hz)
    (fun a ha (_ : Unit) j => by
      simpa only [Nat.cast_zero,sub_zero] using
        (augmented_allowed_tail (κ := Empty) rows m f ε χ hχ G hG x 0 hshift hweight
          a ha (Sum.inl ()) j)) (by
      intro n (_ : Unit) z hz
      simpa only [ha,hc] using hrow n z hz)
  rw [← ha x v]
  apply hv.2 A (fun z => R z ())
    (fun j => augmentedMatrix_analytic rows frees m f ε x (Sum.inl ()) j) (hR ())
  simpa only [Finset.range_zero,Finset.sum_empty,add_zero] using he ()

#print axioms physical_leading_pole_allowed
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveExceptionalSpecializeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelTwentyFiveFiniteGrid

/-- Specialize the exceptional branch, retaining the arbitrary parameter at 7. -/
def exceptionalCoefficient (n : ℕ) (e : Exponent) : ℚ :=
  ((2:ℚ)/2^n)^e.1*((3:ℚ)/3^n)^e.2.1*((5:ℚ)/5^n)^e.2.2.1*
    ((7:ℚ)/7^n)^e.2.2.2.1*(-1/2:ℚ)^e.2.2.2.2.1*(-7/3:ℚ)^e.2.2.2.2.2.1

def exceptionalPoly (n : ℕ) (p : Poly) : Poly := p.map fun t =>
  (t.1*exceptionalCoefficient n t.2.2,t.2.1,(0,0,0,0,0,0,t.2.2.2.2.2.2.2.2))

theorem exceptionalPoly_eval (n : ℕ) (c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval 1 1 1 1 0 0 c v (exceptionalPoly n p)=
      eval ((2:ℂ)/2^n) ((3:ℂ)/3^n) ((5:ℂ)/5^n) ((7:ℂ)/7^n) (-1/2) (-7/3) c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [exceptionalPoly] at ih
    simp only [exceptionalPoly,List.map_cons,eval_cons]
    rw [ih]
    simp only [exceptionalCoefficient,
      Rat.cast_mul,Rat.cast_zpow,Rat.cast_pow,Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat,
      Rat.cast_one,monomial,zpow_zero,pow_zero,one_mul,mul_one]
    ring

theorem primeParameter_exceptional (p m n : ℕ) (hp : p≠0) :
    primeParameter p m ((m:ℂ)+1-(n:ℂ))=(p:ℂ)/(p:ℂ)^n := by
  unfold primeParameter
  rw [show (m:ℂ)+1-(n:ℂ)-(m:ℂ)=1-(n:ℂ) by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one,Complex.cpow_natCast]

/-- Normalized higher shifts on the exceptional branch, with the common
falling-factorial scalar removed. No inverse of a Hecke eigenvalue occurs. -/
def exceptionalShift (χ : ℚ) (n a : ℕ) : SourceRow → Poly
  | .physical (.word r) => shift (χ^r.count*(r.rate/r.rate^n)*r.slope^(a+1)/(a+1).factorial)
      (0,0,0,0,0,0,0) (gridPoly r.target)
  | .physical (.taylor r) => shift (χ*(r.rate/r.rate^n)*r.slope^(a+1)/(a+1).factorial)
      (0,0,0,0,0,0,0) (samplePoly r.q r.target)
  | _ => []

#print axioms exceptionalPoly_eval
#print axioms primeParameter_exceptional
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFiveExceptionalBlockModelV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open QuantitativeArithmeticSevenLaurentRows

def blockMovePoly (n : ℕ) (p : Poly) : Poly :=
  p.map fun t => (t.1,1050*n+t.2.1,t.2.2)

def cuspBlockLift (p : Poly) : Poly :=
  p.map fun t => (t.1,1050*(t.2.1/150)+7*(t.2.1%150),t.2.2)

def exceptionalBlockPoly (χ : ℚ) (n : ℕ) (r : SourceRow) : Poly :=
  blockMovePoly n (exceptionalPoly n (rawSourcePoly χ r)) ++
    (List.range n).flatMap (fun a => shift (-1) (0,0,0,0,0,0,0)
      (blockMovePoly (n-1-a) (exceptionalShift χ n a r)))

end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentyFivePlusExceptionalSpecializeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
open Complex QuantitativeArithmeticSevenLaurentRows

/-- Positive-sign exceptional parameters; the parameter at seven is retained. -/
def plusExceptionalCoefficient (n : ℕ) (e : Exponent) : ℚ :=
  ((2:ℚ)/2^n)^e.1*((3:ℚ)/3^n)^e.2.1*((5:ℚ)/5^n)^e.2.2.1*
    ((7:ℚ)/7^n)^e.2.2.2.1*(-3:ℚ)^e.2.2.2.2.1*(-4:ℚ)^e.2.2.2.2.2.1

def plusExceptionalPoly (n : ℕ) (p : Poly) : Poly := p.map fun t =>
  (t.1*plusExceptionalCoefficient n t.2.2,t.2.1,(0,0,0,0,0,0,t.2.2.2.2.2.2.2.2))

theorem plusExceptionalPoly_eval (n : ℕ) (c : ℂ) (v : ℕ → ℂ) (p : Poly) :
    eval 1 1 1 1 0 0 c v (plusExceptionalPoly n p)=
      eval ((2:ℂ)/2^n) ((3:ℂ)/3^n) ((5:ℂ)/5^n) ((7:ℂ)/7^n) (-3) (-4) c v p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [plusExceptionalPoly] at ih
    simp only [plusExceptionalPoly,List.map_cons,eval_cons]
    rw [ih]
    simp only [plusExceptionalCoefficient,
      Rat.cast_mul,Rat.cast_zpow,Rat.cast_pow,Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat,
      monomial,zpow_zero,pow_zero,one_mul,mul_one]
    ring

def plusExceptionalBlockPoly (n : ℕ) (r : SourceRow) : Poly :=
  blockMovePoly n (plusExceptionalPoly n (rawSourcePoly 1 r)) ++
    (List.range n).flatMap (fun a => shift (-1/((a+1).factorial:ℚ)) (0,0,0,0,0,0,0)
      (blockMovePoly (n-1-a) (plusExceptionalPoly n (rawHigherJetPoly 1 (a+1) r))))

#print axioms plusExceptionalPoly_eval
end QuantitativeArithmeticSmallLevelTwentyFiveAuxGridModel
end
end
