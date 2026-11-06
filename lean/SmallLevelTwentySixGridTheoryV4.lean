module

public import QuantitativeArithmeticAnalyticGermTheoryV4
public import QuantitativeArithmeticSmallLevelTwentySixMMPOriginalPoleExclusionV1
public import SmallLevelContinuedMeromorphicSourcesV1
public import SmallLevelContinuedRegularShiftedV1
public import SmallLevelPoleGridTheoryV4
public import SmallLevelRegularPoleTailV1
public import SmallLevelTwentySixGridContinuationV1
public import SmallLevelTwentySixGridFullMatricesV1
public import SmallLevelTwentySixGridLaurentRowsV1
public import SmallLevelTwentySixGridPoleSystemV1
public import SmallLevelTwentySixGridSignScalingV1
public import SmallLevelTwentySixOddTheoryV4
public import SmallLevelTwentySixGermDAGTheoryV4
public import SmallLevelTwentySixTheoryV4
public import SmallLevelTwentySixUnitMMMBatchedTheoryV4
public import SmallLevelTwentySixUnitMMPBatchedTheoryV4

/-! Consolidated chapter: SmallLevelTwentySixGrid. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixEndpointContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex SmallLevelTwentySixUnitMMM SmallLevelAdditive

/-- The additive transform used in the boundary endgame is one of the
coordinates of the unconditional original continuation. -/
theorem actualGrid_endpoint (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    actualGrid m f s 71=original (2*m) f (2/13) s := by
  change grid (2*m) f 780 (120:ℤ) s=original (2*m) f (2/13) s
  norm_num [grid]

theorem original_endpoint_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ B : ℝ,∃ A : ℂ→ℂ,(∀ x,MeromorphicNFAt A x) ∧
      ∀ s,B<s.re → A s=original (2*m) f (2/13) s := by
  obtain ⟨B,G,hG,hGF⟩:=original_grid_continuation m hm hf
  refine ⟨B,fun s => G s 71,fun x => hG 71 x,?_⟩
  intro s hs
  change G s 71=original (2*m) f (2/13) s
  rw [hGF s hs,actualGrid_endpoint]

#print axioms original_endpoint_continuation
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridAnalyticEndgameV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 7000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex SmallLevelTwentySixUnitMMM SmallLevelAdditive

theorem actualGrid_third_plus (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    actualGrid m f s 102=original (2*m) f (1/3) s := by
  change grid (2*m) f 780 (260:ℤ) s=original (2*m) f (1/3) s
  norm_num [grid]

theorem actualGrid_third_minus (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    actualGrid m f s 219=original (2*m) f (-1/3) s := by
  change grid (2*m) f 780 (520:ℤ) s=original (2*m) f (-1/3) s
  have h:=transform_add_int (FinitenessOriginalFourier.fullCoefficients f (2*m)) (-1/3) 1 s
  convert h using 1 <;> norm_num [grid,original]

/-- Once the actual continued grid is regular, the original solution is
modular. This isolates the analytic/group conclusion from pole exclusion. -/
theorem PoleSystem.modular_of_nonnegative_orders {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (hregular : ∀ x j,0≤meromorphicOrderAt (fun z => S.G z j) x) :
    SmallLevelOriginal.IsModular 26 (2*m) f := by
  have ha (j : Fin 320) (s : ℂ) : AnalyticAt ℂ (fun z => S.G z j) s :=
    (S.meromorphic j s).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hregular s j)
  have hP:=SmallLevelTwentySix.original_P_of_regular_endpoint m hm hf
    (fun s => S.G s 71) S.B (fun s => (S.meromorphic 71 s).meromorphicAt) (ha 71 0)
    (by
      intro s hs
      rw [S.agreement s hs,actualGrid_endpoint])
  apply SmallLevelTwentySixOdd.modular_of_P_and_entire_third m hm hf hP
    (fun s => S.G s 102-S.G s 219) S.B
  · intro s
    exact ((ha 102 s).sub (ha 219 s)).differentiableAt
  · intro s hs
    rw [S.agreement s hs,actualGrid_third_plus,actualGrid_third_minus]
    norm_num only [SmallLevelTwentySixOdd.odd,Nat.cast_ofNat]

#print axioms actualGrid_third_plus
#print axioms actualGrid_third_minus
#print axioms PoleSystem.modular_of_nonnegative_orders
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridBatchedIntegerRankV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix

/-- All eight original sign choices at every positive integer exponent. -/
theorem original_full_leading_kernel_integer_batched (m n : ℕ) (hn : 1≤n) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    ∀ w : Fin 320→ℂ,fullLeadingMatrix m f ε ((m+n:ℕ):ℂ) *ᵥ w=0 → w=0 := by
  have hη : phase m ε=1 ∨ phase m ε= -1 := grid_physical_sign m hε
  have h₂:=badParameter_two_sign hf.toEulerData
  have h₁₃:=badParameter_thirteen_sign hf.toEulerData
  rcases hη with hη|hη <;> rcases h₂ with h₂|h₂ <;> rcases h₁₃ with h₁₃|h₁₃
  · exact SmallLevelTwentySixUnitMMPBatched.full_leading_kernel_integer m n f ε
      (-1) (1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer m n f ε
      (-1) (1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer m n f ε
      (1) (-1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMPBatched.full_leading_kernel_integer m n f ε
      (1) (-1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer m n f ε
      (-1) (-1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMPBatched.full_leading_kernel_integer m n f ε
      (-1) (-1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMPBatched.full_leading_kernel_integer m n f ε
      (1) (1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)
  · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer m n f ε
      (1) (1) (by norm_num) (by norm_num) hn
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₃)

#print axioms original_full_leading_kernel_integer_batched
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridLeadingPoleV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix QuantitativeArithmeticUniversalPoleVector

/-- At a rightmost pole, every original leading row annihilates the
nonzero leading Laurent vector. Lower shifted poles are not discarded. -/
theorem PoleSystem.rightmost_leading_kernel {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ) (v : Fin 320→ℂ)
    (hv : IsLeadingVector S.G x v)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n)) :
    fullLeadingMatrix m f ε x *ᵥ v=0 := by
  funext i
  exact hv.taylor_at S.meromorphic hshift S.B
    (fun z j => fullLeadingMatrix m f ε z i j)
    (fun n z j => fullShiftMatrix m f ε n z i j) (fun n z => S.E n z i)
    (fun j => fullLeadingMatrix_analytic m f ε i j x)
    (fun n j => fullShiftMatrix_analytic m f ε n i j x)
    (fun n hn => S.error n i x hn)
    (fun n hn => S.continued_rows n i x hn)

#print axioms PoleSystem.rightmost_leading_kernel
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridLowerGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Filter Matrix SmallLevelFiniteShift QuantitativeArithmeticAnalyticGerm
open scoped Topology

/-- Every lower Taylor layer gives an identity modulo analytic germs at
the selected point. This retains arbitrary pole orders at all lower layers. -/
theorem PoleSystem.lower_taylor_germs {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (d : ℕ) (i : GridSource) :
    HasAnalyticGerm (fun z => (∑ j,fullLeadingMatrix m f ε (z-d) i j*S.G (z-d) j)-
      ∑ a∈Finset.range d,∑ j,fullShiftMatrix m f ε a (z-d) i j*
        S.G (z-((d-1-a:ℕ):ℂ)) j) x := by
  obtain ⟨R,hR,he⟩:=continued_regular_shifted_source S.B S.G
    (fullLeadingMatrix m f ε) (fullShiftMatrix m f ε) S.E x d S.error
    (fun a ha i j => regular_pole_tail (fullShiftMatrix m f ε)
      (fun n z i j => fullShiftMatrix_analytic m f ε n i j z)
      S.G S.meromorphic x d hshift a ha i j)
    (fun n i y hy => S.continued_rows n i y hy)
  exact ⟨fun z => R z i,hR i,he i⟩

#print axioms PoleSystem.lower_taylor_germs
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridTaylorFactorsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex SmallLevelPrimeRates SmallLevelFourPrimeRates

def taylorDerivative (i : Fin 71) : ℚ := (gridTaylorL i:ℚ)*(gridTaylorT i:ℚ)/780

theorem matrixScalar_factor (m : ℕ) (f : ℕ→ℂ) (η : ℂ) (i : Fin 235) (n : ℕ) (s : ℂ) :
    gridMatrixScalar m f η i n s=
      (gridWordSign (-badParameter f 2) η (sourceWord (gridGroupSource i))*
        SmallLevelFourPrimeRates.monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 13 m s) (parameter 5 m s))*
      I^n*(gridGroupDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  rw [gridMatrixScalar,root_two,groupRate_complex,mul_pow]
  norm_num only [parameter,Nat.cast_ofNat]
  ring

theorem taylorScalar_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 71) (n : ℕ) (s : ℂ) :
    gridTaylorCoefficient m f ε i n s=
      (FinitenessNormalizedTwistProduct.root 26 f (gridTaylorQ i)*phase m ε*
        SmallLevelFourPrimeRates.monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s)
          (parameter 13 m s) (parameter 5 m s))*
      I^n*(taylorDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hc : gridTaylorCoefficient m f ε i n s=
      gridTaylorCoefficient m f ε i 0 s*
        I^n*(taylorDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
    unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar taylorDerivative
    simp only [pow_zero,Ring.choose_zero_right,mul_one,Rat.cast_div,Rat.cast_mul,
      Rat.cast_natCast,Rat.cast_intCast,Rat.cast_ofNat,Complex.ofReal_div,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_ofNat,mul_pow,div_pow]
    ring
  rw [hc,taylorScalar_leading]

#print axioms matrixScalar_factor
#print axioms taylorScalar_factor
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridShiftSignScalingV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex SmallLevelPrimeRates

def laurentShiftRows (m n : ℕ) (s X Y Z W η σ₂ σ₁₃ : ℂ) (w : Fin 780→ℂ) : GridSource→ℂ
  | .word i => (gridWordSign (-σ₂) η (sourceWord (gridGroupSource i))*
      SmallLevelFourPrimeRates.monomial (groupPowers i) X Y Z W)*
      I^(n+1)*(gridGroupDerivative i:ℂ)^(n+1)*
      Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*w (gridGroupTarget i)
  | .taylor i => (((if 2∣gridTaylorQ i then -σ₂ else 1)*
      (if 13∣gridTaylorQ i then -σ₁₃ else 1))*η*
      SmallLevelFourPrimeRates.monomial (taylorPowers i) X Y Z W)*
      I^(n+1)*(taylorDerivative i:ℂ)^(n+1)*
      Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*
      gridSample (gridTaylorQ i) (gridTaylorPartner i) w
  | .entire _ => 0
  | .hecke _ => 0
  | .infinity _ => 0

theorem shiftRows_laurent (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 780→ℂ) (i : GridSource) :
    gridShiftRows m f ε n s w i=
      laurentShiftRows m n s (parameter 2 m s) (parameter 3 m s) (parameter 13 m s)
        (parameter 5 m s) (phase m ε) (badParameter f 2) (badParameter f 13) w i := by
  cases i <;>
    simp only [gridShiftRows,laurentShiftRows,matrixScalar_factor,taylorScalar_factor,
      grid_ramanujan_root,phase]

/-- Sign rescaling transports every positive Taylor order as well as
the leading system, so it preserves the full lower-germ equations. -/
theorem laurentShiftRows_sign_scale (m n : ℕ) (s X Y Z W c u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (w : Fin 780→ℂ) (i : GridSource) :
    laurentShiftRows m n s (u*X) Y (v*Z) W (-1) (-1) c w i=
      laurentShiftRows m n s X Y Z W (-u*v) (-u) (c*v) w i := by
  cases i with
  | word i =>
    simp only [laurentShiftRows,neg_neg,monomial_scale]
    rw [←word_scale_sign i u v hu hv]
    ring
  | taylor i =>
    simp only [laurentShiftRows,neg_neg,ite_self,one_mul,monomial_scale]
    rw [←taylor_scale_sign i c u v hu hv]
    ring
  | entire i => rfl
  | hecke i => rfl
  | infinity i => rfl

#print axioms shiftRows_laurent
#print axioms laurentShiftRows_sign_scale
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridSlopeMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix SmallLevelPrimeRates SmallLevelFiniteGridSupport SmallLevelTwentySixUnitMMM

/-- The rational-slope part of a Taylor source, before its common binomial factor. -/
def slopeRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 780→ℂ) : GridSource→ℂ
  | .word i => (gridWordSign (-badParameter f 2) (phase m ε)
      (sourceWord (gridGroupSource i))*
      SmallLevelFourPrimeRates.monomial (groupPowers i) (parameter 2 m s)
        (parameter 3 m s) (parameter 13 m s) (parameter 5 m s))*
      (gridGroupDerivative i:ℂ)^n*w (gridGroupTarget i)
  | .taylor i => (FinitenessNormalizedTwistProduct.root 26 f (gridTaylorQ i)*phase m ε*
      SmallLevelFourPrimeRates.monomial (taylorPowers i) (parameter 2 m s)
        (parameter 3 m s) (parameter 13 m s) (parameter 5 m s))*
      (taylorDerivative i:ℂ)^n*gridSample (gridTaylorQ i) (gridTaylorPartner i) w
  | .entire _ => 0
  | .hecke _ => 0
  | .infinity _ => 0

theorem shiftRows_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 780→ℂ) (i : GridSource) :
    gridShiftRows m f ε n s w i =
      I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*
        slopeRows m f ε (n+1) s w i := by
  cases i <;> simp only [gridShiftRows,slopeRows,matrixScalar_factor,taylorScalar_factor,phase] <;> ring

def fullSlopeMatrix (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) :
    Matrix GridSource (Fin 320) ℂ :=
  fun i j => slopeRows m f ε n s (extension support (Pi.single j 1)) i

theorem fullShiftMatrix_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (i : GridSource) (j : Fin 320) :
    fullShiftMatrix m f ε n s i j =
      I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)*
        fullSlopeMatrix m f ε (n+1) s i j := by
  simp only [fullShiftMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply,
    shiftLinearMap,fullSlopeMatrix]
  exact shiftRows_factor m f ε n s _ i

#print axioms shiftRows_factor
#print axioms fullShiftMatrix_factor
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridNormalizedGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Filter Matrix QuantitativeArithmeticAnalyticGerm
open scoped Topology

lemma choose_two_complex (z : ℂ) : Ring.choose z 2=z*(z-1)/2 := by
  norm_num [Ring.choose_eq_smul,descPochhammer_succ_right,Polynomial.smeval_mul,
    Polynomial.smeval_sub,Polynomial.smeval_X,Polynomial.smeval_C]
  ring

def firstLayer (m : ℕ) (G : ℂ→Fin 320→ℂ) (s : ℂ) (j : Fin 320) : ℂ :=
  G (s-1) j/(I*(s-((2*m:ℕ):ℂ)))

def secondLayer (m : ℕ) (G : ℂ→Fin 320→ℂ) (s : ℂ) (j : Fin 320) : ℂ :=
  G (s-2) j/(I^2*(s-((2*m:ℕ):ℂ))*(s-((2*m:ℕ):ℂ)-1))

theorem PoleSystem.top_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (i : GridSource) :
    HasAnalyticGerm (fun z => ∑ j,fullLeadingMatrix m f ε z i j*S.G z j) x := by
  simpa using S.lower_taylor_germs x hshift 0 i

/-- Normalization of the first complete Taylor layer, using an analytic
unit at the selected point. No pole-order comparison is used. -/
theorem PoleSystem.first_normalized_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (i : GridSource) :
    HasAnalyticGerm (fun z => ∑ j,
      (fullLeadingMatrix m f ε (z-1) i j*firstLayer m S.G z j-
        fullSlopeMatrix m f ε 1 (z-1) i j*S.G z j)) x := by
  have hh := S.lower_taylor_germs x hshift 1 i
  simp only [Nat.cast_one,Finset.sum_range_one,Nat.sub_self,Nat.zero_sub,Nat.cast_zero,
    sub_zero] at hh
  have ha : AnalyticAt ℂ (fun z : ℂ => 1/(I*(z-((2*m:ℕ):ℂ)))) x :=
    analyticAt_const.div (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
      (mul_ne_zero I_ne_zero (sub_ne_zero.mpr hx))
  apply (hh.mul_analytic ha).congr
  have he : ∀ᶠ z in 𝓝[≠] x,z≠((2*m:ℕ):ℂ) :=
    (eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with z hz
  simp only [mul_sub,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [fullShiftMatrix_factor]
  simp only [Nat.zero_add,Nat.cast_one,pow_one,Ring.choose_one_right,sub_add_cancel,
    firstLayer]
  field_simp [I_ne_zero,sub_ne_zero.mpr hz]

/-- The second normalized layer retains both lower germs. Its second
Taylor coefficient is the rational slope squared divided by two. -/
theorem PoleSystem.second_normalized_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hx : x≠((2*m:ℕ):ℂ)) (hx1 : x≠((2*m:ℕ):ℂ)+1) (i : GridSource) :
    HasAnalyticGerm (fun z => ∑ j,
      (fullLeadingMatrix m f ε (z-2) i j*secondLayer m S.G z j-
        fullSlopeMatrix m f ε 1 (z-2) i j*firstLayer m S.G z j-
        fullSlopeMatrix m f ε 2 (z-2) i j*S.G z j/2)) x := by
  have hh := S.lower_taylor_germs x hshift 2 i
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceSub,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,sub_zero] at hh
  have hn : x-((2*m:ℕ):ℂ)-1≠0 := by intro h; apply hx1; linear_combination h
  have ha : AnalyticAt ℂ
      (fun z : ℂ => 1/(I^2*(z-((2*m:ℕ):ℂ))*(z-((2*m:ℕ):ℂ)-1))) x :=
    analyticAt_const.div
      ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).mul
        ((analyticAt_id.sub analyticAt_const).sub analyticAt_const))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero) (sub_ne_zero.mpr hx)) hn)
  apply (hh.mul_analytic ha).congr
  have he : ∀ᶠ z in 𝓝[≠] x,z≠((2*m:ℕ):ℂ) :=
    (eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds
  have he1 : ∀ᶠ z in 𝓝[≠] x,z≠((2*m:ℕ):ℂ)+1 :=
    (eventually_ne_nhds hx1).filter_mono nhdsWithin_le_nhds
  filter_upwards [he,he1] with z hz hz1
  have hnz : z-((2*m:ℕ):ℂ)-1≠0 := by intro h; apply hz1; linear_combination h
  simp only [mul_sub,mul_add,Finset.mul_sum,←Finset.sum_add_distrib,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [fullShiftMatrix_factor,Nat.reduceAdd,Nat.cast_one,Nat.cast_ofNat,pow_one,
    Ring.choose_one_right,choose_two_complex,firstLayer,secondLayer]
  field_simp [I_ne_zero,sub_ne_zero.mpr hz,hnz]
  ring

#print axioms PoleSystem.top_germ
#print axioms PoleSystem.first_normalized_germ
#print axioms PoleSystem.second_normalized_germ
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridBatchedIntegerPoleExclusionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix QuantitativeArithmeticUniversalPoleVector

/-- A rightmost pole cannot occur at a positive integer exponent. -/
theorem PoleSystem.integer_rightmost_regular_batched {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (n : ℕ) (hn : 1≤n)
    (hshift : ∀ t : ℕ,0<t → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j)
      (((m+n:ℕ):ℂ)+t)) :
    ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) ((m+n:ℕ):ℂ) := by
  intro j
  by_contra h
  have hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) ((m+n:ℕ):ℂ)<0 :=
    ⟨j,lt_of_not_ge h⟩
  obtain ⟨v,hv⟩ := exists_leading_vector S.G ((m+n:ℕ):ℂ)
    (fun j => (S.meromorphic j _).meromorphicAt) hpole
  exact hv.1 (original_full_leading_kernel_integer_batched m n hn hf hε v
    (S.rightmost_leading_kernel _ v hv hshift))

/-- The two normalization denominators are units at any rightmost pole;
this is derived from the original solution, not assumed. -/
theorem PoleSystem.normalization_units_batched {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) (hε : ε=1 ∨ ε= -1)
    (x : ℂ) (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0)
    (hshift : ∀ t : ℕ,0<t → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+t)) :
    x≠((2*m:ℕ):ℂ) ∧ x≠((2*m:ℕ):ℂ)+1 := by
  have exclude (n : ℕ) (hn : 1≤n) (he : x=((m+n:ℕ):ℂ)) : False := by
    subst x
    obtain ⟨j,hj⟩ := hpole
    exact (not_lt_of_ge (S.integer_rightmost_regular_batched hf hε n hn hshift j)) hj
  constructor
  · intro he
    apply exclude m (by omega)
    rw [he]
    congr 1
    omega
  · intro he
    apply exclude (m+1) (by omega)
    rw [he]
    push_cast
    ring

#print axioms PoleSystem.integer_rightmost_regular_batched
#print axioms PoleSystem.normalization_units_batched
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridMMMNormalizationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Matrix QuantitativeArithmeticUniversalPoleVector

theorem PoleSystem.integer_rightmost_regular_mmm {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (T : PoleSystem m f ε) (u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u)
    (hs13 : badParameter f 13= -v) (n : ℕ) (hn : 1≤n)
    (hshift : ∀ t : ℕ,0<t → ∀ j,0≤meromorphicOrderAt (fun z => T.G z j)
      (((m+n:ℕ):ℂ)+t)) :
    ∀ j,0≤meromorphicOrderAt (fun z => T.G z j) ((m+n:ℕ):ℂ) := by
  have hk : ∀ w : Fin 320→ℂ,
      fullLeadingMatrix m f ε ((m+n:ℕ):ℂ) *ᵥ w=0 → w=0 := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer
        m n f ε 1 1 (by norm_num) (by norm_num) hn
        (by simpa using hη) (by simpa using hs2) (by simpa using hs13)
    · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer
        m n f ε 1 (-1) (by norm_num) (by norm_num) hn
        (by simpa using hη) (by simpa using hs2) (by simpa using hs13)
    · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer
        m n f ε (-1) 1 (by norm_num) (by norm_num) hn
        (by simpa using hη) (by simpa using hs2) (by simpa using hs13)
    · exact SmallLevelTwentySixUnitMMMBatched.full_leading_kernel_integer
        m n f ε (-1) (-1) (by norm_num) (by norm_num) hn
        (by simpa using hη) (by simpa using hs2) (by simpa using hs13)
  intro j
  by_contra h
  have hpole : ∃ j,meromorphicOrderAt (fun z => T.G z j) ((m+n:ℕ):ℂ)<0 :=
    ⟨j,lt_of_not_ge h⟩
  obtain ⟨w,hw⟩ := exists_leading_vector T.G ((m+n:ℕ):ℂ)
    (fun j => (T.meromorphic j _).meromorphicAt) hpole
  exact hw.1 (hk w (T.rightmost_leading_kernel _ w hw hshift))

/-- Normalization in the MMM family uses only that family's finite rank
proof; it does not depend on any MMP elimination certificate. -/
theorem PoleSystem.normalization_units_mmm {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (T : PoleSystem m f ε) (hm : 0<m) (s u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u)
    (hs13 : badParameter f 13= -v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => T.G z j) s<0)
    (hshift : ∀ t : ℕ,0<t → ∀ j,0≤meromorphicOrderAt (fun z => T.G z j) (s+t)) :
    s≠((2*m:ℕ):ℂ) ∧ s≠((2*m:ℕ):ℂ)+1 := by
  have exclude (n : ℕ) (hn : 1≤n) (he : s=((m+n:ℕ):ℂ)) : False := by
    subst s
    obtain ⟨j,hj⟩ := hpole
    exact (not_lt_of_ge
      (T.integer_rightmost_regular_mmm u v hu hv hη hs2 hs13 n hn hshift j)) hj
  constructor
  · intro he
    apply exclude m (by omega)
    rw [he]
    congr 1
    omega
  · intro he
    apply exclude (m+1) (by omega)
    rw [he]
    push_cast
    ring

#print axioms PoleSystem.integer_rightmost_regular_mmm
#print axioms PoleSystem.normalization_units_mmm
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixGridRegularityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex Filter SmallLevelAdditive SmallLevelTwentySixUnitMMM
open scoped Topology

theorem PoleSystem.analytic_halfplane {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f) :
    ∃ B : ℝ,∀ i : Fin 320,∀ s : ℂ,B<s.re → AnalyticAt ℂ (fun z => S.G z i) s := by
  obtain ⟨B,hB⟩:=original_common_halfplane hf
  refine ⟨max B S.B,?_⟩
  intro i s hs
  have hS : S.B<s.re:=(le_max_right _ _).trans_lt hs
  have he : (fun z => S.G z i)=ᶠ[𝓝 s] (fun z => actualGrid m f z i) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hS] with z hz
    exact congrFun (S.agreement z hz) i
  apply (analyticAt_congr he).mpr
  simpa only [actualGrid,gridVector,grid,Int.cast_natCast,Nat.cast_ofNat] using
    (hB (((support i).val:ℝ)/780) s ((le_max_left _ _).trans_lt hs)).1

/-- Rightmost-pole exclusion suffices for every point of the original grid;
there is no assumption that poles at different coordinates have equal orders. -/
theorem PoleSystem.nonnegative_orders_of_rightmost {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (hno : ∀ s : ℂ,
      (∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n)) →
      ¬∃ j,meromorphicOrderAt (fun z => S.G z j) s<0) :
    ∀ x j,0≤meromorphicOrderAt (fun z => S.G z j) x := by
  obtain ⟨B,hB⟩:=S.analytic_halfplane hf
  intro x j
  by_contra! hp
  obtain ⟨n,hn,hshift⟩:=SmallLevelPoleGrid.rightmost_pole
    (fun j z => S.G z j) ⟨j,hp⟩ B hB
  exact hno (x+n) hshift hn

#print axioms PoleSystem.analytic_halfplane
#print axioms PoleSystem.nonnegative_orders_of_rightmost
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixOriginalMMMModularitySmallV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex

/-- The signed MMM family, including both Taylor normalization points.
The two systems use actual original continuations; their equality follows
from uniqueness rather than an added compatibility hypothesis. -/
theorem PoleSystem.regular_mmm_small {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (T : PoleSystem m f ε) (S : SmallLevelTwentySixGermSources.PoleSystem m f ε)
    (hm : 0<m) (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u)
    (hs13 : badParameter f 13= -v) :
    ∀ x j,0≤meromorphicOrderAt (fun z => T.G z j) x := by
  apply T.nonnegative_orders_of_rightmost hf
  intro s hshift hpole
  obtain ⟨hs,hs1⟩:=T.normalization_units_mmm hm s u v hu hv hη hs2 hs13 hpole hshift
  have hG:=S.grid_G_eq T
  have hshiftS : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (s+n) := by
    simpa only [hG] using hshift
  have hpoleS : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0 := by
    simpa only [hG] using hpole
  exact SmallLevelTwentySixGermDAG.original_signed_mmm_no_pole_small
    S T s u v hu hv hshiftS hs hs1 hη hs2 hs13 hpoleS

theorem PoleSystem.modular_mmm_small {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (T : PoleSystem m f ε) (S : SmallLevelTwentySixGermSources.PoleSystem m f ε)
    (hm : 0<m) (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u)
    (hs13 : badParameter f 13= -v) :
    SmallLevelOriginal.IsModular 26 (2*m) f :=
  T.modular_of_nonnegative_orders hm hf
    (T.regular_mmm_small S hm hf u v hu hv hη hs2 hs13)

#print axioms PoleSystem.regular_mmm_small
#print axioms PoleSystem.modular_mmm_small
end SmallLevelTwentySixGrid
end
end

/-! ## SmallLevelTwentySixOriginalMMPModularityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentySixGrid
open Complex

/-- The signed MMP family, including both Taylor normalization points.
The two systems use actual original continuations; their equality follows
from uniqueness rather than an added compatibility hypothesis. -/
theorem PoleSystem.regular_mmp {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (T : PoleSystem m f ε) (S : SmallLevelTwentySixGermSources.PoleSystem m f ε)
    (hm : 0<m) (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u)
    (hs13 : badParameter f 13=v) :
    ∀ x j,0≤meromorphicOrderAt (fun z => T.G z j) x := by
  apply T.nonnegative_orders_of_rightmost hf
  intro s hshift hpole
  obtain ⟨hs,hs1⟩:=T.normalization_units_batched hm hf hε s hpole hshift
  have hG:=S.grid_G_eq T
  have hshiftS : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (s+n) := by
    simpa only [hG] using hshift
  have hpoleS : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0 := by
    simpa only [hG] using hpole
  exact QuantitativeArithmeticSmallLevelTwentySixMMPOriginalPoleExclusion.original_signed_mmp_no_pole
    S T s u v hu hv hshiftS hs hs1 hη hs2 hs13 hpoleS

theorem PoleSystem.modular_mmp {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (T : PoleSystem m f ε) (S : SmallLevelTwentySixGermSources.PoleSystem m f ε)
    (hm : 0<m) (hf : FinitenessOriginalInput.IsSolution 26 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u)
    (hs13 : badParameter f 13=v) :
    SmallLevelOriginal.IsModular 26 (2*m) f :=
  T.modular_of_nonnegative_orders hm hf
    (T.regular_mmp S hm hf hε u v hu hv hη hs2 hs13)

#print axioms PoleSystem.regular_mmp
#print axioms PoleSystem.modular_mmp
end SmallLevelTwentySixGrid
end
end
