module

public import SmallLevelTwentyOneFiniteGridTheoryV4
public import SmallLevelTwentyOneLargeGridAlgebraTheoryV4
public import SmallLevelTwentyOneTheoryV4

/-! Consolidated chapter: SmallLevelTwentyOneLargeGridData. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneLargeGridDataTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentyOneLargeGridData. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentyOneLargeGridTaylorCertificateV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridData
open Complex SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneKnownWords SmallLevelTaylor Set
open SmallLevelTwentyOne

def taylorRate (q : ℕ) (t : ℤ) : ℚ := (Nat.lcm 21 (q^2):ℚ)*((t:ℚ)/210)^2
def taylorSlope (q : ℕ) (t : ℤ) : ℚ := (Nat.lcm 21 (q^2):ℚ)*(t:ℚ)/210

structure TaylorCertificate where
  q : ℕ
  source : ℤ
  target : ℤ
  d : ℤ
  positive : 0<q
  divides : q∣210
  nonzero : source≠0
  level_identity : (Nat.lcm 21 (q^2):ℤ)*d=(210:ℤ)^2
  source_divides : source∣d
  target_eq : target= -(d/source)
  rate : ℚ
  slope : ℚ
  powers : ℤ×ℤ×ℤ×ℤ
  rate_eq : taylorRate q source=rate
  slope_eq : taylorSlope q source=slope
  powers_eq : rate=(2:ℚ)^powers.1*(3:ℚ)^powers.2.1*(7:ℚ)^powers.2.2.1*(5:ℚ)^powers.2.2.2

theorem taylorCoefficient_rational (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    {q : ℕ} (hq : q∣210) (t : ℤ) (n : ℕ) (s : ℂ) :
    taylorCoefficient 210 (2*m) f ε q t n s=
      phaseRoot m ε*localRoot (rootU f) (rootV f) q*(taylorRate q t:ℂ)^(s-(m:ℂ))*
        (I*(taylorSlope q t:ℂ))^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hr : (((Nat.lcm 21 (q^2):ℝ)*((t:ℝ)/210)^2:ℝ):ℂ)=(taylorRate q t:ℂ) := by
    simp [taylorRate]
  have hd : I*(Nat.lcm 21 (q^2):ℂ)*(((t:ℝ)/210:ℝ):ℂ)=I*(taylorSlope q t:ℂ) := by
    simp [taylorSlope]
    ring
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  unfold taylorCoefficient taylorRowScalar
  rw [root_large_grid_divisor f hq]
  simp only [Nat.cast_ofNat,Complex.ofReal_natCast]
  rw [hr]
  rw [hd,hm]
  unfold phaseRoot
  ring

theorem taylor_certificate_leading (r : TaylorCertificate) (m : ℕ) (f : ℕ → ℂ)
    (ε s : ℂ) :
    taylorCoefficient 210 (2*m) f ε r.q r.source 0 s=
      phaseRoot m ε*localRoot (rootU f) (rootV f) r.q*
        fourPrimeMonomial r.powers (primeParameter 2 m s) (primeParameter 3 m s)
          (primeParameter 7 m s) (primeParameter 5 m s) := by
  rw [taylorCoefficient_rational m f ε r.divides]
  simp only [pow_zero,Ring.choose_zero_right,mul_one,r.rate_eq]
  rw [rational_four_prime_power _ _ r.powers_eq]
  rfl

theorem taylor_coefficient_analytic (r : TaylorCertificate) (k : ℕ) (f : ℕ → ℂ)
    (ε : ℂ) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (taylorCoefficient 210 k f ε r.q r.source n) s := by
  apply taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<21) (pow_pos r.positive 2)
  · exact div_ne_zero (by exact_mod_cast r.nonzero) (by norm_num)

theorem taylor_certificate_rows (r : TaylorCertificate) {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (taylorError 210 (2*m) f ε r.q r.source M)
        {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        SmallLevelTwentyOneFiniteGrid.sampleSum 210 (by decide) r.q r.source
            (SmallLevelTwentyOneFiniteGrid.gridVector 210 (2*m) f s)-
          taylorCoefficient 210 (2*m) f ε r.q r.source 0 s*
            SmallLevelTwentyOneFiniteGrid.sampleSum 210 (by decide) r.q r.target
              (SmallLevelTwentyOneFiniteGrid.gridVector 210 (2*m) f s)=
        taylorError 210 (2*m) f ε r.q r.source M s+∑ n∈Finset.range M,
          taylorCoefficient 210 (2*m) f ε r.q r.source (n+1) s*
            SmallLevelTwentyOneFiniteGrid.sampleSum 210 (by decide) r.q r.target
              (SmallLevelTwentyOneFiniteGrid.gridVector 210 (2*m) f (s+((n:ℂ)+1))) := by
  rw [r.target_eq]
  exact original_taylor_rows 210 (by decide) hf ε hlaw r.q r.positive r.divides
    r.source r.d r.nonzero r.level_identity r.source_divides

#print axioms taylor_certificate_leading
#print axioms taylor_coefficient_analytic
#print axioms taylor_certificate_rows
end SmallLevelTwentyOneLargeGridData
end
end

/-! ## SmallLevelTwentyOneLargeGridWordDataV1 -/
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneLargeGridData
open SmallLevelTwentyOneKnownWords SmallLevelTwentyOneFiniteGrid Matrix

def word00 : Word := (.mul .one (.generator 3))
theorem word00_matrix : integerRaw word00=!![0,-1;21,0] := by decide
theorem word00_count : frickeCount word00=1 := by decide
#print axioms word00_matrix
def word01 : Word := (.mul (.mul (.mul .one (.generator 3)) (.generator 0)) (.generator 0))
theorem word01_matrix : integerRaw word01=!![0,-1;21,42] := by decide
theorem word01_count : frickeCount word01=1 := by decide
#print axioms word01_matrix
def word02 : Word := (.mul (.mul .one (.generator 3)) (.generator 0))
theorem word02_matrix : integerRaw word02=!![0,-1;21,21] := by decide
theorem word02_count : frickeCount word02=1 := by decide
#print axioms word02_matrix
def word03 : Word := (.mul (.mul .one (.generator 1)) (.generator 3))
theorem word03_matrix : integerRaw word03=!![0,-1;21,-21] := by decide
theorem word03_count : frickeCount word03=1 := by decide
#print axioms word03_matrix
def word04 : Word := (.mul (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 1))) (.generator 2))
theorem word04_matrix : integerRaw word04=!![2,-1;-105,53] := by decide
theorem word04_count : frickeCount word04=0 := by decide
#print axioms word04_matrix
def word05 : Word := (.mul (.mul .one (.generator 1)) (.inv (.generator 0)))
theorem word05_matrix : integerRaw word05=!![1,-1;21,-20] := by decide
theorem word05_count : frickeCount word05=0 := by decide
#print axioms word05_matrix
def word06 : Word := (.mul (.mul .one (.inv (.generator 1))) (.generator 2))
theorem word06_matrix : integerRaw word06=!![2,-1;-63,32] := by decide
theorem word06_count : frickeCount word06=0 := by decide
#print axioms word06_matrix
def word07 : Word := (.mul .one (.generator 2))
theorem word07_matrix : integerRaw word07=!![2,-1;-21,11] := by decide
theorem word07_count : frickeCount word07=0 := by decide
#print axioms word07_matrix
def word08 : Word := (.mul (.mul .one (.generator 1)) (.generator 2))
theorem word08_matrix : integerRaw word08=!![2,-1;21,-10] := by decide
theorem word08_count : frickeCount word08=0 := by decide
#print axioms word08_matrix
def word09 : Word := (.mul (.mul .one (.inv (.generator 1))) (.inv (.generator 0)))
theorem word09_matrix : integerRaw word09=!![1,-1;-21,22] := by decide
theorem word09_count : frickeCount word09=0 := by decide
#print axioms word09_matrix
def word10 : Word := (.mul .one (.inv (.generator 1)))
theorem word10_matrix : integerRaw word10=!![1,0;-21,1] := by decide
theorem word10_count : frickeCount word10=0 := by decide
#print axioms word10_matrix
def word11 : Word := (.mul (.mul (.mul .one (.generator 1)) (.generator 1)) (.generator 2))
theorem word11_matrix : integerRaw word11=!![2,-1;63,-31] := by decide
theorem word11_count : frickeCount word11=0 := by decide
#print axioms word11_matrix
end SmallLevelTwentyOneLargeGridData
end
end
end

/-! ## SmallLevelTwentyOneLargeGridTaylorBundleV4 -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyOneLargeGridData
open Complex SmallLevelTwentyOneFiniteGrid SmallLevelTwentyOneLargeGridAlgebra

def taylorRow1102 : TaylorCertificate where
  q := 6
  source := 5
  target := -35
  d := 175
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := 6
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1102

theorem taylor_link1102 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1102 x y z b v=
      sampleSum 210 (by decide) taylorRow1102.q taylorRow1102.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1102.q*
          fourPrimeMonomial taylorRow1102.powers x y z b*
            sampleSum 210 (by decide) taylorRow1102.q taylorRow1102.target v := by
  norm_num [source1102,sampleSum,gridIndex,taylorRow1102,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1102

def taylorRow1103 : TaylorCertificate where
  q := 6
  source := -5
  target := 35
  d := 175
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := -6
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1103

theorem taylor_link1103 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1103 x y z b v=
      sampleSum 210 (by decide) taylorRow1103.q taylorRow1103.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1103.q*
          fourPrimeMonomial taylorRow1103.powers x y z b*
            sampleSum 210 (by decide) taylorRow1103.q taylorRow1103.target v := by
  norm_num [source1103,sampleSum,gridIndex,taylorRow1103,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1103

def taylorRow1048 : TaylorCertificate where
  q := 3
  source := 10
  target := -70
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := 3
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1048

theorem taylor_link1048 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1048 x y z b v=
      sampleSum 210 (by decide) taylorRow1048.q taylorRow1048.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1048.q*
          fourPrimeMonomial taylorRow1048.powers x y z b*
            sampleSum 210 (by decide) taylorRow1048.q taylorRow1048.target v := by
  norm_num [source1048,sampleSum,gridIndex,taylorRow1048,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1048

def taylorRow1051 : TaylorCertificate where
  q := 3
  source := -14
  target := 50
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/25)
  slope := (-21/5)
  powers := (0,0,1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1051

theorem taylor_link1051 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1051 x y z b v=
      sampleSum 210 (by decide) taylorRow1051.q taylorRow1051.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1051.q*
          fourPrimeMonomial taylorRow1051.powers x y z b*
            sampleSum 210 (by decide) taylorRow1051.q taylorRow1051.target v := by
  norm_num [source1051,sampleSum,gridIndex,taylorRow1051,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1051

def taylorRow1052 : TaylorCertificate where
  q := 3
  source := 20
  target := -35
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (4/7)
  slope := 6
  powers := (2,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1052

theorem taylor_link1052 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1052 x y z b v=
      sampleSum 210 (by decide) taylorRow1052.q taylorRow1052.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1052.q*
          fourPrimeMonomial taylorRow1052.powers x y z b*
            sampleSum 210 (by decide) taylorRow1052.q taylorRow1052.target v := by
  norm_num [source1052,sampleSum,gridIndex,taylorRow1052,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1052

def taylorRow1054 : TaylorCertificate where
  q := 3
  source := 25
  target := -28
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (25/28)
  slope := (15/2)
  powers := (-2,0,-1,2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1054

theorem taylor_link1054 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1054 x y z b v=
      sampleSum 210 (by decide) taylorRow1054.q taylorRow1054.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1054.q*
          fourPrimeMonomial taylorRow1054.powers x y z b*
            sampleSum 210 (by decide) taylorRow1054.q taylorRow1054.target v := by
  norm_num [source1054,sampleSum,gridIndex,taylorRow1054,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1054

def taylorRow1049 : TaylorCertificate where
  q := 3
  source := -10
  target := 70
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := -3
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1049

theorem taylor_link1049 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1049 x y z b v=
      sampleSum 210 (by decide) taylorRow1049.q taylorRow1049.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1049.q*
          fourPrimeMonomial taylorRow1049.powers x y z b*
            sampleSum 210 (by decide) taylorRow1049.q taylorRow1049.target v := by
  norm_num [source1049,sampleSum,gridIndex,taylorRow1049,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1049

def taylorRow1050 : TaylorCertificate where
  q := 3
  source := 14
  target := -50
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/25)
  slope := (21/5)
  powers := (0,0,1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1050

theorem taylor_link1050 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1050 x y z b v=
      sampleSum 210 (by decide) taylorRow1050.q taylorRow1050.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1050.q*
          fourPrimeMonomial taylorRow1050.powers x y z b*
            sampleSum 210 (by decide) taylorRow1050.q taylorRow1050.target v := by
  norm_num [source1050,sampleSum,gridIndex,taylorRow1050,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1050

def taylorRow1053 : TaylorCertificate where
  q := 3
  source := -20
  target := 35
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (4/7)
  slope := -6
  powers := (2,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1053

theorem taylor_link1053 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1053 x y z b v=
      sampleSum 210 (by decide) taylorRow1053.q taylorRow1053.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1053.q*
          fourPrimeMonomial taylorRow1053.powers x y z b*
            sampleSum 210 (by decide) taylorRow1053.q taylorRow1053.target v := by
  norm_num [source1053,sampleSum,gridIndex,taylorRow1053,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1053

def taylorRow1055 : TaylorCertificate where
  q := 3
  source := -25
  target := 28
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (25/28)
  slope := (-15/2)
  powers := (-2,0,-1,2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1055

theorem taylor_link1055 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1055 x y z b v=
      sampleSum 210 (by decide) taylorRow1055.q taylorRow1055.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1055.q*
          fourPrimeMonomial taylorRow1055.powers x y z b*
            sampleSum 210 (by decide) taylorRow1055.q taylorRow1055.target v := by
  norm_num [source1055,sampleSum,gridIndex,taylorRow1055,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1055

def taylorRow1104 : TaylorCertificate where
  q := 6
  source := 7
  target := -25
  d := 175
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/25)
  slope := (42/5)
  powers := (0,0,1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1104

theorem taylor_link1104 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1104 x y z b v=
      sampleSum 210 (by decide) taylorRow1104.q taylorRow1104.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1104.q*
          fourPrimeMonomial taylorRow1104.powers x y z b*
            sampleSum 210 (by decide) taylorRow1104.q taylorRow1104.target v := by
  norm_num [source1104,sampleSum,gridIndex,taylorRow1104,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1104

def taylorRow1044 : TaylorCertificate where
  q := 3
  source := 5
  target := -140
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/28)
  slope := (3/2)
  powers := (-2,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1044

theorem taylor_link1044 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1044 x y z b v=
      sampleSum 210 (by decide) taylorRow1044.q taylorRow1044.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1044.q*
          fourPrimeMonomial taylorRow1044.powers x y z b*
            sampleSum 210 (by decide) taylorRow1044.q taylorRow1044.target v := by
  norm_num [source1044,sampleSum,gridIndex,taylorRow1044,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1044

def taylorRow1105 : TaylorCertificate where
  q := 6
  source := -7
  target := 25
  d := 175
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/25)
  slope := (-42/5)
  powers := (0,0,1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1105

theorem taylor_link1105 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1105 x y z b v=
      sampleSum 210 (by decide) taylorRow1105.q taylorRow1105.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1105.q*
          fourPrimeMonomial taylorRow1105.powers x y z b*
            sampleSum 210 (by decide) taylorRow1105.q taylorRow1105.target v := by
  norm_num [source1105,sampleSum,gridIndex,taylorRow1105,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1105

def taylorRow1045 : TaylorCertificate where
  q := 3
  source := -5
  target := 140
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/28)
  slope := (-3/2)
  powers := (-2,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1045

theorem taylor_link1045 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1045 x y z b v=
      sampleSum 210 (by decide) taylorRow1045.q taylorRow1045.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1045.q*
          fourPrimeMonomial taylorRow1045.powers x y z b*
            sampleSum 210 (by decide) taylorRow1045.q taylorRow1045.target v := by
  norm_num [source1045,sampleSum,gridIndex,taylorRow1045,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1045

def taylorRow1152 : TaylorCertificate where
  q := 10
  source := 3
  target := -7
  d := 21
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/7)
  slope := 30
  powers := (0,1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1152

theorem taylor_link1152 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1152 x y z b v=
      sampleSum 210 (by decide) taylorRow1152.q taylorRow1152.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1152.q*
          fourPrimeMonomial taylorRow1152.powers x y z b*
            sampleSum 210 (by decide) taylorRow1152.q taylorRow1152.target v := by
  norm_num [source1152,sampleSum,gridIndex,taylorRow1152,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1152

def taylorRow1043 : TaylorCertificate where
  q := 3
  source := -4
  target := 175
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (4/175)
  slope := (-6/5)
  powers := (2,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1043

theorem taylor_link1043 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1043 x y z b v=
      sampleSum 210 (by decide) taylorRow1043.q taylorRow1043.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1043.q*
          fourPrimeMonomial taylorRow1043.powers x y z b*
            sampleSum 210 (by decide) taylorRow1043.q taylorRow1043.target v := by
  norm_num [source1043,sampleSum,gridIndex,taylorRow1043,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1043

def taylorRow1153 : TaylorCertificate where
  q := 10
  source := -3
  target := 7
  d := 21
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/7)
  slope := -30
  powers := (0,1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1153

theorem taylor_link1153 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1153 x y z b v=
      sampleSum 210 (by decide) taylorRow1153.q taylorRow1153.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1153.q*
          fourPrimeMonomial taylorRow1153.powers x y z b*
            sampleSum 210 (by decide) taylorRow1153.q taylorRow1153.target v := by
  norm_num [source1153,sampleSum,gridIndex,taylorRow1153,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1153

def taylorRow1042 : TaylorCertificate where
  q := 3
  source := 4
  target := -175
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (4/175)
  slope := (6/5)
  powers := (2,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1042

theorem taylor_link1042 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1042 x y z b v=
      sampleSum 210 (by decide) taylorRow1042.q taylorRow1042.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1042.q*
          fourPrimeMonomial taylorRow1042.powers x y z b*
            sampleSum 210 (by decide) taylorRow1042.q taylorRow1042.target v := by
  norm_num [source1042,sampleSum,gridIndex,taylorRow1042,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1042

def taylorRow1121 : TaylorCertificate where
  q := 7
  source := 5
  target := -60
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/12)
  slope := (7/2)
  powers := (-2,-1,0,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1121

theorem taylor_link1121 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1121 x y z b v=
      sampleSum 210 (by decide) taylorRow1121.q taylorRow1121.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1121.q*
          fourPrimeMonomial taylorRow1121.powers x y z b*
            sampleSum 210 (by decide) taylorRow1121.q taylorRow1121.target v := by
  norm_num [source1121,sampleSum,gridIndex,taylorRow1121,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1121

def taylorRow1100 : TaylorCertificate where
  q := 6
  source := 1
  target := -175
  d := 175
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/175)
  slope := (6/5)
  powers := (0,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1100

theorem taylor_link1100 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1100 x y z b v=
      sampleSum 210 (by decide) taylorRow1100.q taylorRow1100.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1100.q*
          fourPrimeMonomial taylorRow1100.powers x y z b*
            sampleSum 210 (by decide) taylorRow1100.q taylorRow1100.target v := by
  norm_num [source1100,sampleSum,gridIndex,taylorRow1100,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1100

def taylorRow1123 : TaylorCertificate where
  q := 7
  source := 6
  target := -50
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/25)
  slope := (21/5)
  powers := (0,1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1123

theorem taylor_link1123 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1123 x y z b v=
      sampleSum 210 (by decide) taylorRow1123.q taylorRow1123.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1123.q*
          fourPrimeMonomial taylorRow1123.powers x y z b*
            sampleSum 210 (by decide) taylorRow1123.q taylorRow1123.target v := by
  norm_num [source1123,sampleSum,gridIndex,taylorRow1123,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1123

def taylorRow1047 : TaylorCertificate where
  q := 3
  source := -7
  target := 100
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/100)
  slope := (-21/10)
  powers := (-2,0,1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1047

theorem taylor_link1047 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1047 x y z b v=
      sampleSum 210 (by decide) taylorRow1047.q taylorRow1047.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1047.q*
          fourPrimeMonomial taylorRow1047.powers x y z b*
            sampleSum 210 (by decide) taylorRow1047.q taylorRow1047.target v := by
  norm_num [source1047,sampleSum,gridIndex,taylorRow1047,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1047

def taylorRow1046 : TaylorCertificate where
  q := 3
  source := 7
  target := -100
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/100)
  slope := (21/10)
  powers := (-2,0,1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1046

theorem taylor_link1046 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1046 x y z b v=
      sampleSum 210 (by decide) taylorRow1046.q taylorRow1046.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1046.q*
          fourPrimeMonomial taylorRow1046.powers x y z b*
            sampleSum 210 (by decide) taylorRow1046.q taylorRow1046.target v := by
  norm_num [source1046,sampleSum,gridIndex,taylorRow1046,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1046

def taylorRow1122 : TaylorCertificate where
  q := 7
  source := -5
  target := 60
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/12)
  slope := (-7/2)
  powers := (-2,-1,0,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1122

theorem taylor_link1122 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1122 x y z b v=
      sampleSum 210 (by decide) taylorRow1122.q taylorRow1122.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1122.q*
          fourPrimeMonomial taylorRow1122.powers x y z b*
            sampleSum 210 (by decide) taylorRow1122.q taylorRow1122.target v := by
  norm_num [source1122,sampleSum,gridIndex,taylorRow1122,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1122

def taylorRow1085 : TaylorCertificate where
  q := 5
  source := 7
  target := -12
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/12)
  slope := (35/2)
  powers := (-2,-1,1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1085

theorem taylor_link1085 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1085 x y z b v=
      sampleSum 210 (by decide) taylorRow1085.q taylorRow1085.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1085.q*
          fourPrimeMonomial taylorRow1085.powers x y z b*
            sampleSum 210 (by decide) taylorRow1085.q taylorRow1085.target v := by
  norm_num [source1085,sampleSum,gridIndex,taylorRow1085,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1085

def taylorRow1040 : TaylorCertificate where
  q := 3
  source := 2
  target := -350
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/175)
  slope := (3/5)
  powers := (0,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1040

theorem taylor_link1040 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1040 x y z b v=
      sampleSum 210 (by decide) taylorRow1040.q taylorRow1040.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1040.q*
          fourPrimeMonomial taylorRow1040.powers x y z b*
            sampleSum 210 (by decide) taylorRow1040.q taylorRow1040.target v := by
  norm_num [source1040,sampleSum,gridIndex,taylorRow1040,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1040

def taylorRow1038 : TaylorCertificate where
  q := 3
  source := 1
  target := -700
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/700)
  slope := (3/10)
  powers := (-2,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1038

theorem taylor_link1038 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1038 x y z b v=
      sampleSum 210 (by decide) taylorRow1038.q taylorRow1038.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1038.q*
          fourPrimeMonomial taylorRow1038.powers x y z b*
            sampleSum 210 (by decide) taylorRow1038.q taylorRow1038.target v := by
  norm_num [source1038,sampleSum,gridIndex,taylorRow1038,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1038

def taylorRow1101 : TaylorCertificate where
  q := 6
  source := -1
  target := 175
  d := 175
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/175)
  slope := (-6/5)
  powers := (0,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1101

theorem taylor_link1101 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1101 x y z b v=
      sampleSum 210 (by decide) taylorRow1101.q taylorRow1101.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1101.q*
          fourPrimeMonomial taylorRow1101.powers x y z b*
            sampleSum 210 (by decide) taylorRow1101.q taylorRow1101.target v := by
  norm_num [source1101,sampleSum,gridIndex,taylorRow1101,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1101

def taylorRow1124 : TaylorCertificate where
  q := 7
  source := -6
  target := 50
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/25)
  slope := (-21/5)
  powers := (0,1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1124

theorem taylor_link1124 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1124 x y z b v=
      sampleSum 210 (by decide) taylorRow1124.q taylorRow1124.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1124.q*
          fourPrimeMonomial taylorRow1124.powers x y z b*
            sampleSum 210 (by decide) taylorRow1124.q taylorRow1124.target v := by
  norm_num [source1124,sampleSum,gridIndex,taylorRow1124,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1124

def taylorRow1086 : TaylorCertificate where
  q := 5
  source := -7
  target := 12
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (7/12)
  slope := (-35/2)
  powers := (-2,-1,1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1086

theorem taylor_link1086 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1086 x y z b v=
      sampleSum 210 (by decide) taylorRow1086.q taylorRow1086.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1086.q*
          fourPrimeMonomial taylorRow1086.powers x y z b*
            sampleSum 210 (by decide) taylorRow1086.q taylorRow1086.target v := by
  norm_num [source1086,sampleSum,gridIndex,taylorRow1086,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1086

def taylorRow1041 : TaylorCertificate where
  q := 3
  source := -2
  target := 350
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/175)
  slope := (-3/5)
  powers := (0,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1041

theorem taylor_link1041 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1041 x y z b v=
      sampleSum 210 (by decide) taylorRow1041.q taylorRow1041.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1041.q*
          fourPrimeMonomial taylorRow1041.powers x y z b*
            sampleSum 210 (by decide) taylorRow1041.q taylorRow1041.target v := by
  norm_num [source1041,sampleSum,gridIndex,taylorRow1041,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1041

def taylorRow1039 : TaylorCertificate where
  q := 3
  source := -1
  target := 700
  d := 700
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/700)
  slope := (-3/10)
  powers := (-2,0,-1,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1039

theorem taylor_link1039 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1039 x y z b v=
      sampleSum 210 (by decide) taylorRow1039.q taylorRow1039.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1039.q*
          fourPrimeMonomial taylorRow1039.powers x y z b*
            sampleSum 210 (by decide) taylorRow1039.q taylorRow1039.target v := by
  norm_num [source1039,sampleSum,gridIndex,taylorRow1039,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1039

def taylorRow1079 : TaylorCertificate where
  q := 5
  source := 3
  target := -28
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/28)
  slope := (15/2)
  powers := (-2,1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1079

theorem taylor_link1079 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1079 x y z b v=
      sampleSum 210 (by decide) taylorRow1079.q taylorRow1079.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1079.q*
          fourPrimeMonomial taylorRow1079.powers x y z b*
            sampleSum 210 (by decide) taylorRow1079.q taylorRow1079.target v := by
  norm_num [source1079,sampleSum,gridIndex,taylorRow1079,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1079

def taylorRow1080 : TaylorCertificate where
  q := 5
  source := -3
  target := 28
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/28)
  slope := (-15/2)
  powers := (-2,1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1080

theorem taylor_link1080 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1080 x y z b v=
      sampleSum 210 (by decide) taylorRow1080.q taylorRow1080.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1080.q*
          fourPrimeMonomial taylorRow1080.powers x y z b*
            sampleSum 210 (by decide) taylorRow1080.q taylorRow1080.target v := by
  norm_num [source1080,sampleSum,gridIndex,taylorRow1080,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1080

def taylorRow1083 : TaylorCertificate where
  q := 5
  source := 6
  target := -14
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/7)
  slope := 15
  powers := (0,1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1083

theorem taylor_link1083 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1083 x y z b v=
      sampleSum 210 (by decide) taylorRow1083.q taylorRow1083.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1083.q*
          fourPrimeMonomial taylorRow1083.powers x y z b*
            sampleSum 210 (by decide) taylorRow1083.q taylorRow1083.target v := by
  norm_num [source1083,sampleSum,gridIndex,taylorRow1083,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1083

def taylorRow1084 : TaylorCertificate where
  q := 5
  source := -6
  target := 14
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/7)
  slope := -15
  powers := (0,1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1084

theorem taylor_link1084 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1084 x y z b v=
      sampleSum 210 (by decide) taylorRow1084.q taylorRow1084.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1084.q*
          fourPrimeMonomial taylorRow1084.powers x y z b*
            sampleSum 210 (by decide) taylorRow1084.q taylorRow1084.target v := by
  norm_num [source1084,sampleSum,gridIndex,taylorRow1084,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1084

def taylorRow1127 : TaylorCertificate where
  q := 7
  source := 12
  target := -25
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (12/25)
  slope := (42/5)
  powers := (2,1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1127

theorem taylor_link1127 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1127 x y z b v=
      sampleSum 210 (by decide) taylorRow1127.q taylorRow1127.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1127.q*
          fourPrimeMonomial taylorRow1127.powers x y z b*
            sampleSum 210 (by decide) taylorRow1127.q taylorRow1127.target v := by
  norm_num [source1127,sampleSum,gridIndex,taylorRow1127,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1127

def taylorRow1150 : TaylorCertificate where
  q := 10
  source := 1
  target := -21
  d := 21
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/21)
  slope := 10
  powers := (0,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1150

theorem taylor_link1150 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1150 x y z b v=
      sampleSum 210 (by decide) taylorRow1150.q taylorRow1150.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1150.q*
          fourPrimeMonomial taylorRow1150.powers x y z b*
            sampleSum 210 (by decide) taylorRow1150.q taylorRow1150.target v := by
  norm_num [source1150,sampleSum,gridIndex,taylorRow1150,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1150

def taylorRow1151 : TaylorCertificate where
  q := 10
  source := -1
  target := 21
  d := 21
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/21)
  slope := -10
  powers := (0,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1151

theorem taylor_link1151 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1151 x y z b v=
      sampleSum 210 (by decide) taylorRow1151.q taylorRow1151.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1151.q*
          fourPrimeMonomial taylorRow1151.powers x y z b*
            sampleSum 210 (by decide) taylorRow1151.q taylorRow1151.target v := by
  norm_num [source1151,sampleSum,gridIndex,taylorRow1151,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1151

def taylorRow1174 : TaylorCertificate where
  q := 15
  source := 2
  target := -14
  d := 28
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := 15
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1174

theorem taylor_link1174 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1174 x y z b v=
      sampleSum 210 (by decide) taylorRow1174.q taylorRow1174.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1174.q*
          fourPrimeMonomial taylorRow1174.powers x y z b*
            sampleSum 210 (by decide) taylorRow1174.q taylorRow1174.target v := by
  norm_num [source1174,sampleSum,gridIndex,taylorRow1174,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1174

def taylorRow1175 : TaylorCertificate where
  q := 15
  source := -2
  target := 14
  d := 28
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := -15
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1175

theorem taylor_link1175 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1175 x y z b v=
      sampleSum 210 (by decide) taylorRow1175.q taylorRow1175.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1175.q*
          fourPrimeMonomial taylorRow1175.powers x y z b*
            sampleSum 210 (by decide) taylorRow1175.q taylorRow1175.target v := by
  norm_num [source1175,sampleSum,gridIndex,taylorRow1175,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1175

def taylorRow1204 : TaylorCertificate where
  q := 30
  source := 1
  target := -7
  d := 7
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := 30
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1204

theorem taylor_link1204 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1204 x y z b v=
      sampleSum 210 (by decide) taylorRow1204.q taylorRow1204.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1204.q*
          fourPrimeMonomial taylorRow1204.powers x y z b*
            sampleSum 210 (by decide) taylorRow1204.q taylorRow1204.target v := by
  norm_num [source1204,sampleSum,gridIndex,taylorRow1204,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1204

def taylorRow1205 : TaylorCertificate where
  q := 30
  source := -1
  target := 7
  d := 7
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/7)
  slope := -30
  powers := (0,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1205

theorem taylor_link1205 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1205 x y z b v=
      sampleSum 210 (by decide) taylorRow1205.q taylorRow1205.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1205.q*
          fourPrimeMonomial taylorRow1205.powers x y z b*
            sampleSum 210 (by decide) taylorRow1205.q taylorRow1205.target v := by
  norm_num [source1205,sampleSum,gridIndex,taylorRow1205,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1205

def taylorRow1185 : TaylorCertificate where
  q := 21
  source := 1
  target := -100
  d := 100
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/100)
  slope := (21/10)
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1185

theorem taylor_link1185 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1185 x y z b v=
      sampleSum 210 (by decide) taylorRow1185.q taylorRow1185.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1185.q*
          fourPrimeMonomial taylorRow1185.powers x y z b*
            sampleSum 210 (by decide) taylorRow1185.q taylorRow1185.target v := by
  norm_num [source1185,sampleSum,gridIndex,taylorRow1185,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1185

def taylorRow1186 : TaylorCertificate where
  q := 21
  source := -1
  target := 100
  d := 100
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/100)
  slope := (-21/10)
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1186

theorem taylor_link1186 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1186 x y z b v=
      sampleSum 210 (by decide) taylorRow1186.q taylorRow1186.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1186.q*
          fourPrimeMonomial taylorRow1186.powers x y z b*
            sampleSum 210 (by decide) taylorRow1186.q taylorRow1186.target v := by
  norm_num [source1186,sampleSum,gridIndex,taylorRow1186,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1186

def taylorRow1118 : TaylorCertificate where
  q := 7
  source := -3
  target := 100
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/100)
  slope := (-21/10)
  powers := (-2,1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1118

theorem taylor_link1118 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1118 x y z b v=
      sampleSum 210 (by decide) taylorRow1118.q taylorRow1118.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1118.q*
          fourPrimeMonomial taylorRow1118.powers x y z b*
            sampleSum 210 (by decide) taylorRow1118.q taylorRow1118.target v := by
  norm_num [source1118,sampleSum,gridIndex,taylorRow1118,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1118

def taylorRow1117 : TaylorCertificate where
  q := 7
  source := 3
  target := -100
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (3/100)
  slope := (21/10)
  powers := (-2,1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1117

theorem taylor_link1117 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1117 x y z b v=
      sampleSum 210 (by decide) taylorRow1117.q taylorRow1117.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1117.q*
          fourPrimeMonomial taylorRow1117.powers x y z b*
            sampleSum 210 (by decide) taylorRow1117.q taylorRow1117.target v := by
  norm_num [source1117,sampleSum,gridIndex,taylorRow1117,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1117

def taylorRow1075 : TaylorCertificate where
  q := 5
  source := 1
  target := -84
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/84)
  slope := (5/2)
  powers := (-2,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1075

theorem taylor_link1075 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1075 x y z b v=
      sampleSum 210 (by decide) taylorRow1075.q taylorRow1075.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1075.q*
          fourPrimeMonomial taylorRow1075.powers x y z b*
            sampleSum 210 (by decide) taylorRow1075.q taylorRow1075.target v := by
  norm_num [source1075,sampleSum,gridIndex,taylorRow1075,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1075

def taylorRow1076 : TaylorCertificate where
  q := 5
  source := -1
  target := 84
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/84)
  slope := (-5/2)
  powers := (-2,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1076

theorem taylor_link1076 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1076 x y z b v=
      sampleSum 210 (by decide) taylorRow1076.q taylorRow1076.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1076.q*
          fourPrimeMonomial taylorRow1076.powers x y z b*
            sampleSum 210 (by decide) taylorRow1076.q taylorRow1076.target v := by
  norm_num [source1076,sampleSum,gridIndex,taylorRow1076,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1076

def taylorRow1077 : TaylorCertificate where
  q := 5
  source := 2
  target := -42
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/21)
  slope := 5
  powers := (0,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1077

theorem taylor_link1077 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1077 x y z b v=
      sampleSum 210 (by decide) taylorRow1077.q taylorRow1077.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1077.q*
          fourPrimeMonomial taylorRow1077.powers x y z b*
            sampleSum 210 (by decide) taylorRow1077.q taylorRow1077.target v := by
  norm_num [source1077,sampleSum,gridIndex,taylorRow1077,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1077

def taylorRow1078 : TaylorCertificate where
  q := 5
  source := -2
  target := 42
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/21)
  slope := -5
  powers := (0,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1078

theorem taylor_link1078 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1078 x y z b v=
      sampleSum 210 (by decide) taylorRow1078.q taylorRow1078.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1078.q*
          fourPrimeMonomial taylorRow1078.powers x y z b*
            sampleSum 210 (by decide) taylorRow1078.q taylorRow1078.target v := by
  norm_num [source1078,sampleSum,gridIndex,taylorRow1078,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1078

def taylorRow1081 : TaylorCertificate where
  q := 5
  source := 4
  target := -21
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (4/21)
  slope := 10
  powers := (2,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1081

theorem taylor_link1081 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1081 x y z b v=
      sampleSum 210 (by decide) taylorRow1081.q taylorRow1081.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1081.q*
          fourPrimeMonomial taylorRow1081.powers x y z b*
            sampleSum 210 (by decide) taylorRow1081.q taylorRow1081.target v := by
  norm_num [source1081,sampleSum,gridIndex,taylorRow1081,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1081

def taylorRow1082 : TaylorCertificate where
  q := 5
  source := -4
  target := 21
  d := 84
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (4/21)
  slope := -10
  powers := (2,-1,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1082

theorem taylor_link1082 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1082 x y z b v=
      sampleSum 210 (by decide) taylorRow1082.q taylorRow1082.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1082.q*
          fourPrimeMonomial taylorRow1082.powers x y z b*
            sampleSum 210 (by decide) taylorRow1082.q taylorRow1082.target v := by
  norm_num [source1082,sampleSum,gridIndex,taylorRow1082,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1082

def taylorRow1113 : TaylorCertificate where
  q := 7
  source := 1
  target := -300
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/300)
  slope := (7/10)
  powers := (-2,-1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1113

theorem taylor_link1113 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1113 x y z b v=
      sampleSum 210 (by decide) taylorRow1113.q taylorRow1113.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1113.q*
          fourPrimeMonomial taylorRow1113.powers x y z b*
            sampleSum 210 (by decide) taylorRow1113.q taylorRow1113.target v := by
  norm_num [source1113,sampleSum,gridIndex,taylorRow1113,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1113

def taylorRow1114 : TaylorCertificate where
  q := 7
  source := -1
  target := 300
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/300)
  slope := (-7/10)
  powers := (-2,-1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1114

theorem taylor_link1114 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1114 x y z b v=
      sampleSum 210 (by decide) taylorRow1114.q taylorRow1114.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1114.q*
          fourPrimeMonomial taylorRow1114.powers x y z b*
            sampleSum 210 (by decide) taylorRow1114.q taylorRow1114.target v := by
  norm_num [source1114,sampleSum,gridIndex,taylorRow1114,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1114

def taylorRow1119 : TaylorCertificate where
  q := 7
  source := 4
  target := -75
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (4/75)
  slope := (14/5)
  powers := (2,-1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1119

theorem taylor_link1119 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1119 x y z b v=
      sampleSum 210 (by decide) taylorRow1119.q taylorRow1119.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1119.q*
          fourPrimeMonomial taylorRow1119.powers x y z b*
            sampleSum 210 (by decide) taylorRow1119.q taylorRow1119.target v := by
  norm_num [source1119,sampleSum,gridIndex,taylorRow1119,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1119

def taylorRow1172 : TaylorCertificate where
  q := 15
  source := 1
  target := -28
  d := 28
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/28)
  slope := (15/2)
  powers := (-2,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1172

theorem taylor_link1172 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1172 x y z b v=
      sampleSum 210 (by decide) taylorRow1172.q taylorRow1172.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1172.q*
          fourPrimeMonomial taylorRow1172.powers x y z b*
            sampleSum 210 (by decide) taylorRow1172.q taylorRow1172.target v := by
  norm_num [source1172,sampleSum,gridIndex,taylorRow1172,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1172

def taylorRow1173 : TaylorCertificate where
  q := 15
  source := -1
  target := 28
  d := 28
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/28)
  slope := (-15/2)
  powers := (-2,0,-1,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1173

theorem taylor_link1173 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1173 x y z b v=
      sampleSum 210 (by decide) taylorRow1173.q taylorRow1173.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1173.q*
          fourPrimeMonomial taylorRow1173.powers x y z b*
            sampleSum 210 (by decide) taylorRow1173.q taylorRow1173.target v := by
  norm_num [source1173,sampleSum,gridIndex,taylorRow1173,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1173

def taylorRow1209 : TaylorCertificate where
  q := 35
  source := 1
  target := -12
  d := 12
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/12)
  slope := (35/2)
  powers := (-2,-1,0,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1209

theorem taylor_link1209 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1209 x y z b v=
      sampleSum 210 (by decide) taylorRow1209.q taylorRow1209.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1209.q*
          fourPrimeMonomial taylorRow1209.powers x y z b*
            sampleSum 210 (by decide) taylorRow1209.q taylorRow1209.target v := by
  norm_num [source1209,sampleSum,gridIndex,taylorRow1209,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1209

def taylorRow1210 : TaylorCertificate where
  q := 35
  source := -1
  target := 12
  d := 12
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/12)
  slope := (-35/2)
  powers := (-2,-1,0,0)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1210

theorem taylor_link1210 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1210 x y z b v=
      sampleSum 210 (by decide) taylorRow1210.q taylorRow1210.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1210.q*
          fourPrimeMonomial taylorRow1210.powers x y z b*
            sampleSum 210 (by decide) taylorRow1210.q taylorRow1210.target v := by
  norm_num [source1210,sampleSum,gridIndex,taylorRow1210,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1210

def taylorRow1116 : TaylorCertificate where
  q := 7
  source := -2
  target := 150
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/75)
  slope := (-7/5)
  powers := (0,-1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1116

theorem taylor_link1116 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1116 x y z b v=
      sampleSum 210 (by decide) taylorRow1116.q taylorRow1116.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1116.q*
          fourPrimeMonomial taylorRow1116.powers x y z b*
            sampleSum 210 (by decide) taylorRow1116.q taylorRow1116.target v := by
  norm_num [source1116,sampleSum,gridIndex,taylorRow1116,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1116

def taylorRow1115 : TaylorCertificate where
  q := 7
  source := 2
  target := -150
  d := 300
  positive := by decide
  divides := by decide
  nonzero := by decide
  level_identity := by decide
  source_divides := by decide
  target_eq := by decide
  rate := (1/75)
  slope := (7/5)
  powers := (0,-1,0,-2)
  rate_eq := by norm_num [taylorRate,Nat.lcm]
  slope_eq := by norm_num [taylorSlope,Nat.lcm]
  powers_eq := by norm_num
#print axioms taylorRow1115

theorem taylor_link1115 (x y z b : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) (hb : b≠0)
    (v : Fin 210 → ℂ) :
    source1115 x y z b v=
      sampleSum 210 (by decide) taylorRow1115.q taylorRow1115.source v-
        (-1:ℂ)*SmallLevelTwentyOne.localRoot (-1) 1 taylorRow1115.q*
          fourPrimeMonomial taylorRow1115.powers x y z b*
            sampleSum 210 (by decide) taylorRow1115.q taylorRow1115.target v := by
  norm_num [source1115,sampleSum,gridIndex,taylorRow1115,fourPrimeMonomial,
    SmallLevelTwentyOne.localRoot,FinitenessRamanujanSum.residues,Finset.sum_filter,Finset.sum_range_succ]
  <;> field_simp [hx,hy,hz,hb] <;> ring
#print axioms taylor_link1115

end SmallLevelTwentyOneLargeGridData
end
end

/-! ## SmallLevelTwentyOneLargeGridWordBundleV4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyOneLargeGridData
open SmallLevelTwentyOneKnownWords SmallLevelTwentyOneFiniteGrid Matrix

def wordRow0 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word01
  source := 0
  target := -5
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 84
  slope := 42
  count := 1
  powers := (2,1,1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word01_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word01_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow0

def wordRow2 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word02
  source := 0
  target := -10
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 21
  slope := 21
  count := 1
  powers := (0,1,1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word02_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word02_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow2

def wordRow6 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 1
  target := -2100
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/2100)
  slope := (1/10)
  count := 1
  powers := (-2,-1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow6

def wordRow7 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 2
  target := -1050
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/525)
  slope := (1/5)
  count := 1
  powers := (0,-1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow7

def wordRow10 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 5
  target := -420
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/84)
  slope := (1/2)
  count := 1
  powers := (-2,-1,-1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow10

def wordRow13 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 10
  target := -210
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/21)
  slope := 1
  count := 1
  powers := (0,-1,-1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow13

def wordRow61 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word03
  source := 208
  target := 1050
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/525)
  slope := (-1/5)
  count := 1
  powers := (0,-1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word03_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word03_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow61

def wordRow62 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word03
  source := 209
  target := 2100
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/2100)
  slope := (-1/10)
  count := 1
  powers := (-2,-1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word03_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word03_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow62

def wordRow123 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word04
  source := 104
  target := -2
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 1
  slope := -105
  count := 0
  powers := (0,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow123

def wordRow124 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word04
  source := 105
  target := 0
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/4)
  slope := (-105/2)
  count := 0
  powers := (-2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow124

def wordRow1 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word01
  source := 105
  target := -4
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (525/4)
  slope := (105/2)
  count := 1
  powers := (-2,1,1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word01_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word01_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow1

def wordRow9 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 4
  target := -525
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (4/525)
  slope := (2/5)
  count := 1
  powers := (2,-1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow9

def wordRow17 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 20
  target := -105
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (4/21)
  slope := 2
  count := 1
  powers := (2,-1,-1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow17

def wordRow30 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 105
  target := -20
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (21/4)
  slope := (21/2)
  count := 1
  powers := (-2,1,1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow30

def wordRow128 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word04
  source := 110
  target := -5
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 4
  slope := 210
  count := 0
  powers := (2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow128

def wordRow18 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 21
  target := -100
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (21/100)
  slope := (21/10)
  count := 1
  powers := (-2,1,1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow18

def wordRow79 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word05
  source := 199
  target := 110
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/100)
  slope := (-21/10)
  count := 0
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word05_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word05_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow79

def wordRow130 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word06
  source := 100
  target := -5
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 4
  slope := -126
  count := 0
  powers := (2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word06_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word06_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow130

def wordRow29 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 100
  target := -21
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (100/21)
  slope := 10
  count := 1
  powers := (2,-1,-1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow29

def wordRow71 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word05
  source := 100
  target := 11
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 100
  slope := -210
  count := 0
  powers := (2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word05_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word05_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow71

def wordRow138 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 10
  target := -19
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 100
  slope := -210
  count := 0
  powers := (2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow138

def wordRow174 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 200
  target := 19
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 100
  slope := 210
  count := 0
  powers := (2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow174

def wordRow16 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 15
  target := -140
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (3/28)
  slope := (3/2)
  count := 1
  powers := (-2,1,-1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow16

def wordRow11 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 6
  target := -350
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (3/175)
  slope := (3/5)
  count := 1
  powers := (0,1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow11

def wordRow26 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 70
  target := -30
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (7/3)
  slope := 7
  count := 1
  powers := (0,-1,1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow26

def wordRow60 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word03
  source := 207
  target := 700
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (3/700)
  slope := (-3/10)
  count := 1
  powers := (-2,1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word03_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word03_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow60

def wordRow122 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word04
  source := 102
  target := -3
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 4
  slope := -210
  count := 0
  powers := (2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow122

def wordRow152 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 120
  target := -30
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 1
  slope := 21
  count := 0
  powers := (0,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow152

def wordRow12 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 7
  target := -300
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (7/300)
  slope := (7/10)
  count := 1
  powers := (-2,-1,1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow12

def wordRow67 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word09
  source := 120
  target := -9
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 100
  slope := -210
  count := 0
  powers := (2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word09_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word09_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow67

def wordRow163 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 98
  target := 70
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/25)
  slope := (-21/5)
  count := 0
  powers := (0,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow163

def wordRow164 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 99
  target := 120
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/100)
  slope := (-21/10)
  count := 0
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow164

def wordRow4 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word02
  source := 140
  target := -6
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (175/3)
  slope := 35
  count := 1
  powers := (0,-1,1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word02_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word02_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow4

def wordRow8 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 3
  target := -700
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (3/700)
  slope := (3/10)
  count := 1
  powers := (-2,1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow8

def wordRow21 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 30
  target := -70
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (3/7)
  slope := 3
  count := 1
  powers := (0,1,-1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow21

def wordRow31 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 140
  target := -15
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (28/3)
  slope := 14
  count := 1
  powers := (2,-1,1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow31

def wordRow127 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word04
  source := 108
  target := -6
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 1
  slope := 105
  count := 0
  powers := (0,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow127

def wordRow129 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word06
  source := 90
  target := -6
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 25
  slope := -315
  count := 0
  powers := (0,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word06_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word06_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow129

def wordRow3 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word02
  source := 90
  target := -7
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (300/7)
  slope := 30
  count := 1
  powers := (2,1,-1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word02_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word02_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow3

def wordRow104 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word10
  source := 9
  target := 90
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/100)
  slope := (-21/10)
  count := 0
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word10_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word10_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow104

def wordRow148 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 111
  target := -120
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/100)
  slope := (21/10)
  count := 0
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow148

def wordRow149 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 112
  target := -70
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/25)
  slope := (21/5)
  count := 0
  powers := (0,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow149

def wordRow103 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word10
  source := 8
  target := 40
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/25)
  slope := (-21/5)
  count := 0
  powers := (0,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word10_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word10_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow103

def wordRow161 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 95
  target := 40
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/4)
  slope := (-21/2)
  count := 0
  powers := (-2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow161

def wordRow179 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word11
  source := 103
  target := 40
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/100)
  slope := (-63/10)
  count := 0
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word11_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word11_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow179

def wordRow68 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word09
  source := 170
  target := -8
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 25
  slope := -105
  count := 0
  powers := (0,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word09_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word09_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow68

def wordRow126 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word04
  source := 107
  target := -8
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/4)
  slope := (105/2)
  count := 0
  powers := (-2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word04_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow126

def wordRow136 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word06
  source := 115
  target := -8
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (25/4)
  slope := (315/2)
  count := 0
  powers := (-2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word06_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word06_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow136

def wordRow14 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 12
  target := -175
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (12/175)
  slope := (6/5)
  count := 1
  powers := (2,1,-1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow14

def wordRow22 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 35
  target := -60
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (7/12)
  slope := (7/2)
  count := 1
  powers := (-2,-1,1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow22

def wordRow32 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 150
  target := -14
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (75/7)
  slope := 15
  count := 1
  powers := (0,1,-1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow32

def wordRow173 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 150
  target := 18
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 25
  slope := 105
  count := 0
  powers := (0,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow173

def wordRow146 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 109
  target := 80
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/100)
  slope := (-21/10)
  count := 0
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow146

def wordRow159 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 80
  target := 25
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 4
  slope := -42
  count := 0
  powers := (2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow159

def wordRow19 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 25
  target := -84
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (25/84)
  slope := (5/2)
  count := 1
  powers := (-2,-1,-1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow19

def wordRow23 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 42
  target := -50
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (21/25)
  slope := (21/5)
  count := 1
  powers := (0,1,1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow23

def wordRow155 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 160
  target := -22
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 25
  slope := 105
  count := 0
  powers := (0,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow155

def wordRow150 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 114
  target := -45
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (4/25)
  slope := (42/5)
  count := 0
  powers := (2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow150

def wordRow25 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 60
  target := -35
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (12/7)
  slope := 6
  count := 1
  powers := (2,1,-1,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow25

def wordRow15 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 14
  target := -150
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (7/75)
  slope := (7/5)
  count := 1
  powers := (0,-1,1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow15

def wordRow33 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 175
  target := -12
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (175/12)
  slope := (35/2)
  count := 1
  powers := (-2,-1,1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow33

def wordRow139 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 60
  target := -18
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 25
  slope := -105
  count := 0
  powers := (0,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow139

def wordRow153 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 130
  target := -25
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 4
  slope := 42
  count := 0
  powers := (2,0,0,0)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow153

def wordRow28 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 84
  target := -25
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (84/25)
  slope := (42/5)
  count := 1
  powers := (2,1,1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow28

def wordRow166 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 101
  target := -80
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (1/100)
  slope := (21/10)
  count := 0
  powers := (-2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow166

def wordRow24 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 50
  target := -42
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (25/21)
  slope := 5
  count := 1
  powers := (0,-1,-1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow24

def wordRow157 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 50
  target := 22
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := 25
  slope := -105
  count := 0
  powers := (0,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow157

def wordRow162 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 96
  target := 45
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (4/25)
  slope := (-42/5)
  count := 0
  powers := (2,0,0,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow162

def wordRow27 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 75
  target := -28
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (75/28)
  slope := (15/2)
  count := 1
  powers := (-2,1,-1,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow27

def wordRow158 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 75
  target := 24
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (25/4)
  slope := (-105/2)
  count := 0
  powers := (-2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow158

def wordRow20 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word00
  source := 28
  target := -75
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (28/75)
  slope := (14/5)
  count := 1
  powers := (2,-1,1,-2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word00_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow20

def wordRow154 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 135
  target := -24
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (25/4)
  slope := (105/2)
  count := 0
  powers := (-2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow154

def wordRow172 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word08
  source := 125
  target := 16
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (25/4)
  slope := (105/2)
  count := 0
  powers := (-2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word08_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow172

def wordRow140 : SmallLevelTwentyOneFiniteGrid.WordCertificate 210 where
  word := word07
  source := 85
  target := -16
  nonaffine := by decide
  denominator := by decide
  closed := by decide
  rate := (25/4)
  slope := (-105/2)
  count := 0
  powers := (-2,0,0,2)
  rate_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalRate,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  slope_eq := by norm_num [SmallLevelTwentyOneFiniteGrid.rationalDerivative,SmallLevelTwentyOneFiniteGrid.integerDen,word07_matrix,Matrix.det_fin_two]
  count_eq := by decide
  powers_eq := by norm_num
#print axioms wordRow140

end SmallLevelTwentyOneLargeGridData
end
end
