module
public meta import SmallLevelCompactRowCommandsV4

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import SmallLevelContinuationTheoryV4
public import SmallLevelSixRootsV1
public import SmallLevelTwentyOneFullHeckeGridV1
public import SmallLevelTwentyOneGridMatrixV1
public import SmallLevelTwentyOneMatrixSystemV1
public import SmallLevelTwentyOneTaylorGridV1

-- Keep the large certificate proofs sequential to bound retained elaboration state.
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option stderrAsMessages false

/-! Consolidated chapter: SmallLevelTwentyOne. Original statements are retained; exact sign normalization reduces eight elimination cases to two. -/

/-! ## SmallLevelTwentyOneLaurentRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix

/-- The explicit Laurent rows in the exact interleaved order of the written
level-21 determinant certificate. Variables E,u,v are the three signs. -/
def laurentRows (E u v X Y Z lam : ℂ) (w : Fin 42 → ℂ) : Fin 42 → ℂ :=
  ![(1)*w 0,
    ((-1)*X^2*Y*Z*E)*w 0 + (1)*w 1,
    ((-1)*X^2*Y*Z*E)*w 0 + (1)*w 41,
    ((-1)*Y*Z*E)*w 0 + (1)*w 2,
    ((-1)*Y*Z*E)*w 0 + (1)*w 40,
    (1)*w 3 + (((-1)*X^2*Z*E)/(Y))*w 14,
    (((-1)*X^2*Z*E)/(Y))*w 28 + (1)*w 39,
    (1)*w 4 + (((-1)*Y*Z*E)/(X^2))*w 21,
    (((-1)*Y*Z*E)/(X^2))*w 21 + (1)*w 38,
    (1)*w 6 + (((-1)*Z*E)/(Y))*w 28,
    (((-1)*Z*E)/(Y))*w 14 + (1)*w 36,
    (1)*w 7 + (((-1)*X^2*Y*E)/(Z))*w 30,
    (((-1)*X^2*Y*E)/(Z))*w 12 + (1)*w 35,
    (1)*w 21,
    ((-1)*Y*Z*E)*w 0 + (1)*w 22,
    ((-1)*Y*Z*E)*w 0 + (1)*w 20,
    (((-1)*Z*E)/(Y))*w 14 + (1)*w 24,
    (1)*w 18 + (((-1)*Z*E)/(Y))*w 28,
    (1)*w 14 + (1)*w 28,
    (X^2*Z*E*u)*w 0 + (1)*w 15 + (X^2*Z*E*u)*w 28 + (1)*w 29,
    (X^2*Z*E*u)*w 0 + (1)*w 13 + (X^2*Z*E*u)*w 14 + (1)*w 27,
    (Z*E*u)*w 0 + (Z*E*u)*w 14 + (1)*w 16 + (1)*w 30,
    (Z*E*u)*w 0 + (1)*w 12 + (1)*w 26 + (Z*E*u)*w 28,
    ((Z*E*u)/(X^2))*w 7 + (1)*w 18 + ((Z*E*u)/(X^2))*w 21 + (1)*w 32,
    (1)*w 10 + ((Z*E*u)/(X^2))*w 21 + (1)*w 24 + ((Z*E*u)/(X^2))*w 35,
    (1)*w 7 + (1)*w 35,
    (Z*E*u)*w 0 + (1)*w 8 + (Z*E*u)*w 28 + (1)*w 36,
    (Z*E*u)*w 0 + (1)*w 6 + (Z*E*u)*w 14 + (1)*w 34,
    (X^2*Y*E*v)*w 0 + (X^2*Y*E*v)*w 6 + (1)*w 7 + (X^2*Y*E*v)*w 12 + (1)*w 13 + (X^2*Y*E*v)*w 18 + (1)*w 19 + (X^2*Y*E*v)*w 24 + (1)*w 25 + (1)*w 31 + (X^2*Y*E*v)*w 36 + (1)*w 37,
    (X^2*Y*E*v)*w 0 + (1)*w 5 + (X^2*Y*E*v)*w 6 + (1)*w 11 + (1)*w 17 + (X^2*Y*E*v)*w 18 + (1)*w 23 + (X^2*Y*E*v)*w 24 + (1)*w 29 + (X^2*Y*E*v)*w 30 + (1)*w 35 + (X^2*Y*E*v)*w 36,
    (Y*E*v)*w 0 + (Y*E*v)*w 6 + (1)*w 8 + (Y*E*v)*w 12 + (1)*w 14 + (Y*E*v)*w 18 + (1)*w 20 + (Y*E*v)*w 24 + (1)*w 26 + (Y*E*v)*w 30 + (1)*w 32 + (1)*w 38,
    ((X^2*E*v)/(Y))*w 2 + ((X^2*E*v)/(Y))*w 8 + (1)*w 9 + ((X^2*E*v)/(Y))*w 14 + (1)*w 15 + ((X^2*E*v)/(Y))*w 20 + (1)*w 21 + ((X^2*E*v)/(Y))*w 26 + (1)*w 27 + ((X^2*E*v)/(Y))*w 32 + (1)*w 33 + (1)*w 39,
    (1)*w 2 + ((-1)*X*lam)*w 4 + (X^2)*w 8 + (1)*w 23,
    (1)*w 3 + ((-1)*X*lam)*w 6 + (X^2)*w 12 + (1)*w 24,
    (1)*w 4 + ((-1)*X*lam)*w 8 + (X^2)*w 16 + (1)*w 25,
    (1)*w 5 + ((-1)*X*lam)*w 10 + (X^2)*w 20 + (1)*w 26,
    (1)*w 6 + ((-1)*X*lam)*w 12 + (X^2)*w 24 + (1)*w 27,
    (1)*w 8 + ((-1)*X*lam)*w 16 + (1)*w 29 + (X^2)*w 32,
    (1)*w 9 + ((-1)*X*lam)*w 18 + (1)*w 30 + (X^2)*w 36,
    (1)*w 10 + ((-1)*X*lam)*w 20 + (1)*w 31 + (X^2)*w 40,
    (X^2)*w 2 + (1)*w 11 + ((-1)*X*lam)*w 22 + (1)*w 32,
    (1)*w 16 + (X^2)*w 22 + ((-1)*X*lam)*w 32 + (1)*w 37]

/-- The polynomial factor of the written determinant. -/
def determinantFactor (E u v X Y Z lam : ℂ) : ℂ :=
  (lam*X+1)*Z*(Y-u)+(E*u*v-1)*X^2*Y*Z-E*u*X^2*Y-u*X^2*Z

end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneKernelCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Shared sign normalization and exact elimination certificates. -/
namespace SmallLevelTwentyOne
open Complex Matrix


compact_certificate
/-- The ramified signs are absorbed into Y and Z; only their product remains. -/
theorem laurentRows_sign_normalize (E u v X Y Z lam : ℂ)
    (hu : u^2=1) (hv : v^2=1) (w : Fin 42 → ℂ) :
    laurentRows (E*u*v) 1 1 X (u*Y) (v*Z) lam w =
      laurentRows E u v X Y Z lam w := by
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hu)
  have hvi : v⁻¹=v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv)
  funext i
  fin_cases i <;>
    norm_num [laurentRows, div_eq_mul_inv, _root_.mul_inv_rev, hui, hvi] <;>
    ring_nf <;> simp [hu,hv]

compact_certificate
theorem determinantFactor_sign_normalize (E u v X Y Z lam : ℂ)
    (hu : u^2=1) (hv : v^2=1) :
    determinantFactor (E*u*v) 1 1 X (u*Y) (v*Z) lam =
      (u*v)*determinantFactor E u v X Y Z lam := by
  unfold determinantFactor
  ring_nf
  simp [hu,hv]
  <;> ring

#print axioms laurentRows_sign_normalize
#print axioms determinantFactor_sign_normalize

compact_certificate
theorem laurent_structure_base_neg (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) 1 1 X Y Z lam w=0) : (determinantFactor (-1) 1 1 X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  have h0_0 : (1)*w 0=0 := by
    have h := congrFun hw (0:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h1_0 : (X^2*Y*Z)*w 0 + (1)*w 1=0 := by
    have h := congrFun hw (1:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h2_0 : (X^2*Y*Z)*w 0 + (1)*w 41=0 := by
    have h := congrFun hw (2:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h3_0 : (Y*Z)*w 0 + (1)*w 2=0 := by
    have h := congrFun hw (3:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h4_0 : (Y*Z)*w 0 + (1)*w 40=0 := by
    have h := congrFun hw (4:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h5_0 : (1)*w 3 + ((X^2*Z)/(Y))*w 14=0 := by
    have h := congrFun hw (5:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h6_0 : ((X^2*Z)/(Y))*w 28 + (1)*w 39=0 := by
    have h := congrFun hw (6:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h7_0 : (1)*w 4 + ((Y*Z)/(X^2))*w 21=0 := by
    have h := congrFun hw (7:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h8_0 : ((Y*Z)/(X^2))*w 21 + (1)*w 38=0 := by
    have h := congrFun hw (8:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h9_0 : (1)*w 6 + ((Z)/(Y))*w 28=0 := by
    have h := congrFun hw (9:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h10_0 : ((Z)/(Y))*w 14 + (1)*w 36=0 := by
    have h := congrFun hw (10:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h11_0 : (1)*w 7 + ((X^2*Y)/(Z))*w 30=0 := by
    have h := congrFun hw (11:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h12_0 : ((X^2*Y)/(Z))*w 12 + (1)*w 35=0 := by
    have h := congrFun hw (12:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h13_0 : (1)*w 21=0 := by
    have h := congrFun hw (13:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h14_0 : (Y*Z)*w 0 + (1)*w 22=0 := by
    have h := congrFun hw (14:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h15_0 : (Y*Z)*w 0 + (1)*w 20=0 := by
    have h := congrFun hw (15:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h16_0 : ((Z)/(Y))*w 14 + (1)*w 24=0 := by
    have h := congrFun hw (16:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h17_0 : (1)*w 18 + ((Z)/(Y))*w 28=0 := by
    have h := congrFun hw (17:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h18_0 : (1)*w 14 + (1)*w 28=0 := by
    have h := congrFun hw (18:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h19_0 : ((-1)*X^2*Z)*w 0 + (1)*w 15 + ((-1)*X^2*Z)*w 28 + (1)*w 29=0 := by
    have h := congrFun hw (19:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h20_0 : ((-1)*X^2*Z)*w 0 + (1)*w 13 + ((-1)*X^2*Z)*w 14 + (1)*w 27=0 := by
    have h := congrFun hw (20:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h21_0 : ((-1)*Z)*w 0 + ((-1)*Z)*w 14 + (1)*w 16 + (1)*w 30=0 := by
    have h := congrFun hw (21:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h22_0 : ((-1)*Z)*w 0 + (1)*w 12 + (1)*w 26 + ((-1)*Z)*w 28=0 := by
    have h := congrFun hw (22:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h23_0 : (((-1)*Z)/(X^2))*w 7 + (1)*w 18 + (((-1)*Z)/(X^2))*w 21 + (1)*w 32=0 := by
    have h := congrFun hw (23:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h24_0 : (1)*w 10 + (((-1)*Z)/(X^2))*w 21 + (1)*w 24 + (((-1)*Z)/(X^2))*w 35=0 := by
    have h := congrFun hw (24:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h25_0 : (1)*w 7 + (1)*w 35=0 := by
    have h := congrFun hw (25:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h26_0 : ((-1)*Z)*w 0 + (1)*w 8 + ((-1)*Z)*w 28 + (1)*w 36=0 := by
    have h := congrFun hw (26:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h27_0 : ((-1)*Z)*w 0 + (1)*w 6 + ((-1)*Z)*w 14 + (1)*w 34=0 := by
    have h := congrFun hw (27:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h28_0 : ((-1)*X^2*Y)*w 0 + ((-1)*X^2*Y)*w 6 + (1)*w 7 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + ((-1)*X^2*Y)*w 18 + (1)*w 19 + ((-1)*X^2*Y)*w 24 + (1)*w 25 + (1)*w 31 + ((-1)*X^2*Y)*w 36 + (1)*w 37=0 := by
    have h := congrFun hw (28:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h29_0 : ((-1)*X^2*Y)*w 0 + (1)*w 5 + ((-1)*X^2*Y)*w 6 + (1)*w 11 + (1)*w 17 + ((-1)*X^2*Y)*w 18 + (1)*w 23 + ((-1)*X^2*Y)*w 24 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + (1)*w 35 + ((-1)*X^2*Y)*w 36=0 := by
    have h := congrFun hw (29:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h30_0 : ((-1)*Y)*w 0 + ((-1)*Y)*w 6 + (1)*w 8 + ((-1)*Y)*w 12 + (1)*w 14 + ((-1)*Y)*w 18 + (1)*w 20 + ((-1)*Y)*w 24 + (1)*w 26 + ((-1)*Y)*w 30 + (1)*w 32 + (1)*w 38=0 := by
    have h := congrFun hw (30:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h31_0 : (((-1)*X^2)/(Y))*w 2 + (((-1)*X^2)/(Y))*w 8 + (1)*w 9 + (((-1)*X^2)/(Y))*w 14 + (1)*w 15 + (((-1)*X^2)/(Y))*w 20 + (1)*w 21 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    have h := congrFun hw (31:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h32_0 : (1)*w 2 + ((-1)*X*lam)*w 4 + (X^2)*w 8 + (1)*w 23=0 := by
    have h := congrFun hw (32:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h33_0 : (1)*w 3 + ((-1)*X*lam)*w 6 + (X^2)*w 12 + (1)*w 24=0 := by
    have h := congrFun hw (33:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h34_0 : (1)*w 4 + ((-1)*X*lam)*w 8 + (X^2)*w 16 + (1)*w 25=0 := by
    have h := congrFun hw (34:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h35_0 : (1)*w 5 + ((-1)*X*lam)*w 10 + (X^2)*w 20 + (1)*w 26=0 := by
    have h := congrFun hw (35:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h36_0 : (1)*w 6 + ((-1)*X*lam)*w 12 + (X^2)*w 24 + (1)*w 27=0 := by
    have h := congrFun hw (36:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h37_0 : (1)*w 8 + ((-1)*X*lam)*w 16 + (1)*w 29 + (X^2)*w 32=0 := by
    have h := congrFun hw (37:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h38_0 : (1)*w 9 + ((-1)*X*lam)*w 18 + (1)*w 30 + (X^2)*w 36=0 := by
    have h := congrFun hw (38:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h39_0 : (1)*w 10 + ((-1)*X*lam)*w 20 + (1)*w 31 + (X^2)*w 40=0 := by
    have h := congrFun hw (39:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h40_0 : (X^2)*w 2 + (1)*w 11 + ((-1)*X*lam)*w 22 + (1)*w 32=0 := by
    have h := congrFun hw (40:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h41_0 : (1)*w 16 + (X^2)*w 22 + ((-1)*X*lam)*w 32 + (1)*w 37=0 := by
    have h := congrFun hw (41:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h7_1 : (1)*w 4=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h7_0-(((Y*Z)/(X^2)))*h13_0
  have h8_1 : (1)*w 38=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h8_0-(((Y*Z)/(X^2)))*h13_0
  have h23_1 : (((-1)*Z)/(X^2))*w 7 + (1)*w 18 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_0-((((-1)*Z)/(X^2)))*h13_0
  have h24_1 : (1)*w 10 + (1)*w 24 + (((-1)*Z)/(X^2))*w 35=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_0-((((-1)*Z)/(X^2)))*h13_0
  have h31_1 : (((-1)*X^2)/(Y))*w 2 + (((-1)*X^2)/(Y))*w 8 + (1)*w 9 + (((-1)*X^2)/(Y))*w 14 + (1)*w 15 + (((-1)*X^2)/(Y))*w 20 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_0-((1))*h13_0
  have h30_1 : ((-1)*Y)*w 0 + ((-1)*Y)*w 6 + (1)*w 8 + ((-1)*Y)*w 12 + (1)*w 14 + ((-1)*Y)*w 18 + (1)*w 20 + ((-1)*Y)*w 24 + (1)*w 26 + ((-1)*Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_0-((1))*h8_1
  have h32_1 : (1)*w 2 + (X^2)*w 8 + (1)*w 23=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h32_0-(((-1)*X*lam))*h7_1
  have h34_1 : ((-1)*X*lam)*w 8 + (X^2)*w 16 + (1)*w 25=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h34_0-((1))*h7_1
  have h1_1 : (1)*w 1=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h1_0-((X^2*Y*Z))*h0_0
  have h2_1 : (1)*w 41=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h2_0-((X^2*Y*Z))*h0_0
  have h3_1 : (1)*w 2=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h3_0-((Y*Z))*h0_0
  have h4_1 : (1)*w 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h4_0-((Y*Z))*h0_0
  have h14_1 : (1)*w 22=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h14_0-((Y*Z))*h0_0
  have h15_1 : (1)*w 20=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h15_0-((Y*Z))*h0_0
  have h19_1 : (1)*w 15 + ((-1)*X^2*Z)*w 28 + (1)*w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h19_0-(((-1)*X^2*Z))*h0_0
  have h20_1 : (1)*w 13 + ((-1)*X^2*Z)*w 14 + (1)*w 27=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h20_0-(((-1)*X^2*Z))*h0_0
  clear h7_0 h8_0 h23_0 h24_0 h31_0 h30_0 h32_0 h34_0 h1_0 h2_0 h3_0 h4_0 h14_0 h15_0 h19_0 h20_0
  have h21_1 : ((-1)*Z)*w 14 + (1)*w 16 + (1)*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_0-(((-1)*Z))*h0_0
  have h22_1 : (1)*w 12 + (1)*w 26 + ((-1)*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h22_0-(((-1)*Z))*h0_0
  have h26_1 : (1)*w 8 + ((-1)*Z)*w 28 + (1)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h26_0-(((-1)*Z))*h0_0
  have h27_1 : (1)*w 6 + ((-1)*Z)*w 14 + (1)*w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h27_0-(((-1)*Z))*h0_0
  have h28_1 : ((-1)*X^2*Y)*w 6 + (1)*w 7 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + ((-1)*X^2*Y)*w 18 + (1)*w 19 + ((-1)*X^2*Y)*w 24 + (1)*w 25 + (1)*w 31 + ((-1)*X^2*Y)*w 36 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_0-(((-1)*X^2*Y))*h0_0
  have h29_1 : (1)*w 5 + ((-1)*X^2*Y)*w 6 + (1)*w 11 + (1)*w 17 + ((-1)*X^2*Y)*w 18 + (1)*w 23 + ((-1)*X^2*Y)*w 24 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + (1)*w 35 + ((-1)*X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_0-(((-1)*X^2*Y))*h0_0
  have h30_2 : ((-1)*Y)*w 6 + (1)*w 8 + ((-1)*Y)*w 12 + (1)*w 14 + ((-1)*Y)*w 18 + (1)*w 20 + ((-1)*Y)*w 24 + (1)*w 26 + ((-1)*Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_1-(((-1)*Y))*h0_0
  have h39_1 : (1)*w 10 + ((-1)*X*lam)*w 20 + (1)*w 31=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h39_0-((X^2))*h4_1
  have h40_1 : (X^2)*w 2 + (1)*w 11 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h40_0-(((-1)*X*lam))*h14_1
  have h41_1 : (1)*w 16 + ((-1)*X*lam)*w 32 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h41_0-((X^2))*h14_1
  have h31_2 : (((-1)*X^2)/(Y))*w 8 + (1)*w 9 + (((-1)*X^2)/(Y))*w 14 + (1)*w 15 + (((-1)*X^2)/(Y))*w 20 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_1-((((-1)*X^2)/(Y)))*h3_1
  have h32_2 : (X^2)*w 8 + (1)*w 23=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h32_1-((1))*h3_1
  have h40_2 : (1)*w 11 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h40_1-((X^2))*h3_1
  have h30_3 : ((-1)*Y)*w 6 + (1)*w 8 + ((-1)*Y)*w 12 + (1)*w 14 + ((-1)*Y)*w 18 + ((-1)*Y)*w 24 + (1)*w 26 + ((-1)*Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_2-((1))*h15_1
  have h31_3 : (((-1)*X^2)/(Y))*w 8 + (1)*w 9 + (((-1)*X^2)/(Y))*w 14 + (1)*w 15 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_2-((((-1)*X^2)/(Y)))*h15_1
  have h35_1 : (1)*w 5 + ((-1)*X*lam)*w 10 + (1)*w 26=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h35_0-((X^2))*h15_1
  clear h21_0 h22_0 h26_0 h27_0 h28_0 h29_0 h30_1 h39_0 h40_0 h41_0 h31_1 h32_1 h40_1 h30_2 h31_2 h35_0
  have h39_2 : (1)*w 10 + (1)*w 31=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h39_1-(((-1)*X*lam))*h15_1
  have h33_1 : ((-1)*X*lam)*w 6 + (X^2)*w 12 + (((-1)*X^2*Z)/(Y))*w 14 + (1)*w 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_0-((1))*h5_0
  have h31_4 : (((-1)*X^2)/(Y))*w 8 + (1)*w 9 + (((-1)*X^2)/(Y))*w 14 + (1)*w 15 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + (((-1)*X^2*Z)/(Y))*w 28 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_3-((1))*h6_0
  have h29_2 : (1)*w 5 + ((-1)*X^2*Y)*w 6 + ((-1)*X^2)*w 8 + (1)*w 11 + (1)*w 17 + ((-1)*X^2*Y)*w 18 + ((-1)*X^2*Y)*w 24 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + (1)*w 35 + ((-1)*X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_1-((1))*h32_2
  have h28_2 : ((-1)*X^2*Y)*w 6 + (1)*w 7 + ((-1))*w 10 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + ((-1)*X^2*Y)*w 18 + (1)*w 19 + ((-1)*X^2*Y)*w 24 + (1)*w 25 + ((-1)*X^2*Y)*w 36 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_1-((1))*h39_2
  have h29_3 : (1)*w 5 + ((-1)*X^2*Y)*w 6 + ((-1)*X^2)*w 8 + (1)*w 17 + ((-1)*X^2*Y)*w 18 + ((-1)*X^2*Y)*w 24 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + ((-1))*w 32 + (1)*w 35 + ((-1)*X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_2-((1))*h40_2
  have h23_2 : (1)*w 18 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_1-((((-1)*Z)/(X^2)))*h11_0
  have h25_1 : (((-1)*X^2*Y)/(Z))*w 30 + (1)*w 35=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h25_0-((1))*h11_0
  have h28_3 : ((-1)*X^2*Y)*w 6 + ((-1))*w 10 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + ((-1)*X^2*Y)*w 18 + (1)*w 19 + ((-1)*X^2*Y)*w 24 + (1)*w 25 + (((-1)*X^2*Y)/(Z))*w 30 + ((-1)*X^2*Y)*w 36 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_2-((1))*h11_0
  have h24_2 : (1)*w 10 + (Y)*w 12 + (1)*w 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_1-((((-1)*Z)/(X^2)))*h12_0
  have h25_2 : (((-1)*X^2*Y)/(Z))*w 12 + (((-1)*X^2*Y)/(Z))*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h25_1-((1))*h12_0
  have h29_4 : (1)*w 5 + ((-1)*X^2*Y)*w 6 + ((-1)*X^2)*w 8 + (((-1)*X^2*Y)/(Z))*w 12 + (1)*w 17 + ((-1)*X^2*Y)*w 18 + ((-1)*X^2*Y)*w 24 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + ((-1))*w 32 + ((-1)*X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_3-((1))*h12_0
  have h26_2 : (1)*w 8 + (((-1)*Z)/(Y))*w 14 + ((-1)*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h26_1-((1))*h10_0
  have h28_4 : ((-1)*X^2*Y)*w 6 + ((-1))*w 10 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + (X^2*Z)*w 14 + ((-1)*X^2*Y)*w 18 + (1)*w 19 + ((-1)*X^2*Y)*w 24 + (1)*w 25 + (((-1)*X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_3-(((-1)*X^2*Y))*h10_0
  have h29_5 : (1)*w 5 + ((-1)*X^2*Y)*w 6 + ((-1)*X^2)*w 8 + (((-1)*X^2*Y)/(Z))*w 12 + (X^2*Z)*w 14 + (1)*w 17 + ((-1)*X^2*Y)*w 18 + ((-1)*X^2*Y)*w 24 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_4-(((-1)*X^2*Y))*h10_0
  have h38_1 : (1)*w 9 + (((-1)*X^2*Z)/(Y))*w 14 + ((-1)*X*lam)*w 18 + (1)*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_0-((X^2))*h10_0
  clear h39_1 h33_0 h31_3 h29_1 h28_1 h29_2 h23_1 h25_0 h28_2 h24_1 h25_1 h29_3 h26_1 h28_3 h29_4 h38_0
  have h23_3 : (((-1)*Z)/(Y))*w 28 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_2-((1))*h17_0
  have h28_5 : ((-1)*X^2*Y)*w 6 + ((-1))*w 10 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + (X^2*Z)*w 14 + (1)*w 19 + ((-1)*X^2*Y)*w 24 + (1)*w 25 + (X^2*Z)*w 28 + (((-1)*X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_4-(((-1)*X^2*Y))*h17_0
  have h29_6 : (1)*w 5 + ((-1)*X^2*Y)*w 6 + ((-1)*X^2)*w 8 + (((-1)*X^2*Y)/(Z))*w 12 + (X^2*Z)*w 14 + (1)*w 17 + ((-1)*X^2*Y)*w 24 + (X^2*Z)*w 28 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_5-(((-1)*X^2*Y))*h17_0
  have h30_4 : ((-1)*Y)*w 6 + (1)*w 8 + ((-1)*Y)*w 12 + (1)*w 14 + ((-1)*Y)*w 24 + (1)*w 26 + (Z)*w 28 + ((-1)*Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_3-(((-1)*Y))*h17_0
  have h38_2 : (1)*w 9 + (((-1)*X^2*Z)/(Y))*w 14 + ((X*Z*lam)/(Y))*w 28 + (1)*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_1-(((-1)*X*lam))*h17_0
  have h27_2 : ((-1)*Z)*w 14 + (((-1)*Z)/(Y))*w 28 + (1)*w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h27_1-((1))*h9_0
  have h28_6 : ((-1))*w 10 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + (X^2*Z)*w 14 + (1)*w 19 + ((-1)*X^2*Y)*w 24 + (1)*w 25 + (2*X^2*Z)*w 28 + (((-1)*X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_5-(((-1)*X^2*Y))*h9_0
  have h29_7 : (1)*w 5 + ((-1)*X^2)*w 8 + (((-1)*X^2*Y)/(Z))*w 12 + (X^2*Z)*w 14 + (1)*w 17 + ((-1)*X^2*Y)*w 24 + (2*X^2*Z)*w 28 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_6-(((-1)*X^2*Y))*h9_0
  have h30_5 : (1)*w 8 + ((-1)*Y)*w 12 + (1)*w 14 + ((-1)*Y)*w 24 + (1)*w 26 + (2*Z)*w 28 + ((-1)*Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_4-(((-1)*Y))*h9_0
  have h33_2 : (X^2)*w 12 + (((-1)*X^2*Z)/(Y))*w 14 + (1)*w 24 + ((X*Z*lam)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_1-(((-1)*X*lam))*h9_0
  have h36_1 : ((-1)*X*lam)*w 12 + (X^2)*w 24 + (1)*w 27 + (((-1)*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_0-((1))*h9_0
  have h24_3 : (1)*w 10 + (Y)*w 12 + (((-1)*Z)/(Y))*w 14=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_2-((1))*h16_0
  have h28_7 : ((-1))*w 10 + ((-1)*X^2*Y)*w 12 + (1)*w 13 + (2*X^2*Z)*w 14 + (1)*w 19 + (1)*w 25 + (2*X^2*Z)*w 28 + (((-1)*X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_6-(((-1)*X^2*Y))*h16_0
  have h29_8 : (1)*w 5 + ((-1)*X^2)*w 8 + (((-1)*X^2*Y)/(Z))*w 12 + (2*X^2*Z)*w 14 + (1)*w 17 + (2*X^2*Z)*w 28 + (1)*w 29 + ((-1)*X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_7-(((-1)*X^2*Y))*h16_0
  have h30_6 : (1)*w 8 + ((-1)*Y)*w 12 + (1 + Z)*w 14 + (1)*w 26 + (2*Z)*w 28 + ((-1)*Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_5-(((-1)*Y))*h16_0
  have h33_3 : (X^2)*w 12 + (((-1)*Z)/(Y) + ((-1)*X^2*Z)/(Y))*w 14 + ((X*Z*lam)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_2-((1))*h16_0
  clear h23_2 h28_4 h29_5 h30_3 h38_1 h27_1 h28_5 h29_6 h30_4 h33_1 h36_0 h24_2 h28_6 h29_7 h30_5 h33_2
  have h36_2 : ((-1)*X*lam)*w 12 + (((-1)*X^2*Z)/(Y))*w 14 + (1)*w 27 + (((-1)*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_1-((X^2))*h16_0
  have h21_2 : ((-1))*w 12 + ((-1)*Z)*w 14 + (1)*w 16=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_1-((((-1)*Z)/(X^2*Y)))*h25_2
  have h23_4 : ((-1)*Y)*w 12 + (((-1)*Z)/(Y))*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_3-((((-1)*Z)/(X^2)))*h25_2
  have h28_8 : ((-1))*w 10 + ((X^2*Y)/(Z) + (-1)*X^2*Y)*w 12 + (1)*w 13 + (2*X^2*Z)*w 14 + (1)*w 19 + (1)*w 25 + (2*X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_7-((1))*h25_2
  have h29_9 : (1)*w 5 + ((-1)*X^2)*w 8 + (((-1)*X^2*Y)/(Z) + X^2*Y)*w 12 + (2*X^2*Z)*w 14 + (1)*w 17 + (2*X^2*Z)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_8-((Z))*h25_2
  have h30_7 : (1)*w 8 + (1 + Z)*w 14 + (1)*w 26 + (2*Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_6-(((Z)/(X^2)))*h25_2
  have h38_3 : (1)*w 9 + ((-1))*w 12 + (((-1)*X^2*Z)/(Y))*w 14 + ((X*Z*lam)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_2-((((-1)*Z)/(X^2*Y)))*h25_2
  have h20_2 : (1)*w 13 + (1)*w 27 + (X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h20_1-(((-1)*X^2*Z))*h18_0
  have h21_3 : ((-1))*w 12 + (1)*w 16 + (Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_2-(((-1)*Z))*h18_0
  have h24_4 : (1)*w 10 + (Y)*w 12 + ((Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_3-((((-1)*Z)/(Y)))*h18_0
  have h26_3 : (1)*w 8 + ((Z)/(Y) + (-1)*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h26_2-((((-1)*Z)/(Y)))*h18_0
  have h27_3 : (((-1)*Z)/(Y) + Z)*w 28 + (1)*w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h27_2-(((-1)*Z))*h18_0
  have h28_9 : ((-1))*w 10 + ((X^2*Y)/(Z) + (-1)*X^2*Y)*w 12 + (1)*w 13 + (1)*w 19 + (1)*w 25 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_8-((2*X^2*Z))*h18_0
  have h29_10 : (1)*w 5 + ((-1)*X^2)*w 8 + (((-1)*X^2*Y)/(Z) + X^2*Y)*w 12 + (1)*w 17 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_9-((2*X^2*Z))*h18_0
  have h30_8 : (1)*w 8 + (1)*w 26 + ((-1) + Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_7-((1 + Z))*h18_0
  have h31_5 : (((-1)*X^2)/(Y))*w 8 + (1)*w 9 + (1)*w 15 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + ((X^2)/(Y) + ((-1)*X^2*Z)/(Y))*w 28 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_4-((((-1)*X^2)/(Y)))*h18_0
  clear h36_1 h21_1 h23_3 h28_7 h29_8 h30_6 h38_2 h20_1 h21_2 h24_3 h26_2 h27_2 h28_8 h29_9 h30_7 h31_4
  have h33_4 : (X^2)*w 12 + ((Z)/(Y) + (X*Z*lam)/(Y) + (X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_3-((((-1)*Z)/(Y) + ((-1)*X^2*Z)/(Y)))*h18_0
  have h36_3 : ((-1)*X*lam)*w 12 + (1)*w 27 + (((-1)*Z)/(Y) + (X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_2-((((-1)*X^2*Z)/(Y)))*h18_0
  have h38_4 : (1)*w 9 + ((-1))*w 12 + ((X*Z*lam)/(Y) + (X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_3-((((-1)*X^2*Z)/(Y)))*h18_0
  have h29_11 : (1)*w 5 + (((-1)*X^2*Y)/(Z) + X^2*Y)*w 12 + (1)*w 17 + ((X^2*Z)/(Y) + (-1)*X^2*Z)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_10-(((-1)*X^2))*h26_3
  have h30_9 : (1)*w 26 + (((-1)*Z)/(Y) + (-1) + 2*Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_8-((1))*h26_3
  have h31_6 : (1)*w 9 + (1)*w 15 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + ((X^2*Z)/(Y^2) + (X^2)/(Y) + ((-2)*X^2*Z)/(Y))*w 28 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_5-((((-1)*X^2)/(Y)))*h26_3
  have h34_2 : (X^2)*w 16 + (1)*w 25 + ((X*Z*lam)/(Y) + (-1)*X*Z*lam)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h34_1-(((-1)*X*lam))*h26_3
  have h37_1 : ((-1)*X*lam)*w 16 + (((-1)*Z)/(Y) + Z)*w 28 + (1)*w 29 + (X^2)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h37_0-((1))*h26_3
  have h21_4 : (1)*w 16 + ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + (Z)/(Y) + Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_3-((((-1))/(X^2)))*h33_4
  have h22_2 : (1)*w 26 + (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (-1)*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h22_1-(((1)/(X^2)))*h33_4
  have h23_5 : ((Z)/(X^2) + (Z*lam)/(X) + ((-1)*Z)/(Y) + Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_4-((((-1)*Y)/(X^2)))*h33_4
  have h24_5 : (1)*w 10 + (((-1)*Z)/(X^2) + ((-1)*Z*lam)/(X) + (Z)/(Y) + (-1)*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_4-(((Y)/(X^2)))*h33_4
  have h28_10 : ((-1))*w 10 + (1)*w 13 + (1)*w 19 + (1)*w 25 + ((-1) + Z + (-1)*X*lam + X*Z*lam + (-1)*X^2 + X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_9-(((Y)/(Z) + (-1)*Y))*h33_4
  have h29_12 : (1)*w 5 + (1)*w 17 + (1 + (-1)*Z + X*lam + (-1)*X*Z*lam + (X^2*Z)/(Y) + X^2 + (-2)*X^2*Z)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_11-((((-1)*Y)/(Z) + Y))*h33_4
  have h36_4 : (1)*w 27 + ((Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (Z*lam^2)/(Y) + (X*Z*lam)/(Y) + (X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_3-((((-1)*lam)/(X)))*h33_4
  have h38_5 : (1)*w 9 + ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + (Z)/(Y) + (X*Z*lam)/(Y) + (X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_4-((((-1))/(X^2)))*h33_4
  clear h33_3 h36_2 h38_3 h29_10 h30_8 h31_5 h34_1 h37_0 h21_3 h22_1 h23_4 h24_4 h28_9 h29_11 h36_3 h38_4
  have h31_7 : (1)*w 15 + (((-1)*X^2)/(Y))*w 26 + (1)*w 27 + (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + ((-1)*Z)/(Y) + ((-1)*X*Z*lam)/(Y) + (X^2*Z)/(Y^2) + (X^2)/(Y) + ((-3)*X^2*Z)/(Y))*w 28 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_6-((1))*h38_5
  have h28_11 : (1)*w 13 + (1)*w 19 + (1)*w 25 + (((-1)*Z)/(X^2) + ((-1)*Z*lam)/(X) + (Z)/(Y) + (-1) + (-1)*X*lam + X*Z*lam + (-1)*X^2 + X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_10-(((-1)))*h24_5
  have h35_2 : (1)*w 5 + (1)*w 26 + (((-1)*Z*lam)/(X) + (-1)*Z*lam^2 + (X*Z*lam)/(Y) + (-1)*X*Z*lam)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h35_1-(((-1)*X*lam))*h24_5
  have h20_3 : (1)*w 13 + (((-1)*Z*lam)/(X*Y) + (Z)/(Y) + ((-1)*Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y) + X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h20_2-((1))*h36_4
  have h31_8 : (1)*w 15 + (((-1)*X^2)/(Y))*w 26 + (((-1)*Z)/(X^2*Y) + ((-2)*Z*lam)/(X*Y) + ((-1)*Z*lam^2)/(Y) + ((-2)*X*Z*lam)/(Y) + (X^2*Z)/(Y^2) + (X^2)/(Y) + ((-4)*X^2*Z)/(Y))*w 28 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_7-((1))*h36_4
  have h28_12 : (1)*w 19 + (1)*w 25 + (((-1)*Z)/(X^2) + (Z*lam)/(X*Y) + ((-1)*Z*lam)/(X) + (Z*lam^2)/(Y) + (-1) + (X*Z*lam)/(Y) + (-1)*X*lam + X*Z*lam + (X^2*Z)/(Y) + (-1)*X^2)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_11-((1))*h20_3
  have h34_3 : (1)*w 25 + (((-1)*Z)/(Y) + (-1)*X*Z*lam + ((-1)*X^2*Z)/(Y) + (-1)*X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h34_2-((X^2))*h21_4
  have h37_2 : ((Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (Z*lam^2)/(Y) + Z + (X*Z*lam)/(Y) + X*Z*lam)*w 28 + (1)*w 29 + (X^2)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h37_1-(((-1)*X*lam))*h21_4
  have h41_2 : (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (-1)*Z)*w 28 + ((-1)*X*lam)*w 32 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h41_1-((1))*h21_4
  have h28_13 : (1)*w 19 + (((-1)*Z)/(X^2) + (Z*lam)/(X*Y) + ((-1)*Z*lam)/(X) + (Z)/(Y) + (Z*lam^2)/(Y) + (-1) + (X*Z*lam)/(Y) + (-1)*X*lam + 2*X*Z*lam + (2*X^2*Z)/(Y) + (-1)*X^2 + X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_12-((1))*h34_3
  have h30_10 : ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + (-1) + 3*Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_9-((1))*h22_2
  have h31_9 : (1)*w 15 + (((-1)*Z)/(X^2*Y) + ((-2)*Z*lam)/(X*Y) + ((-1)*Z)/(Y^2) + ((-1)*Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y^2) + ((-2)*X*Z*lam)/(Y) + (X^2)/(Y) + ((-5)*X^2*Z)/(Y))*w 28 + (((-1)*X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_8-((((-1)*X^2)/(Y)))*h22_2
  have h35_3 : (1)*w 5 + ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + ((-1)*Z*lam)/(X) + (Z)/(Y) + Z + (-1)*Z*lam^2 + (X*Z*lam)/(Y) + (-1)*X*Z*lam)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h35_2-((1))*h22_2
  have h29_13 : (1)*w 17 + (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + (Z*lam)/(X) + ((-1)*Z)/(Y) + 1 + (-2)*Z + Z*lam^2 + ((-1)*X*Z*lam)/(Y) + X*lam + (X^2*Z)/(Y) + X^2 + (-2)*X^2*Z)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_12-((1))*h35_3
  have h29_14 : (1)*w 17 + (((-1)*Z)/(X^2*Y) + (Z)/(X^2) + ((-1)*Z*lam)/(X*Y) + (2*Z*lam)/(X) + ((-2)*Z)/(Y) + 1 + (-1)*Z + Z*lam^2 + ((-1)*X*Z*lam)/(Y) + X*lam + (X^2*Z)/(Y) + X^2 + (-2)*X^2*Z)*w 28 + (1)*w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_13-(((-1)))*h23_5
  have h30_11 : ((Z)/(X^2*Y) + ((-1)*Z)/(X^2) + (Z*lam)/(X*Y) + ((-1)*Z*lam)/(X) + (Z)/(Y) + (-1) + 2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_10-((1))*h23_5
  clear h31_6 h28_10 h35_1 h20_2 h31_7 h28_11 h34_2 h37_1 h41_1 h28_12 h30_9 h31_8 h35_2 h29_12 h29_13 h30_10
  have h31_10 : (1)*w 15 + (((-1)*Z)/(X^2*Y) + ((-2)*Z*lam)/(X*Y) + ((-1)*Z)/(Y^2) + (Z)/(Y) + ((-1)*Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y^2) + ((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y^2) + (X^2)/(Y) + ((-4)*X^2*Z)/(Y))*w 28 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_9-((((-1)*X^2)/(Y)))*h23_5
  have h37_3 : ((Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (Z*lam^2)/(Y) + (X*Z*lam)/(Y) + (X^2*Z)/(Y) + (-1)*X^2*Z)*w 28 + (1)*w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h37_2-((X^2))*h23_5
  have h41_3 : (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + (Z*lam)/(X) + ((-1)*Z)/(Y) + (-1)*Z + Z*lam^2 + ((-1)*X*Z*lam)/(Y) + X*Z*lam)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h41_2-(((-1)*X*lam))*h23_5
  have h28_14 : (1)*w 19 + ((Z)/(X^2*Y) + ((-1)*Z)/(X^2) + (2*Z*lam)/(X*Y) + ((-2)*Z*lam)/(X) + (2*Z)/(Y) + (Z*lam^2)/(Y) + (-1) + Z + (-1)*Z*lam^2 + (2*X*Z*lam)/(Y) + (-1)*X*lam + X*Z*lam + (2*X^2*Z)/(Y) + (-1)*X^2 + X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_13-((1))*h41_3
  have h19_2 : (1)*w 15 + (((-1)*Z*lam)/(X*Y) + (Z)/(Y) + ((-1)*Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h19_1-((1))*h37_3
  have h29_15 : (1)*w 17 + (((-1)*Z)/(X^2*Y) + (Z)/(X^2) + ((-2)*Z*lam)/(X*Y) + (2*Z*lam)/(X) + ((-1)*Z)/(Y) + ((-1)*Z*lam^2)/(Y) + 1 + (-1)*Z + Z*lam^2 + ((-2)*X*Z*lam)/(Y) + X*lam + X^2 + (-1)*X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_14-((1))*h37_3
  have h31_11 : (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + ((-1)*Z)/(Y^2) + ((-1)*X*Z*lam)/(Y^2) + ((-1)*X^2*Z)/(Y^2) + (X^2)/(Y) + ((-3)*X^2*Z)/(Y))*w 28 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_10-((1))*h19_2
  have hd : determinantFactor (-1) 1 1 X Y Z lam*w 28=0 := by
    unfold determinantFactor
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (((-1)*X^2*Y))*h30_11
  refine ⟨hd, ?_⟩
  intro hz28
  simp only [hz28] at h31_11
  have hz33 : w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h31_11
  simp only [hz28] at h19_2
  have hz15 : w 15=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h19_2
  simp only [hz28] at h29_15
  have hz17 : w 17=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h29_15
  simp only [hz28] at h37_3
  have hz29 : w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h37_3
  simp only [hz28] at h28_14
  have hz19 : w 19=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h28_14
  simp only [hz28] at h41_3
  have hz37 : w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h41_3
  simp only [hz28] at h23_5
  have hz32 : w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h23_5
  simp only [hz28] at h35_3
  have hz5 : w 5=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h35_3
  clear h31_9 h37_2 h41_2 h28_13 h19_1 h29_14 h31_10 h30_11 h31_11 h19_2 h29_15 h37_3 h28_14 h41_3 h23_5 h35_3
  simp only [hz28] at h22_2
  have hz26 : w 26=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h22_2
  simp only [hz28] at h34_3
  have hz25 : w 25=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h34_3
  simp only [hz28] at h21_4
  have hz16 : w 16=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h21_4
  simp only [hz28] at h20_3
  have hz13 : w 13=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h20_3
  simp only [hz28] at h36_4
  have hz27 : w 27=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h36_4
  simp only [hz28] at h24_5
  have hz10 : w 10=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h24_5
  simp only [hz28] at h38_5
  have hz9 : w 9=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h38_5
  simp only [hz28] at h33_4
  have hz12 : w 12=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (((1)/(X^2)))*h33_4
  simp only [hz28] at h26_3
  have hz8 : w 8=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h26_3
  simp only [hz28] at h27_3
  have hz34 : w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h27_3
  simp only [hz28] at h18_0
  have hz14 : w 14=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h18_0
  simp only [hz12] at h25_2
  have hz30 : w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((((-1)*Z)/(X^2*Y)))*h25_2
  simp only [hz14] at h16_0
  have hz24 : w 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h16_0
  simp only [hz28] at h9_0
  have hz6 : w 6=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h9_0
  simp only [hz28] at h17_0
  have hz18 : w 18=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h17_0
  simp only [hz14] at h10_0
  have hz36 : w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h10_0
  clear h22_2 h34_3 h21_4 h20_3 h36_4 h24_5 h38_5 h33_4 h26_3 h27_3 h18_0 h25_2 h16_0 h9_0 h17_0 h10_0
  simp only [hz12] at h12_0
  have hz35 : w 35=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h12_0
  simp only [hz30] at h11_0
  have hz7 : w 7=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h11_0
  simp only [hz32] at h40_2
  have hz11 : w 11=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h40_2
  simp only [hz10] at h39_2
  have hz31 : w 31=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h39_2
  simp only [hz8] at h32_2
  have hz23 : w 23=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h32_2
  simp only [hz28] at h6_0
  have hz39 : w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h6_0
  simp only [hz14] at h5_0
  have hz3 : w 3=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h5_0
  have hz20 : w 20=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h15_1
  have hz2 : w 2=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h3_1
  have hz22 : w 22=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h14_1
  have hz40 : w 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h4_1
  have hz41 : w 41=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h2_1
  have hz1 : w 1=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h1_1
  have hz0 : w 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h0_0
  have hz4 : w 4=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h7_1
  have hz38 : w 38=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h8_1
  clear h12_0 h11_0 h40_2 h39_2 h32_2 h6_0 h5_0 h15_1 h3_1 h14_1 h4_1 h2_1 h1_1 h0_0 h7_1 h8_1
  have hz21 : w 21=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h13_0
  clear h13_0
  funext j
  fin_cases j <;> assumption

#print axioms laurent_structure_base_neg

compact_certificate
theorem laurent_structure_base_pos (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 1 1 X Y Z lam w=0) : (determinantFactor 1 1 1 X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  have h0_0 : (1)*w 0=0 := by
    have h := congrFun hw (0:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h1_0 : ((-1)*X^2*Y*Z)*w 0 + (1)*w 1=0 := by
    have h := congrFun hw (1:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h2_0 : ((-1)*X^2*Y*Z)*w 0 + (1)*w 41=0 := by
    have h := congrFun hw (2:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h3_0 : ((-1)*Y*Z)*w 0 + (1)*w 2=0 := by
    have h := congrFun hw (3:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h4_0 : ((-1)*Y*Z)*w 0 + (1)*w 40=0 := by
    have h := congrFun hw (4:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h5_0 : (1)*w 3 + (((-1)*X^2*Z)/(Y))*w 14=0 := by
    have h := congrFun hw (5:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h6_0 : (((-1)*X^2*Z)/(Y))*w 28 + (1)*w 39=0 := by
    have h := congrFun hw (6:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h7_0 : (1)*w 4 + (((-1)*Y*Z)/(X^2))*w 21=0 := by
    have h := congrFun hw (7:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h8_0 : (((-1)*Y*Z)/(X^2))*w 21 + (1)*w 38=0 := by
    have h := congrFun hw (8:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h9_0 : (1)*w 6 + (((-1)*Z)/(Y))*w 28=0 := by
    have h := congrFun hw (9:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h10_0 : (((-1)*Z)/(Y))*w 14 + (1)*w 36=0 := by
    have h := congrFun hw (10:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h11_0 : (1)*w 7 + (((-1)*X^2*Y)/(Z))*w 30=0 := by
    have h := congrFun hw (11:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h12_0 : (((-1)*X^2*Y)/(Z))*w 12 + (1)*w 35=0 := by
    have h := congrFun hw (12:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h13_0 : (1)*w 21=0 := by
    have h := congrFun hw (13:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h14_0 : ((-1)*Y*Z)*w 0 + (1)*w 22=0 := by
    have h := congrFun hw (14:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h15_0 : ((-1)*Y*Z)*w 0 + (1)*w 20=0 := by
    have h := congrFun hw (15:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h16_0 : (((-1)*Z)/(Y))*w 14 + (1)*w 24=0 := by
    have h := congrFun hw (16:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h17_0 : (1)*w 18 + (((-1)*Z)/(Y))*w 28=0 := by
    have h := congrFun hw (17:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h18_0 : (1)*w 14 + (1)*w 28=0 := by
    have h := congrFun hw (18:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h19_0 : (X^2*Z)*w 0 + (1)*w 15 + (X^2*Z)*w 28 + (1)*w 29=0 := by
    have h := congrFun hw (19:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h20_0 : (X^2*Z)*w 0 + (1)*w 13 + (X^2*Z)*w 14 + (1)*w 27=0 := by
    have h := congrFun hw (20:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h21_0 : (Z)*w 0 + (Z)*w 14 + (1)*w 16 + (1)*w 30=0 := by
    have h := congrFun hw (21:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h22_0 : (Z)*w 0 + (1)*w 12 + (1)*w 26 + (Z)*w 28=0 := by
    have h := congrFun hw (22:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h23_0 : ((Z)/(X^2))*w 7 + (1)*w 18 + ((Z)/(X^2))*w 21 + (1)*w 32=0 := by
    have h := congrFun hw (23:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h24_0 : (1)*w 10 + ((Z)/(X^2))*w 21 + (1)*w 24 + ((Z)/(X^2))*w 35=0 := by
    have h := congrFun hw (24:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h25_0 : (1)*w 7 + (1)*w 35=0 := by
    have h := congrFun hw (25:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h26_0 : (Z)*w 0 + (1)*w 8 + (Z)*w 28 + (1)*w 36=0 := by
    have h := congrFun hw (26:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h27_0 : (Z)*w 0 + (1)*w 6 + (Z)*w 14 + (1)*w 34=0 := by
    have h := congrFun hw (27:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h28_0 : (X^2*Y)*w 0 + (X^2*Y)*w 6 + (1)*w 7 + (X^2*Y)*w 12 + (1)*w 13 + (X^2*Y)*w 18 + (1)*w 19 + (X^2*Y)*w 24 + (1)*w 25 + (1)*w 31 + (X^2*Y)*w 36 + (1)*w 37=0 := by
    have h := congrFun hw (28:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h29_0 : (X^2*Y)*w 0 + (1)*w 5 + (X^2*Y)*w 6 + (1)*w 11 + (1)*w 17 + (X^2*Y)*w 18 + (1)*w 23 + (X^2*Y)*w 24 + (1)*w 29 + (X^2*Y)*w 30 + (1)*w 35 + (X^2*Y)*w 36=0 := by
    have h := congrFun hw (29:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h30_0 : (Y)*w 0 + (Y)*w 6 + (1)*w 8 + (Y)*w 12 + (1)*w 14 + (Y)*w 18 + (1)*w 20 + (Y)*w 24 + (1)*w 26 + (Y)*w 30 + (1)*w 32 + (1)*w 38=0 := by
    have h := congrFun hw (30:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h31_0 : ((X^2)/(Y))*w 2 + ((X^2)/(Y))*w 8 + (1)*w 9 + ((X^2)/(Y))*w 14 + (1)*w 15 + ((X^2)/(Y))*w 20 + (1)*w 21 + ((X^2)/(Y))*w 26 + (1)*w 27 + ((X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    have h := congrFun hw (31:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h32_0 : (1)*w 2 + ((-1)*X*lam)*w 4 + (X^2)*w 8 + (1)*w 23=0 := by
    have h := congrFun hw (32:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h33_0 : (1)*w 3 + ((-1)*X*lam)*w 6 + (X^2)*w 12 + (1)*w 24=0 := by
    have h := congrFun hw (33:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h34_0 : (1)*w 4 + ((-1)*X*lam)*w 8 + (X^2)*w 16 + (1)*w 25=0 := by
    have h := congrFun hw (34:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h35_0 : (1)*w 5 + ((-1)*X*lam)*w 10 + (X^2)*w 20 + (1)*w 26=0 := by
    have h := congrFun hw (35:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h36_0 : (1)*w 6 + ((-1)*X*lam)*w 12 + (X^2)*w 24 + (1)*w 27=0 := by
    have h := congrFun hw (36:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h37_0 : (1)*w 8 + ((-1)*X*lam)*w 16 + (1)*w 29 + (X^2)*w 32=0 := by
    have h := congrFun hw (37:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h38_0 : (1)*w 9 + ((-1)*X*lam)*w 18 + (1)*w 30 + (X^2)*w 36=0 := by
    have h := congrFun hw (38:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h39_0 : (1)*w 10 + ((-1)*X*lam)*w 20 + (1)*w 31 + (X^2)*w 40=0 := by
    have h := congrFun hw (39:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h40_0 : (X^2)*w 2 + (1)*w 11 + ((-1)*X*lam)*w 22 + (1)*w 32=0 := by
    have h := congrFun hw (40:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h41_0 : (1)*w 16 + (X^2)*w 22 + ((-1)*X*lam)*w 32 + (1)*w 37=0 := by
    have h := congrFun hw (41:Fin 42)
    reduce_compact_row at h
    norm_num at h ⊢
    exact h
  have h7_1 : (1)*w 4=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h7_0-((((-1)*Y*Z)/(X^2)))*h13_0
  have h8_1 : (1)*w 38=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h8_0-((((-1)*Y*Z)/(X^2)))*h13_0
  have h23_1 : ((Z)/(X^2))*w 7 + (1)*w 18 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_0-(((Z)/(X^2)))*h13_0
  have h24_1 : (1)*w 10 + (1)*w 24 + ((Z)/(X^2))*w 35=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_0-(((Z)/(X^2)))*h13_0
  have h31_1 : ((X^2)/(Y))*w 2 + ((X^2)/(Y))*w 8 + (1)*w 9 + ((X^2)/(Y))*w 14 + (1)*w 15 + ((X^2)/(Y))*w 20 + ((X^2)/(Y))*w 26 + (1)*w 27 + ((X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_0-((1))*h13_0
  have h30_1 : (Y)*w 0 + (Y)*w 6 + (1)*w 8 + (Y)*w 12 + (1)*w 14 + (Y)*w 18 + (1)*w 20 + (Y)*w 24 + (1)*w 26 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_0-((1))*h8_1
  have h32_1 : (1)*w 2 + (X^2)*w 8 + (1)*w 23=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h32_0-(((-1)*X*lam))*h7_1
  have h34_1 : ((-1)*X*lam)*w 8 + (X^2)*w 16 + (1)*w 25=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h34_0-((1))*h7_1
  have h1_1 : (1)*w 1=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h1_0-(((-1)*X^2*Y*Z))*h0_0
  have h2_1 : (1)*w 41=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h2_0-(((-1)*X^2*Y*Z))*h0_0
  have h3_1 : (1)*w 2=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h3_0-(((-1)*Y*Z))*h0_0
  have h4_1 : (1)*w 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h4_0-(((-1)*Y*Z))*h0_0
  have h14_1 : (1)*w 22=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h14_0-(((-1)*Y*Z))*h0_0
  have h15_1 : (1)*w 20=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h15_0-(((-1)*Y*Z))*h0_0
  have h19_1 : (1)*w 15 + (X^2*Z)*w 28 + (1)*w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h19_0-((X^2*Z))*h0_0
  have h20_1 : (1)*w 13 + (X^2*Z)*w 14 + (1)*w 27=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h20_0-((X^2*Z))*h0_0
  clear h7_0 h8_0 h23_0 h24_0 h31_0 h30_0 h32_0 h34_0 h1_0 h2_0 h3_0 h4_0 h14_0 h15_0 h19_0 h20_0
  have h21_1 : (Z)*w 14 + (1)*w 16 + (1)*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_0-((Z))*h0_0
  have h22_1 : (1)*w 12 + (1)*w 26 + (Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h22_0-((Z))*h0_0
  have h26_1 : (1)*w 8 + (Z)*w 28 + (1)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h26_0-((Z))*h0_0
  have h27_1 : (1)*w 6 + (Z)*w 14 + (1)*w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h27_0-((Z))*h0_0
  have h28_1 : (X^2*Y)*w 6 + (1)*w 7 + (X^2*Y)*w 12 + (1)*w 13 + (X^2*Y)*w 18 + (1)*w 19 + (X^2*Y)*w 24 + (1)*w 25 + (1)*w 31 + (X^2*Y)*w 36 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_0-((X^2*Y))*h0_0
  have h29_1 : (1)*w 5 + (X^2*Y)*w 6 + (1)*w 11 + (1)*w 17 + (X^2*Y)*w 18 + (1)*w 23 + (X^2*Y)*w 24 + (1)*w 29 + (X^2*Y)*w 30 + (1)*w 35 + (X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_0-((X^2*Y))*h0_0
  have h30_2 : (Y)*w 6 + (1)*w 8 + (Y)*w 12 + (1)*w 14 + (Y)*w 18 + (1)*w 20 + (Y)*w 24 + (1)*w 26 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_1-((Y))*h0_0
  have h39_1 : (1)*w 10 + ((-1)*X*lam)*w 20 + (1)*w 31=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h39_0-((X^2))*h4_1
  have h40_1 : (X^2)*w 2 + (1)*w 11 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h40_0-(((-1)*X*lam))*h14_1
  have h41_1 : (1)*w 16 + ((-1)*X*lam)*w 32 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h41_0-((X^2))*h14_1
  have h31_2 : ((X^2)/(Y))*w 8 + (1)*w 9 + ((X^2)/(Y))*w 14 + (1)*w 15 + ((X^2)/(Y))*w 20 + ((X^2)/(Y))*w 26 + (1)*w 27 + ((X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_1-(((X^2)/(Y)))*h3_1
  have h32_2 : (X^2)*w 8 + (1)*w 23=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h32_1-((1))*h3_1
  have h40_2 : (1)*w 11 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h40_1-((X^2))*h3_1
  have h30_3 : (Y)*w 6 + (1)*w 8 + (Y)*w 12 + (1)*w 14 + (Y)*w 18 + (Y)*w 24 + (1)*w 26 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_2-((1))*h15_1
  have h31_3 : ((X^2)/(Y))*w 8 + (1)*w 9 + ((X^2)/(Y))*w 14 + (1)*w 15 + ((X^2)/(Y))*w 26 + (1)*w 27 + ((X^2)/(Y))*w 32 + (1)*w 33 + (1)*w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_2-(((X^2)/(Y)))*h15_1
  have h35_1 : (1)*w 5 + ((-1)*X*lam)*w 10 + (1)*w 26=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h35_0-((X^2))*h15_1
  clear h21_0 h22_0 h26_0 h27_0 h28_0 h29_0 h30_1 h39_0 h40_0 h41_0 h31_1 h32_1 h40_1 h30_2 h31_2 h35_0
  have h39_2 : (1)*w 10 + (1)*w 31=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h39_1-(((-1)*X*lam))*h15_1
  have h33_1 : ((-1)*X*lam)*w 6 + (X^2)*w 12 + ((X^2*Z)/(Y))*w 14 + (1)*w 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_0-((1))*h5_0
  have h31_4 : ((X^2)/(Y))*w 8 + (1)*w 9 + ((X^2)/(Y))*w 14 + (1)*w 15 + ((X^2)/(Y))*w 26 + (1)*w 27 + ((X^2*Z)/(Y))*w 28 + ((X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_3-((1))*h6_0
  have h29_2 : (1)*w 5 + (X^2*Y)*w 6 + ((-1)*X^2)*w 8 + (1)*w 11 + (1)*w 17 + (X^2*Y)*w 18 + (X^2*Y)*w 24 + (1)*w 29 + (X^2*Y)*w 30 + (1)*w 35 + (X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_1-((1))*h32_2
  have h28_2 : (X^2*Y)*w 6 + (1)*w 7 + ((-1))*w 10 + (X^2*Y)*w 12 + (1)*w 13 + (X^2*Y)*w 18 + (1)*w 19 + (X^2*Y)*w 24 + (1)*w 25 + (X^2*Y)*w 36 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_1-((1))*h39_2
  have h29_3 : (1)*w 5 + (X^2*Y)*w 6 + ((-1)*X^2)*w 8 + (1)*w 17 + (X^2*Y)*w 18 + (X^2*Y)*w 24 + (1)*w 29 + (X^2*Y)*w 30 + ((-1))*w 32 + (1)*w 35 + (X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_2-((1))*h40_2
  have h23_2 : (1)*w 18 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_1-(((Z)/(X^2)))*h11_0
  have h25_1 : ((X^2*Y)/(Z))*w 30 + (1)*w 35=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h25_0-((1))*h11_0
  have h28_3 : (X^2*Y)*w 6 + ((-1))*w 10 + (X^2*Y)*w 12 + (1)*w 13 + (X^2*Y)*w 18 + (1)*w 19 + (X^2*Y)*w 24 + (1)*w 25 + ((X^2*Y)/(Z))*w 30 + (X^2*Y)*w 36 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_2-((1))*h11_0
  have h24_2 : (1)*w 10 + (Y)*w 12 + (1)*w 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_1-(((Z)/(X^2)))*h12_0
  have h25_2 : ((X^2*Y)/(Z))*w 12 + ((X^2*Y)/(Z))*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h25_1-((1))*h12_0
  have h29_4 : (1)*w 5 + (X^2*Y)*w 6 + ((-1)*X^2)*w 8 + ((X^2*Y)/(Z))*w 12 + (1)*w 17 + (X^2*Y)*w 18 + (X^2*Y)*w 24 + (1)*w 29 + (X^2*Y)*w 30 + ((-1))*w 32 + (X^2*Y)*w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_3-((1))*h12_0
  have h26_2 : (1)*w 8 + ((Z)/(Y))*w 14 + (Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h26_1-((1))*h10_0
  have h28_4 : (X^2*Y)*w 6 + ((-1))*w 10 + (X^2*Y)*w 12 + (1)*w 13 + (X^2*Z)*w 14 + (X^2*Y)*w 18 + (1)*w 19 + (X^2*Y)*w 24 + (1)*w 25 + ((X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_3-((X^2*Y))*h10_0
  have h29_5 : (1)*w 5 + (X^2*Y)*w 6 + ((-1)*X^2)*w 8 + ((X^2*Y)/(Z))*w 12 + (X^2*Z)*w 14 + (1)*w 17 + (X^2*Y)*w 18 + (X^2*Y)*w 24 + (1)*w 29 + (X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_4-((X^2*Y))*h10_0
  have h38_1 : (1)*w 9 + ((X^2*Z)/(Y))*w 14 + ((-1)*X*lam)*w 18 + (1)*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_0-((X^2))*h10_0
  clear h39_1 h33_0 h31_3 h29_1 h28_1 h29_2 h23_1 h25_0 h28_2 h24_1 h25_1 h29_3 h26_1 h28_3 h29_4 h38_0
  have h23_3 : ((Z)/(Y))*w 28 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_2-((1))*h17_0
  have h28_5 : (X^2*Y)*w 6 + ((-1))*w 10 + (X^2*Y)*w 12 + (1)*w 13 + (X^2*Z)*w 14 + (1)*w 19 + (X^2*Y)*w 24 + (1)*w 25 + (X^2*Z)*w 28 + ((X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_4-((X^2*Y))*h17_0
  have h29_6 : (1)*w 5 + (X^2*Y)*w 6 + ((-1)*X^2)*w 8 + ((X^2*Y)/(Z))*w 12 + (X^2*Z)*w 14 + (1)*w 17 + (X^2*Y)*w 24 + (X^2*Z)*w 28 + (1)*w 29 + (X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_5-((X^2*Y))*h17_0
  have h30_4 : (Y)*w 6 + (1)*w 8 + (Y)*w 12 + (1)*w 14 + (Y)*w 24 + (1)*w 26 + (Z)*w 28 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_3-((Y))*h17_0
  have h38_2 : (1)*w 9 + ((X^2*Z)/(Y))*w 14 + (((-1)*X*Z*lam)/(Y))*w 28 + (1)*w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_1-(((-1)*X*lam))*h17_0
  have h27_2 : (Z)*w 14 + ((Z)/(Y))*w 28 + (1)*w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h27_1-((1))*h9_0
  have h28_6 : ((-1))*w 10 + (X^2*Y)*w 12 + (1)*w 13 + (X^2*Z)*w 14 + (1)*w 19 + (X^2*Y)*w 24 + (1)*w 25 + (2*X^2*Z)*w 28 + ((X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_5-((X^2*Y))*h9_0
  have h29_7 : (1)*w 5 + ((-1)*X^2)*w 8 + ((X^2*Y)/(Z))*w 12 + (X^2*Z)*w 14 + (1)*w 17 + (X^2*Y)*w 24 + (2*X^2*Z)*w 28 + (1)*w 29 + (X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_6-((X^2*Y))*h9_0
  have h30_5 : (1)*w 8 + (Y)*w 12 + (1)*w 14 + (Y)*w 24 + (1)*w 26 + (2*Z)*w 28 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_4-((Y))*h9_0
  have h33_2 : (X^2)*w 12 + ((X^2*Z)/(Y))*w 14 + (1)*w 24 + (((-1)*X*Z*lam)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_1-(((-1)*X*lam))*h9_0
  have h36_1 : ((-1)*X*lam)*w 12 + (X^2)*w 24 + (1)*w 27 + ((Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_0-((1))*h9_0
  have h24_3 : (1)*w 10 + (Y)*w 12 + ((Z)/(Y))*w 14=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_2-((1))*h16_0
  have h28_7 : ((-1))*w 10 + (X^2*Y)*w 12 + (1)*w 13 + (2*X^2*Z)*w 14 + (1)*w 19 + (1)*w 25 + (2*X^2*Z)*w 28 + ((X^2*Y)/(Z))*w 30 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_6-((X^2*Y))*h16_0
  have h29_8 : (1)*w 5 + ((-1)*X^2)*w 8 + ((X^2*Y)/(Z))*w 12 + (2*X^2*Z)*w 14 + (1)*w 17 + (2*X^2*Z)*w 28 + (1)*w 29 + (X^2*Y)*w 30 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_7-((X^2*Y))*h16_0
  have h30_6 : (1)*w 8 + (Y)*w 12 + (1 + Z)*w 14 + (1)*w 26 + (2*Z)*w 28 + (Y)*w 30 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_5-((Y))*h16_0
  have h33_3 : (X^2)*w 12 + ((Z)/(Y) + (X^2*Z)/(Y))*w 14 + (((-1)*X*Z*lam)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_2-((1))*h16_0
  clear h23_2 h28_4 h29_5 h30_3 h38_1 h27_1 h28_5 h29_6 h30_4 h33_1 h36_0 h24_2 h28_6 h29_7 h30_5 h33_2
  have h36_2 : ((-1)*X*lam)*w 12 + ((X^2*Z)/(Y))*w 14 + (1)*w 27 + ((Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_1-((X^2))*h16_0
  have h21_2 : ((-1))*w 12 + (Z)*w 14 + (1)*w 16=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_1-(((Z)/(X^2*Y)))*h25_2
  have h23_4 : ((-1)*Y)*w 12 + ((Z)/(Y))*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_3-(((Z)/(X^2)))*h25_2
  have h28_8 : ((-1))*w 10 + (((-1)*X^2*Y)/(Z) + X^2*Y)*w 12 + (1)*w 13 + (2*X^2*Z)*w 14 + (1)*w 19 + (1)*w 25 + (2*X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_7-((1))*h25_2
  have h29_9 : (1)*w 5 + ((-1)*X^2)*w 8 + ((X^2*Y)/(Z) + (-1)*X^2*Y)*w 12 + (2*X^2*Z)*w 14 + (1)*w 17 + (2*X^2*Z)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_8-((Z))*h25_2
  have h30_7 : (1)*w 8 + (1 + Z)*w 14 + (1)*w 26 + (2*Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_6-(((Z)/(X^2)))*h25_2
  have h38_3 : (1)*w 9 + ((-1))*w 12 + ((X^2*Z)/(Y))*w 14 + (((-1)*X*Z*lam)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_2-(((Z)/(X^2*Y)))*h25_2
  have h20_2 : (1)*w 13 + (1)*w 27 + ((-1)*X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h20_1-((X^2*Z))*h18_0
  have h21_3 : ((-1))*w 12 + (1)*w 16 + ((-1)*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_2-((Z))*h18_0
  have h24_4 : (1)*w 10 + (Y)*w 12 + (((-1)*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_3-(((Z)/(Y)))*h18_0
  have h26_3 : (1)*w 8 + (((-1)*Z)/(Y) + Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h26_2-(((Z)/(Y)))*h18_0
  have h27_3 : ((Z)/(Y) + (-1)*Z)*w 28 + (1)*w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h27_2-((Z))*h18_0
  have h28_9 : ((-1))*w 10 + (((-1)*X^2*Y)/(Z) + X^2*Y)*w 12 + (1)*w 13 + (1)*w 19 + (1)*w 25 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_8-((2*X^2*Z))*h18_0
  have h29_10 : (1)*w 5 + ((-1)*X^2)*w 8 + ((X^2*Y)/(Z) + (-1)*X^2*Y)*w 12 + (1)*w 17 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_9-((2*X^2*Z))*h18_0
  have h30_8 : (1)*w 8 + (1)*w 26 + ((-1) + Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_7-((1 + Z))*h18_0
  have h31_5 : ((X^2)/(Y))*w 8 + (1)*w 9 + (1)*w 15 + ((X^2)/(Y))*w 26 + (1)*w 27 + (((-1)*X^2)/(Y) + (X^2*Z)/(Y))*w 28 + ((X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_4-(((X^2)/(Y)))*h18_0
  clear h36_1 h21_1 h23_3 h28_7 h29_8 h30_6 h38_2 h20_1 h21_2 h24_3 h26_2 h27_2 h28_8 h29_9 h30_7 h31_4
  have h33_4 : (X^2)*w 12 + (((-1)*Z)/(Y) + ((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h33_3-(((Z)/(Y) + (X^2*Z)/(Y)))*h18_0
  have h36_3 : ((-1)*X*lam)*w 12 + (1)*w 27 + ((Z)/(Y) + ((-1)*X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_2-(((X^2*Z)/(Y)))*h18_0
  have h38_4 : (1)*w 9 + ((-1))*w 12 + (((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_3-(((X^2*Z)/(Y)))*h18_0
  have h29_11 : (1)*w 5 + ((X^2*Y)/(Z) + (-1)*X^2*Y)*w 12 + (1)*w 17 + (((-1)*X^2*Z)/(Y) + X^2*Z)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_10-(((-1)*X^2))*h26_3
  have h30_9 : (1)*w 26 + ((Z)/(Y) + (-1))*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_8-((1))*h26_3
  have h31_6 : (1)*w 9 + (1)*w 15 + ((X^2)/(Y))*w 26 + (1)*w 27 + ((X^2*Z)/(Y^2) + ((-1)*X^2)/(Y))*w 28 + ((X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_5-(((X^2)/(Y)))*h26_3
  have h34_2 : (X^2)*w 16 + (1)*w 25 + (((-1)*X*Z*lam)/(Y) + X*Z*lam)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h34_1-(((-1)*X*lam))*h26_3
  have h37_1 : ((-1)*X*lam)*w 16 + ((Z)/(Y) + (-1)*Z)*w 28 + (1)*w 29 + (X^2)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h37_0-((1))*h26_3
  have h21_4 : (1)*w 16 + (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (-1)*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h21_3-((((-1))/(X^2)))*h33_4
  have h22_2 : (1)*w 26 + ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + (Z)/(Y) + Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h22_1-(((1)/(X^2)))*h33_4
  have h23_5 : (((-1)*Z)/(X^2) + ((-1)*Z*lam)/(X) + (Z)/(Y) + (-1)*Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h23_4-((((-1)*Y)/(X^2)))*h33_4
  have h24_5 : (1)*w 10 + ((Z)/(X^2) + (Z*lam)/(X) + ((-1)*Z)/(Y) + Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h24_4-(((Y)/(X^2)))*h33_4
  have h28_10 : ((-1))*w 10 + (1)*w 13 + (1)*w 19 + (1)*w 25 + ((-1) + Z + (-1)*X*lam + X*Z*lam + (-1)*X^2 + X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_9-((((-1)*Y)/(Z) + Y))*h33_4
  have h29_12 : (1)*w 5 + (1)*w 17 + (1 + (-1)*Z + X*lam + (-1)*X*Z*lam + ((-1)*X^2*Z)/(Y) + X^2)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_11-(((Y)/(Z) + (-1)*Y))*h33_4
  have h36_4 : (1)*w 27 + (((-1)*Z*lam)/(X*Y) + (Z)/(Y) + ((-1)*Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h36_3-((((-1)*lam)/(X)))*h33_4
  have h38_5 : (1)*w 9 + (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + ((-1)*Z)/(Y) + ((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h38_4-((((-1))/(X^2)))*h33_4
  clear h33_3 h36_2 h38_3 h29_10 h30_8 h31_5 h34_1 h37_0 h21_3 h22_1 h23_4 h24_4 h28_9 h29_11 h36_3 h38_4
  have h31_7 : (1)*w 15 + ((X^2)/(Y))*w 26 + (1)*w 27 + ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + (Z)/(Y) + (X*Z*lam)/(Y) + (X^2*Z)/(Y^2) + ((-1)*X^2)/(Y) + (X^2*Z)/(Y))*w 28 + ((X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_6-((1))*h38_5
  have h28_11 : (1)*w 13 + (1)*w 19 + (1)*w 25 + ((Z)/(X^2) + (Z*lam)/(X) + ((-1)*Z)/(Y) + (-1) + 2*Z + (-1)*X*lam + X*Z*lam + (-1)*X^2 + X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_10-(((-1)))*h24_5
  have h35_2 : (1)*w 5 + (1)*w 26 + ((Z*lam)/(X) + Z*lam^2 + ((-1)*X*Z*lam)/(Y) + X*Z*lam)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h35_1-(((-1)*X*lam))*h24_5
  have h20_3 : (1)*w 13 + ((Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (Z*lam^2)/(Y) + (X*Z*lam)/(Y) + (X^2*Z)/(Y) + (-1)*X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h20_2-((1))*h36_4
  have h31_8 : (1)*w 15 + ((X^2)/(Y))*w 26 + ((Z)/(X^2*Y) + (2*Z*lam)/(X*Y) + (Z*lam^2)/(Y) + (2*X*Z*lam)/(Y) + (X^2*Z)/(Y^2) + ((-1)*X^2)/(Y) + (2*X^2*Z)/(Y))*w 28 + ((X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_7-((1))*h36_4
  have h28_12 : (1)*w 19 + (1)*w 25 + ((Z)/(X^2) + ((-1)*Z*lam)/(X*Y) + (Z*lam)/(X) + ((-1)*Z*lam^2)/(Y) + (-1) + 2*Z + ((-1)*X*Z*lam)/(Y) + (-1)*X*lam + X*Z*lam + ((-1)*X^2*Z)/(Y) + (-1)*X^2 + 2*X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_11-((1))*h20_3
  have h34_3 : (1)*w 25 + ((Z)/(Y) + X*Z*lam + (X^2*Z)/(Y) + X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h34_2-((X^2))*h21_4
  have h37_2 : (((-1)*Z*lam)/(X*Y) + (Z)/(Y) + ((-1)*Z*lam^2)/(Y) + (-1)*Z + ((-1)*X*Z*lam)/(Y) + (-1)*X*Z*lam)*w 28 + (1)*w 29 + (X^2)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h37_1-(((-1)*X*lam))*h21_4
  have h41_2 : ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + (Z)/(Y) + Z)*w 28 + ((-1)*X*lam)*w 32 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h41_1-((1))*h21_4
  have h28_13 : (1)*w 19 + ((Z)/(X^2) + ((-1)*Z*lam)/(X*Y) + (Z*lam)/(X) + ((-1)*Z)/(Y) + ((-1)*Z*lam^2)/(Y) + (-1) + 2*Z + ((-1)*X*Z*lam)/(Y) + (-1)*X*lam + ((-2)*X^2*Z)/(Y) + (-1)*X^2 + X^2*Z)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_12-((1))*h34_3
  have h30_10 : (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + (-1) + (-1)*Z)*w 28 + (1)*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_9-((1))*h22_2
  have h31_9 : (1)*w 15 + ((Z)/(X^2*Y) + (2*Z*lam)/(X*Y) + ((-1)*Z)/(Y^2) + (Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y^2) + (2*X*Z*lam)/(Y) + ((-1)*X^2)/(Y) + (X^2*Z)/(Y))*w 28 + ((X^2)/(Y))*w 32 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_8-(((X^2)/(Y)))*h22_2
  have h35_3 : (1)*w 5 + (((-1)*Z)/(X^2*Y) + ((-1)*Z*lam)/(X*Y) + (Z*lam)/(X) + ((-1)*Z)/(Y) + (-1)*Z + Z*lam^2 + ((-1)*X*Z*lam)/(Y) + X*Z*lam)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h35_2-((1))*h22_2
  have h29_13 : (1)*w 17 + ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + ((-1)*Z*lam)/(X) + (Z)/(Y) + 1 + (-1)*Z*lam^2 + (X*Z*lam)/(Y) + X*lam + (-2)*X*Z*lam + ((-1)*X^2*Z)/(Y) + X^2)*w 28 + (1)*w 29 + ((-1))*w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_12-((1))*h35_3
  have h29_14 : (1)*w 17 + ((Z)/(X^2*Y) + ((-1)*Z)/(X^2) + (Z*lam)/(X*Y) + ((-2)*Z*lam)/(X) + (2*Z)/(Y) + 1 + (-1)*Z + (-1)*Z*lam^2 + (X*Z*lam)/(Y) + X*lam + (-2)*X*Z*lam + ((-1)*X^2*Z)/(Y) + X^2)*w 28 + (1)*w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_13-(((-1)))*h23_5
  have h30_11 : (((-1)*Z)/(X^2*Y) + (Z)/(X^2) + ((-1)*Z*lam)/(X*Y) + (Z*lam)/(X) + ((-1)*Z)/(Y) + (-1))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h30_10-((1))*h23_5
  clear h31_6 h28_10 h35_1 h20_2 h31_7 h28_11 h34_2 h37_1 h41_1 h28_12 h30_9 h31_8 h35_2 h29_12 h29_13 h30_10
  have h31_10 : (1)*w 15 + ((Z)/(X^2*Y) + (2*Z*lam)/(X*Y) + ((-1)*Z)/(Y^2) + (Z)/(Y) + (Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y^2) + (3*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y^2) + ((-1)*X^2)/(Y) + (2*X^2*Z)/(Y))*w 28 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_9-(((X^2)/(Y)))*h23_5
  have h37_3 : (((-1)*Z*lam)/(X*Y) + (Z)/(Y) + ((-1)*Z*lam^2)/(Y) + ((-1)*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y) + X^2*Z)*w 28 + (1)*w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h37_2-((X^2))*h23_5
  have h41_3 : ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + ((-1)*Z*lam)/(X) + (Z)/(Y) + Z + (-1)*Z*lam^2 + (X*Z*lam)/(Y) + (-1)*X*Z*lam)*w 28 + (1)*w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h41_2-(((-1)*X*lam))*h23_5
  have h28_14 : (1)*w 19 + (((-1)*Z)/(X^2*Y) + (Z)/(X^2) + ((-2)*Z*lam)/(X*Y) + (2*Z*lam)/(X) + ((-2)*Z)/(Y) + ((-1)*Z*lam^2)/(Y) + (-1) + Z + Z*lam^2 + ((-2)*X*Z*lam)/(Y) + (-1)*X*lam + X*Z*lam + ((-2)*X^2*Z)/(Y) + (-1)*X^2 + X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h28_13-((1))*h41_3
  have h19_2 : (1)*w 15 + ((Z*lam)/(X*Y) + ((-1)*Z)/(Y) + (Z*lam^2)/(Y) + (X*Z*lam)/(Y) + (X^2*Z)/(Y))*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h19_1-((1))*h37_3
  have h29_15 : (1)*w 17 + ((Z)/(X^2*Y) + ((-1)*Z)/(X^2) + (2*Z*lam)/(X*Y) + ((-2)*Z*lam)/(X) + (Z)/(Y) + (Z*lam^2)/(Y) + 1 + (-1)*Z + (-1)*Z*lam^2 + (2*X*Z*lam)/(Y) + X*lam + (-2)*X*Z*lam + X^2 + (-1)*X^2*Z)*w 28=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h29_14-((1))*h37_3
  have h31_11 : ((Z)/(X^2*Y) + (Z*lam)/(X*Y) + ((-1)*Z)/(Y^2) + (2*Z)/(Y) + ((-1)*X*Z*lam)/(Y^2) + (2*X*Z*lam)/(Y) + ((-1)*X^2*Z)/(Y^2) + ((-1)*X^2)/(Y) + (X^2*Z)/(Y))*w 28 + (1)*w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) h31_10-((1))*h19_2
  have hd : determinantFactor 1 1 1 X Y Z lam*w 28=0 := by
    unfold determinantFactor
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((X^2*Y))*h30_11
  refine ⟨hd, ?_⟩
  intro hz28
  simp only [hz28] at h31_11
  have hz33 : w 33=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h31_11
  simp only [hz28] at h19_2
  have hz15 : w 15=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h19_2
  simp only [hz28] at h29_15
  have hz17 : w 17=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h29_15
  simp only [hz28] at h37_3
  have hz29 : w 29=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h37_3
  simp only [hz28] at h28_14
  have hz19 : w 19=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h28_14
  simp only [hz28] at h41_3
  have hz37 : w 37=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h41_3
  simp only [hz28] at h23_5
  have hz32 : w 32=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h23_5
  simp only [hz28] at h35_3
  have hz5 : w 5=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h35_3
  clear h31_9 h37_2 h41_2 h28_13 h19_1 h29_14 h31_10 h30_11 h31_11 h19_2 h29_15 h37_3 h28_14 h41_3 h23_5 h35_3
  simp only [hz28] at h22_2
  have hz26 : w 26=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h22_2
  simp only [hz28] at h34_3
  have hz25 : w 25=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h34_3
  simp only [hz28] at h21_4
  have hz16 : w 16=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h21_4
  simp only [hz28] at h20_3
  have hz13 : w 13=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h20_3
  simp only [hz28] at h36_4
  have hz27 : w 27=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h36_4
  simp only [hz28] at h24_5
  have hz10 : w 10=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h24_5
  simp only [hz28] at h38_5
  have hz9 : w 9=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h38_5
  simp only [hz28] at h33_4
  have hz12 : w 12=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (((1)/(X^2)))*h33_4
  simp only [hz28] at h26_3
  have hz8 : w 8=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h26_3
  simp only [hz28] at h27_3
  have hz34 : w 34=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h27_3
  simp only [hz28] at h18_0
  have hz14 : w 14=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h18_0
  simp only [hz12] at h25_2
  have hz30 : w 30=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) (((Z)/(X^2*Y)))*h25_2
  simp only [hz14] at h16_0
  have hz24 : w 24=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h16_0
  simp only [hz28] at h9_0
  have hz6 : w 6=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h9_0
  simp only [hz28] at h17_0
  have hz18 : w 18=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h17_0
  simp only [hz14] at h10_0
  have hz36 : w 36=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h10_0
  clear h22_2 h34_3 h21_4 h20_3 h36_4 h24_5 h38_5 h33_4 h26_3 h27_3 h18_0 h25_2 h16_0 h9_0 h17_0 h10_0
  simp only [hz12] at h12_0
  have hz35 : w 35=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h12_0
  simp only [hz30] at h11_0
  have hz7 : w 7=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h11_0
  simp only [hz32] at h40_2
  have hz11 : w 11=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h40_2
  simp only [hz10] at h39_2
  have hz31 : w 31=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h39_2
  simp only [hz8] at h32_2
  have hz23 : w 23=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h32_2
  simp only [hz28] at h6_0
  have hz39 : w 39=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h6_0
  simp only [hz14] at h5_0
  have hz3 : w 3=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h5_0
  have hz20 : w 20=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h15_1
  have hz2 : w 2=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h3_1
  have hz22 : w 22=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h14_1
  have hz40 : w 40=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h4_1
  have hz41 : w 41=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h2_1
  have hz1 : w 1=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h1_1
  have hz0 : w 0=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h0_0
  have hz4 : w 4=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h7_1
  have hz38 : w 38=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h8_1
  clear h12_0 h11_0 h40_2 h39_2 h32_2 h6_0 h5_0 h15_1 h3_1 h14_1 h4_1 h2_1 h1_1 h0_0 h7_1 h8_1
  have hz21 : w 21=0 := by
    linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) ((1))*h13_0
  clear h13_0
  funext j
  fin_cases j <;> assumption

#print axioms laurent_structure_base_pos


compact_certificate
/-- Both conclusions use one of just two checked elimination certificates. -/
theorem laurent_structure_signs (E u v X Y Z lam : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows E u v X Y Z lam w=0)
    (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    determinantFactor E u v X Y Z lam*w 28=0 ∧ (w 28=0 → w=0) := by
  have hu2 : u^2=1 := by rcases hu with rfl | rfl <;> norm_num
  have hv2 : v^2=1 := by rcases hv with rfl | rfl <;> norm_num
  have hu0 : u≠0 := by rcases hu with rfl | rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl | rfl <;> norm_num
  have hsign : E*u*v=1 ∨ E*u*v= -1 := by
    rcases hE with rfl | rfl <;> rcases hu with rfl | rfl <;>
      rcases hv with rfl | rfl <;> norm_num
  have hw' : laurentRows (E*u*v) 1 1 X (u*Y) (v*Z) lam w=0 :=
    (laurentRows_sign_normalize E u v X Y Z lam hu2 hv2 w).trans hw
  have h : determinantFactor (E*u*v) 1 1 X (u*Y) (v*Z) lam*w 28=0 ∧
      (w 28=0 → w=0) := by
    rcases hsign with hp | hn
    · rw [hp] at hw' ⊢
      exact laurent_structure_base_pos X (u*Y) (v*Z) lam
        hX (mul_ne_zero hu0 hY) (mul_ne_zero hv0 hZ) w hw'
    · rw [hn] at hw' ⊢
      exact laurent_structure_base_neg X (u*Y) (v*Z) lam
        hX (mul_ne_zero hu0 hY) (mul_ne_zero hv0 hZ) w hw'
  refine ⟨?_,h.2⟩
  have hh0 := h.1
  rw [determinantFactor_sign_normalize E u v X Y Z lam hu2 hv2] at hh0
  have hh : (u*v)*(determinantFactor E u v X Y Z lam*w 28)=0 := by
    simpa only [mul_assoc] using hh0
  exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hu0 hv0)

#print axioms laurent_structure_signs

compact_certificate
/-- Sparse elimination certificate for signs (-1, -1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case0 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) (-1) (-1) X Y Z lam w=0) : (determinantFactor (-1) (-1) (-1) X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs (-1) (-1) (-1) X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case0

compact_certificate
theorem laurent_kernel_case0 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor (-1) (-1) (-1) X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) (-1) (-1) X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case0 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case0

compact_certificate
/-- Sparse elimination certificate for signs (-1, -1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case1 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) (-1) 1 X Y Z lam w=0) : (determinantFactor (-1) (-1) 1 X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs (-1) (-1) 1 X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case1

compact_certificate
theorem laurent_kernel_case1 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor (-1) (-1) 1 X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) (-1) 1 X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case1 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case1

compact_certificate
/-- Sparse elimination certificate for signs (-1, 1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case2 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) 1 (-1) X Y Z lam w=0) : (determinantFactor (-1) 1 (-1) X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs (-1) 1 (-1) X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case2

compact_certificate
theorem laurent_kernel_case2 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor (-1) 1 (-1) X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) 1 (-1) X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case2 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case2

compact_certificate
/-- Sparse elimination certificate for signs (-1, 1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case3 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) 1 1 X Y Z lam w=0) : (determinantFactor (-1) 1 1 X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs (-1) 1 1 X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case3

compact_certificate
theorem laurent_kernel_case3 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor (-1) 1 1 X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) 1 1 X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case3 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case3

compact_certificate
/-- Sparse elimination certificate for signs (1, -1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case4 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 (-1) (-1) X Y Z lam w=0) : (determinantFactor 1 (-1) (-1) X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs 1 (-1) (-1) X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case4

compact_certificate
theorem laurent_kernel_case4 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor 1 (-1) (-1) X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 (-1) (-1) X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case4 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case4

compact_certificate
/-- Sparse elimination certificate for signs (1, -1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case5 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 (-1) 1 X Y Z lam w=0) : (determinantFactor 1 (-1) 1 X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs 1 (-1) 1 X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case5

compact_certificate
theorem laurent_kernel_case5 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor 1 (-1) 1 X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 (-1) 1 X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case5 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case5

compact_certificate
/-- Sparse elimination certificate for signs (1, 1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case6 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 1 (-1) X Y Z lam w=0) : (determinantFactor 1 1 (-1) X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs 1 1 (-1) X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case6

compact_certificate
theorem laurent_kernel_case6 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor 1 1 (-1) X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 1 (-1) X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case6 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case6

compact_certificate
/-- Sparse elimination certificate for signs (1, 1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. -/
theorem laurent_structure_case7 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 1 1 X Y Z lam w=0) : (determinantFactor 1 1 1 X Y Z lam*w 28=0) ∧ (w 28=0 → w=0) := by
  exact laurent_structure_signs 1 1 1 X Y Z lam hX hY hZ w hw
    (by norm_num) (by norm_num) (by norm_num)

#print axioms laurent_structure_case7

compact_certificate
theorem laurent_kernel_case7 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor 1 1 1 X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 1 1 X Y Z lam w=0) : w=0 := by
  have h := laurent_structure_case7 X Y Z lam hX hY hZ w hw
  exact h.2 ((mul_eq_zero.mp h.1).resolve_left hD)

#print axioms laurent_kernel_case7

end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneRankCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Shared sign normalization and exact elimination certificates. -/
namespace SmallLevelTwentyOne
open Complex Matrix

compact_certificate
/-- Sparse elimination certificate for signs (-1, -1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case0 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) (-1) (-1) X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case0 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case0

compact_certificate
/-- Sparse elimination certificate for signs (-1, -1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case1 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) (-1) 1 X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case1 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case1

compact_certificate
/-- Sparse elimination certificate for signs (-1, 1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case2 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) 1 (-1) X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case2 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case2

compact_certificate
/-- Sparse elimination certificate for signs (-1, 1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case3 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows (-1) 1 1 X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case3 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case3

compact_certificate
/-- Sparse elimination certificate for signs (1, -1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case4 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 (-1) (-1) X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case4 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case4

compact_certificate
/-- Sparse elimination certificate for signs (1, -1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case5 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 (-1) 1 X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case5 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case5

compact_certificate
/-- Sparse elimination certificate for signs (1, 1, -1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case6 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 1 (-1) X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case6 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case6

compact_certificate
/-- Sparse elimination certificate for signs (1, 1, 1). Every row operation
and the reverse substitution are checked by the Lean kernel. The free
coordinate 28 controls the entire kernel, without any determinant premise. -/
theorem laurent_rank_case7 (X Y Z lam : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows 1 1 1 X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  exact (laurent_structure_case7 X Y Z lam hX hY hZ w hw).2 hzero

#print axioms laurent_rank_case7

end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneTheoryV4 -/
section
/-! Consolidated chapter: SmallLevelTwentyOne. Original statements are retained; exact sign normalization reduces eight elimination cases to two. -/

/-! ## SmallLevelTwentyOneRootSignsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex FinitenessNormalizedTwistProduct

def phaseRoot (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)
def rootU (f : ℕ → ℂ) : ℂ := -root 21 f 3
def rootV (f : ℕ → ℂ) : ℂ := -root 21 f 7

compact_certificate
theorem phaseRoot_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    phaseRoot m ε=1 ∨ phaseRoot m ε= -1 := by
  unfold phaseRoot
  rw [pow_mul,I_sq]
  rcases neg_one_pow_eq_or ℂ m with hm|hm <;> rcases hε with rfl|rfl <;> simp [hm]

compact_certificate
theorem rootU_sign {f : ℕ → ℂ} (hf : FinitenessOriginalInput.EulerData 21 f) :
    rootU f=1 ∨ rootU f= -1 := by
  rcases root_unit hf 3 with h|h <;> simp [rootU,h]

compact_certificate
theorem rootV_sign {f : ℕ → ℂ} (hf : FinitenessOriginalInput.EulerData 21 f) :
    rootV f=1 ∨ rootV f= -1 := by
  rcases root_unit hf 7 with h|h <;> simp [rootV,h]

compact_certificate
theorem root_one (f : ℕ → ℂ) : root 21 f 1=1 := by simp [root]
compact_certificate
theorem root_two (f : ℕ → ℂ) : root 21 f 2=1 := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign]
compact_certificate
theorem root_six (f : ℕ → ℂ) : root 21 f 6=root 21 f 3 :=
  SmallLevelSixEigen.root_six_three (by decide) f

def localRoot (u v : ℂ) (q : ℕ) : ℂ :=
  (if 3∣q then -u else 1)*(if 7∣q then -v else 1)

compact_certificate
theorem selected_root_scalar (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 28) :
    root 21 f (rowQ i)*ε*I^(2*m)=phaseRoot m ε*localRoot (rootU f) (rootV f) (rowQ i) := by
  fin_cases i <;>
    norm_num [rowQ,taylorSpecs,phaseRoot,localRoot,rootU,rootV,root_one,root_two,root_six] <;> ring

#print axioms phaseRoot_sign
#print axioms selected_root_scalar
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneAugmentedRootsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace SmallLevelTwentyOne
open Complex FinitenessNormalizedTwistProduct

compact_certificate
/-- The sign variables in the written augmented system are the actual
bad-prime normalized eigenvalues, not additional choices. -/
theorem rootU_eigenvalue (f : ℕ → ℂ) : rootU f=(Real.sqrt 3:ℂ)*f 3 := by
  norm_num [rootU,root,FinitenessNormalizedTwistLocal.sign]
  ring

compact_certificate
theorem rootV_eigenvalue (f : ℕ → ℂ) : rootV f=(Real.sqrt 7:ℂ)*f 7 := by
  norm_num [rootV,root,FinitenessNormalizedTwistLocal.sign]
  ring

compact_certificate
/-- All eight grid divisors have the same two local signs, including the
previously unselected q=14,21,42 Ramanujan rows. -/
theorem root_grid_divisor (f : ℕ → ℂ) {q : ℕ} (hq : q∣42) :
    root 21 f q=localRoot (rootU f) (rootV f) q := by
  have hp14 : Nat.primeFactors 14=({2,7}:Finset ℕ) := by
    rw [show (14:ℕ)=2*7 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp21 : Nat.primeFactors 21=({3,7}:Finset ℕ) := by
    rw [show (21:ℕ)=3*7 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have hp42 : Nat.primeFactors 42=({2,3,7}:Finset ℕ) := by
    rw [show (42:ℕ)=2*21 by decide,Nat.primeFactors_mul (by decide) (by decide),hp21]
    norm_num
    decide
  have he : Nat.divisors 42=({1,2,3,6,7,14,21,42}:Finset ℕ) := by decide
  have hmem := Nat.mem_divisors.mpr ⟨hq,(by decide : (42:ℕ)≠0)⟩
  rw [he] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [root,localRoot,rootU,rootV,FinitenessNormalizedTwistLocal.sign,
      SmallLevelSixEigen.primeFactors_six,hp14,hp21,hp42,Nat.factorization_eq_zero_iff]

#print axioms rootU_eigenvalue
#print axioms rootV_eigenvalue
#print axioms root_grid_divisor
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneOriginalMatrixSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Set Matrix SmallLevelTaylor SmallLevelAdditive

compact_certificate
/-- The actual 42-dimensional closed Taylor system, with all coefficients,
errors and coordinate functions explicit and all analytic hypotheses proved. -/
theorem original_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ,
      (∀ i : Fin 42, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 42, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => errorVector m f ε M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        leadingMatrix m f ε s *ᵥ gridVector (2*m) f s=
          errorVector m f ε M s+
            ∑ n∈Finset.range M, shiftMatrix m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  obtain ⟨ε,hε,BT,hT⟩ := original_taylor_system (by exact even_two_mul m) hf
  obtain ⟨hRE,BR,hR⟩ := original_entire_rows (by omega : 0<2*m) hf
  obtain ⟨BH,hH⟩ := original_selected_hecke_rows hf
  obtain ⟨BF,hF⟩ := SmallLevelAdditive.original_common_halfplane hf
  let B : ℝ := max (max BT BR) (max BH BF)
  have hBT : BT≤B := (le_max_left _ _).trans (le_max_left _ _)
  have hBR : BR≤B := (le_max_right _ _).trans (le_max_left _ _)
  have hBH : BH≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hBF : BF≤B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨ε,hε,B,?_,?_,?_⟩
  · intro i s hs
    exact (hF (((i:ℕ):ℝ)/42) s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have ht (a : Fin 28) : AnalyticAt ℂ (rowError (2*m) f ε a M) s := by
      apply (hT a M).1 s
      change BT-((M:ℝ)+1)<s.re
      linarith
    fin_cases i <;> dsimp [errorVector,assemble]
    · exact hRE 0 s
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · exact ht 3
    · exact ht 4
    · exact ht 5
    · exact ht 6
    · exact ht 7
    · exact ht 8
    · exact ht 9
    · exact ht 10
    · exact ht 11
    · exact hRE 1 s
    · exact ht 12
    · exact ht 13
    · exact ht 14
    · exact ht 15
    · exact hRE 2 s
    · exact ht 16
    · exact ht 17
    · exact ht 18
    · exact ht 19
    · exact ht 20
    · exact ht 21
    · exact hRE 3 s
    · exact ht 22
    · exact ht 23
    · exact ht 24
    · exact ht 25
    · exact ht 26
    · exact ht 27
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
  · intro M s hs
    have hsT : BT<s.re := lt_of_le_of_lt hBT hs
    have hsR : BR<s.re := lt_of_le_of_lt hBR hs
    have hsH : BH<s.re := lt_of_le_of_lt hBH hs
    rw [leadingMatrix_mulVec]
    simp_rw [shiftMatrix_mulVec]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    fin_cases i <;>
      dsimp [leadingRows,taylorLeading,heckeLeading,errorVector,shiftRows,assemble] <;>
      norm_num only [sampleSum_grid,gridVector_index,Finset.sum_const_zero,add_zero]
    · exact (hR 0 s hsR).symm
    · exact (hT 0 M).2 s hsT
    · exact (hT 1 M).2 s hsT
    · exact (hT 2 M).2 s hsT
    · exact (hT 3 M).2 s hsT
    · exact (hT 4 M).2 s hsT
    · exact (hT 5 M).2 s hsT
    · exact (hT 6 M).2 s hsT
    · exact (hT 7 M).2 s hsT
    · exact (hT 8 M).2 s hsT
    · exact (hT 9 M).2 s hsT
    · exact (hT 10 M).2 s hsT
    · exact (hT 11 M).2 s hsT
    · exact (hR 1 s hsR).symm
    · exact (hT 12 M).2 s hsT
    · exact (hT 13 M).2 s hsT
    · exact (hT 14 M).2 s hsT
    · exact (hT 15 M).2 s hsT
    · exact (hR 2 s hsR).symm
    · exact (hT 16 M).2 s hsT
    · exact (hT 17 M).2 s hsT
    · exact (hT 18 M).2 s hsT
    · exact (hT 19 M).2 s hsT
    · exact (hT 20 M).2 s hsT
    · exact (hT 21 M).2 s hsT
    · exact (hR 3 s hsR).symm
    · exact (hT 22 M).2 s hsT
    · exact (hT 23 M).2 s hsT
    · exact (hT 24 M).2 s hsT
    · exact (hT 25 M).2 s hsT
    · exact (hT 26 M).2 s hsT
    · exact (hT 27 M).2 s hsT
    · exact hH 0 s hsH
    · exact hH 1 s hsH
    · exact hH 2 s hsH
    · exact hH 3 s hsH
    · exact hH 4 s hsH
    · exact hH 5 s hsH
    · exact hH 6 s hsH
    · exact hH 7 s hsH
    · exact hH 8 s hsH
    · exact hH 9 s hsH

#print axioms original_matrix_system
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneCoherentMatrixSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOne
open Complex Set Matrix SmallLevelTaylor SmallLevelAdditive
open MeasureTheory FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct

-- Fix the original coherent sign before constructing the continuation.
-- This permits every old matrix row and new word row to use the same sign.
compact_certificate
theorem taylor_system_of_law {k : ℕ} (hk : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 k f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 k f ε) :
    ∃ B : ℝ, ∀ i : Fin 28, ∀ M : ℕ,
      AnalyticOnNhd ℂ (rowError k f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum k f 42 (rowQ i) (rowT i) s-
          rowCoefficient k f ε i 0 s*gridSum k f 42 (rowQ i) (rowPartner i) s=
        rowError k f ε i M s+
          ∑ n∈Finset.range M, rowCoefficient k f ε i (n+1) s*
            gridSum k f 42 (rowQ i) (rowPartner i) (s+((n:ℂ)+1)) := by
  have hrows := QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
    (by decide : 0<21) hk hf ε hlaw
  have hi (i : Fin 28) := hrows 42 (rowQ i) (by decide) (taylorSpecs_valid i).1
    (taylorSpecs_valid i).2.1 (rowT i) (rowD i) (taylorSpecs_valid i).2.2.1
    (taylorSpecs_valid i).2.2.2.1 (taylorSpecs_valid i).2.2.2.2
  choose b hb using hi
  let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 28) : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

compact_certificate
theorem matrix_system_of_law {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    ∃ B : ℝ,
      (∀ i : Fin 42, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 42, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => errorVector m f ε M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        leadingMatrix m f ε s *ᵥ gridVector (2*m) f s=
          errorVector m f ε M s+
            ∑ n∈Finset.range M, shiftMatrix m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  obtain ⟨BT,hT⟩ := taylor_system_of_law (by exact even_two_mul m) hf ε hlaw
  obtain ⟨hRE,BR,hR⟩ := original_entire_rows (by omega : 0<2*m) hf
  obtain ⟨BH,hH⟩ := original_selected_hecke_rows hf
  obtain ⟨BF,hF⟩ := SmallLevelAdditive.original_common_halfplane hf
  let B : ℝ := max (max BT BR) (max BH BF)
  have hBT : BT≤B := (le_max_left _ _).trans (le_max_left _ _)
  have hBR : BR≤B := (le_max_right _ _).trans (le_max_left _ _)
  have hBH : BH≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hBF : BF≤B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B,?_,?_,?_⟩
  · intro i s hs
    exact (hF (((i:ℕ):ℝ)/42) s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have ht (a : Fin 28) : AnalyticAt ℂ (rowError (2*m) f ε a M) s := by
      apply (hT a M).1 s
      change BT-((M:ℝ)+1)<s.re
      linarith
    fin_cases i <;> dsimp [errorVector,assemble]
    · exact hRE 0 s
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · exact ht 3
    · exact ht 4
    · exact ht 5
    · exact ht 6
    · exact ht 7
    · exact ht 8
    · exact ht 9
    · exact ht 10
    · exact ht 11
    · exact hRE 1 s
    · exact ht 12
    · exact ht 13
    · exact ht 14
    · exact ht 15
    · exact hRE 2 s
    · exact ht 16
    · exact ht 17
    · exact ht 18
    · exact ht 19
    · exact ht 20
    · exact ht 21
    · exact hRE 3 s
    · exact ht 22
    · exact ht 23
    · exact ht 24
    · exact ht 25
    · exact ht 26
    · exact ht 27
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
  · intro M s hs
    have hsT : BT<s.re := lt_of_le_of_lt hBT hs
    have hsR : BR<s.re := lt_of_le_of_lt hBR hs
    have hsH : BH<s.re := lt_of_le_of_lt hBH hs
    rw [leadingMatrix_mulVec]
    simp_rw [shiftMatrix_mulVec]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    fin_cases i <;>
      dsimp [leadingRows,taylorLeading,heckeLeading,errorVector,shiftRows,assemble] <;>
      norm_num only [sampleSum_grid,gridVector_index,Finset.sum_const_zero,add_zero]
    · exact (hR 0 s hsR).symm
    · exact (hT 0 M).2 s hsT
    · exact (hT 1 M).2 s hsT
    · exact (hT 2 M).2 s hsT
    · exact (hT 3 M).2 s hsT
    · exact (hT 4 M).2 s hsT
    · exact (hT 5 M).2 s hsT
    · exact (hT 6 M).2 s hsT
    · exact (hT 7 M).2 s hsT
    · exact (hT 8 M).2 s hsT
    · exact (hT 9 M).2 s hsT
    · exact (hT 10 M).2 s hsT
    · exact (hT 11 M).2 s hsT
    · exact (hR 1 s hsR).symm
    · exact (hT 12 M).2 s hsT
    · exact (hT 13 M).2 s hsT
    · exact (hT 14 M).2 s hsT
    · exact (hT 15 M).2 s hsT
    · exact (hR 2 s hsR).symm
    · exact (hT 16 M).2 s hsT
    · exact (hT 17 M).2 s hsT
    · exact (hT 18 M).2 s hsT
    · exact (hT 19 M).2 s hsT
    · exact (hT 20 M).2 s hsT
    · exact (hT 21 M).2 s hsT
    · exact (hR 3 s hsR).symm
    · exact (hT 22 M).2 s hsT
    · exact (hT 23 M).2 s hsT
    · exact (hT 24 M).2 s hsT
    · exact (hT 25 M).2 s hsT
    · exact (hT 26 M).2 s hsT
    · exact (hT 27 M).2 s hsT
    · exact hH 0 s hsH
    · exact hH 1 s hsH
    · exact hH 2 s hsH
    · exact hH 3 s hsH
    · exact hH 4 s hsH
    · exact hH 5 s hsH
    · exact hH 6 s hsH
    · exact hH 7 s hsH
    · exact hH 8 s hsH
    · exact hH 9 s hsH


#print axioms taylor_system_of_law
#print axioms matrix_system_of_law
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneIntegerRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex SmallLevelTaylor

def rowRate (i : Fin 28) : ℚ := (rowL i:ℚ)*((rowT i:ℚ)/42)^2

def ratePowers : Fin 28 → ℤ×ℤ×ℤ :=
  ![(-2,-1,-1),(-2,-1,-1),(0,-1,-1),(0,-1,-1),(-2,1,-1),(-2,1,-1),
    (2,-1,-1),(2,-1,-1),(0,1,-1),(0,1,-1),(-2,-1,1),(-2,-1,1),
    (0,-1,-1),(0,-1,-1),(0,1,-1),(0,1,-1),
    (-2,0,-1),(-2,0,-1),(0,0,-1),(0,0,-1),(2,0,-1),(2,0,-1),
    (0,0,-1),(0,0,-1),(-2,-1,0),(-2,-1,0),(0,-1,0),(-2,1,0)]

compact_certificate
theorem rate_certificate : ∀ i : Fin 28,
    rowRate i=(2:ℚ)^(ratePowers i).1*(3:ℚ)^(ratePowers i).2.1*(7:ℚ)^(ratePowers i).2.2 := by
  intro i
  fin_cases i <;> norm_num [rowRate,rowL,rowQ,rowT,taylorSpecs,ratePowers]

def rateMonomial (i : Fin 28) (X Y Z : ℂ) : ℂ :=
  X^(-(ratePowers i).1)*Y^(-(ratePowers i).2.1)*Z^(-(ratePowers i).2.2)

compact_certificate
theorem inverse_geometric_zpow (p : ℂ) (n : ℕ) (a : ℤ) :
    (p^a)^n=((1/p)^n)^(-a) := by
  simp only [one_div,← zpow_natCast,← zpow_mul,inv_zpow,← zpow_neg]
  congr 1
  ring

compact_certificate
theorem rate_integer_power (i : Fin 28) (n : ℕ) :
    (rowRate i:ℂ)^n=rateMonomial i ((1/2:ℂ)^n) ((1/3:ℂ)^n) ((1/7:ℂ)^n) := by
  have he : (rowRate i:ℂ)=(2:ℂ)^(ratePowers i).1*(3:ℂ)^(ratePowers i).2.1*(7:ℂ)^(ratePowers i).2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q:ℂ)) (rate_certificate i)
  rw [he,mul_pow,mul_pow,inverse_geometric_zpow,inverse_geometric_zpow,inverse_geometric_zpow]
  rfl

compact_certificate
theorem rowCoefficient_integer (m n : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 28) :
    rowCoefficient (2*m) f ε i 0 ((m+n:ℕ):ℂ)=
      phaseRoot m ε*localRoot (rootU f) (rootV f) (rowQ i)*
        rateMonomial i ((1/2:ℂ)^n) ((1/3:ℂ)^n) ((1/7:ℂ)^n) := by
  unfold rowCoefficient taylorRowScalar
  simp only [pow_zero,mul_one,Ring.choose_zero_right]
  rw [selected_root_scalar]
  have hex : ((m+n:ℕ):ℂ)-((2*m:ℕ):ℂ)/2=(n:ℂ) := by push_cast; ring
  rw [hex,Complex.cpow_natCast]
  have hr : (((rowL i:ℝ)*((rowT i:ℝ)/42)^2:ℝ):ℂ)=(rowRate i:ℂ) := by
    unfold rowRate
    push_cast
    rfl
  rw [hr,rate_integer_power]

compact_certificate
theorem hecke_parameter_integer (m n : ℕ) :
    (2:ℂ)^((m:ℂ)-((m+n:ℕ):ℂ))=(1/2:ℂ)^n := by
  rw [Nat.cast_add,sub_add_cancel_left,Complex.cpow_neg,Complex.cpow_natCast]
  simp only [one_div,inv_pow]

#print axioms rate_certificate
#print axioms rowCoefficient_integer
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneLaurentMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix

def laurentLinear (E u v X Y Z lam : ℂ) : (Fin 42 → ℂ) →ₗ[ℂ] (Fin 42 → ℂ) where
  toFun := laurentRows E u v X Y Z lam
  map_add' := by
    intro w z
    funext i
    fin_cases i <;> simp [laurentRows,Pi.add_apply] <;> ring
  map_smul' := by
    intro c w
    funext i
    fin_cases i <;> simp [laurentRows,Pi.smul_apply,smul_eq_mul] <;> ring

def laurentMatrix (E u v X Y Z lam : ℂ) : Matrix (Fin 42) (Fin 42) ℂ :=
  (laurentLinear E u v X Y Z lam).toMatrix'

compact_certificate
theorem laurentMatrix_mulVec (E u v X Y Z lam : ℂ) (w : Fin 42 → ℂ) :
    laurentMatrix E u v X Y Z lam *ᵥ w=laurentRows E u v X Y Z lam w :=
  LinearMap.toMatrix'_mulVec _ _

compact_certificate
theorem laurentMatrix_apply (E u v X Y Z lam : ℂ) (i j : Fin 42) :
    laurentMatrix E u v X Y Z lam i j=
      laurentRows E u v X Y Z lam (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

#print axioms laurentMatrix_mulVec
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneFactorWitnessV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Filter
open scoped Topology

def normalizedFactorSequence (E u v lam : ℂ) (n : ℕ) : ℂ :=
  (lam*(1/2:ℂ)^n+1)*((1/3:ℂ)^n-u)+
    (E*u*v-1)*(1/12:ℂ)^n-E*u*(7/12:ℂ)^n-u*(1/4:ℂ)^n

compact_certificate
theorem factor_geometric_identity (E u v lam : ℂ) (n : ℕ) :
    determinantFactor E u v ((1/2:ℂ)^n) ((1/3:ℂ)^n) ((1/7:ℂ)^n) lam=
      (1/7:ℂ)^n*normalizedFactorSequence E u v lam n := by
  have h12 : (1/12:ℂ)^n=((1/2:ℂ)^n)^2*(1/3:ℂ)^n := by
    rw [pow_two,← mul_pow,← mul_pow]
    norm_num
  have h4 : (1/4:ℂ)^n=((1/2:ℂ)^n)^2 := by
    rw [pow_two,← mul_pow]
    norm_num
  have h7 : (1/7:ℂ)^n*(7/12:ℂ)^n=(1/12:ℂ)^n := by
    rw [← mul_pow]
    norm_num
  unfold determinantFactor normalizedFactorSequence
  rw [h12,h4] at *
  linear_combination E*u*h7

compact_certificate
theorem factor_sequence_limit (E u v lam : ℂ) :
    Tendsto (normalizedFactorSequence E u v lam) atTop (𝓝 (-u)) := by
  have h2 : Tendsto (fun n : ℕ => (1/2:ℂ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have h3 : Tendsto (fun n : ℕ => (1/3:ℂ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have h12 : Tendsto (fun n : ℕ => (1/12:ℂ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have h7 : Tendsto (fun n : ℕ => (7/12:ℂ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have h4 : Tendsto (fun n : ℕ => (1/4:ℂ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hA := ((tendsto_const_nhds (x := lam)).mul h2).add (tendsto_const_nhds (x := (1:ℂ)))
  have hB := h3.sub (tendsto_const_nhds (x := u))
  have hC := (hA.mul hB).add ((tendsto_const_nhds (x := E*u*v-1)).mul h12)
  have hD := hC.sub ((tendsto_const_nhds (x := E*u)).mul h7)
  unfold normalizedFactorSequence
  simpa only [mul_zero,zero_add,zero_sub,one_mul,sub_zero,add_zero] using
    hD.sub ((tendsto_const_nhds (x := u)).mul h4)


compact_certificate
/-- The determinant factor is not identically zero for any complex Hecke
eigenvalue. A point on the real integer sequence witnesses this. -/
theorem determinantFactor_exists_nonzero (E u v lam : ℂ) (hu : u≠0) :
    ∃ n : ℕ, determinantFactor E u v ((1/2:ℂ)^n) ((1/3:ℂ)^n) ((1/7:ℂ)^n) lam≠0 := by
  have he : ∀ᶠ n : ℕ in atTop, normalizedFactorSequence E u v lam n≠0 :=
    (factor_sequence_limit E u v lam).eventually_ne (neg_ne_zero.mpr hu)
  obtain ⟨n,hn⟩ := he.exists
  refine ⟨n,?_⟩
  rw [factor_geometric_identity]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hn

#print axioms factor_geometric_identity
#print axioms determinantFactor_exists_nonzero
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneKernelCertificateV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix

compact_certificate
/-- All eight original sign cases of the exact 42-row kernel certificate. -/
theorem laurent_kernel (E u v X Y Z lam : ℂ)
    (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor E u v X Y Z lam≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows E u v X Y Z lam w=0) : w=0 := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · exact laurent_kernel_case7 X Y Z lam hX hY hZ hD w hw
  · exact laurent_kernel_case6 X Y Z lam hX hY hZ hD w hw
  · exact laurent_kernel_case5 X Y Z lam hX hY hZ hD w hw
  · exact laurent_kernel_case4 X Y Z lam hX hY hZ hD w hw
  · exact laurent_kernel_case3 X Y Z lam hX hY hZ hD w hw
  · exact laurent_kernel_case2 X Y Z lam hX hY hZ hD w hw
  · exact laurent_kernel_case1 X Y Z lam hX hY hZ hD w hw
  · exact laurent_kernel_case0 X Y Z lam hX hY hZ hD w hw

compact_certificate
/-- Nonsingularity of the actual Laurent matrix follows from the checked
sparse kernel certificate, without a permutation expansion of its determinant. -/
theorem laurentMatrix_det_ne_zero (E u v X Y Z lam : ℂ)
    (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hD : determinantFactor E u v X Y Z lam≠0) :
    (laurentMatrix E u v X Y Z lam).det≠0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro w z hw
  have hn : laurentMatrix E u v X Y Z lam *ᵥ (w-z)=0 := by
    rw [Matrix.mulVec_sub,hw,sub_self]
  rw [laurentMatrix_mulVec] at hn
  exact sub_eq_zero.mp (laurent_kernel E u v X Y Z lam hE hu hv hX hY hZ hD (w-z) hn)

compact_certificate
/-- For every complex Hecke eigenvalue and all original sign choices,
the leading matrix is nonsingular at some point of the geometric sequence. -/
theorem laurentMatrix_exists_nonsingular (E u v lam : ℂ)
    (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    ∃ n : ℕ, (laurentMatrix E u v ((1/2:ℂ)^n) ((1/3:ℂ)^n) ((1/7:ℂ)^n) lam).det≠0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  obtain ⟨n,hn⟩ := determinantFactor_exists_nonzero E u v lam hu0
  exact ⟨n,laurentMatrix_det_ne_zero E u v _ _ _ lam hE hu hv
    (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num)) hn⟩

#print axioms laurent_kernel
#print axioms laurentMatrix_det_ne_zero
#print axioms laurentMatrix_exists_nonsingular
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneMatrixIdentificationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix SmallLevelTaylor FinitenessRamanujanSum

compact_certificate
theorem leadingRows_integer (m n : ℕ) (f : ℕ → ℂ) (ε : ℂ) (w : Fin 42 → ℂ) :
    leadingRows m f ε ((m+n:ℕ):ℂ) w=
      laurentRows (phaseRoot m ε) (rootU f) (rootV f)
        ((1/2:ℂ)^n) ((1/3:ℂ)^n) ((1/7:ℂ)^n) ((Real.sqrt 2:ℂ)*f 2) w := by
  unfold leadingRows taylorLeading heckeLeading
  simp_rw [rowCoefficient_integer,hecke_parameter_integer]
  funext i
  fin_cases i <;>
    norm_num [laurentRows,sampleSum,residues,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      heckeSpecs,gridIndex,Finset.sum_filter,Finset.sum_range_succ,rateMonomial,ratePowers,localRoot] <;>
    ring1

compact_certificate
theorem leadingMatrix_integer (m n : ℕ) (f : ℕ → ℂ) (ε : ℂ) :
    leadingMatrix m f ε ((m+n:ℕ):ℂ)=
      laurentMatrix (phaseRoot m ε) (rootU f) (rootV f)
        ((1/2:ℂ)^n) ((1/3:ℂ)^n) ((1/7:ℂ)^n) ((Real.sqrt 2:ℂ)*f 2) := by
  ext i j
  rw [leadingMatrix_apply,laurentMatrix_apply,leadingRows_integer]

compact_certificate
/-- An actual nonzero determinant witness for the leading matrix assembled
from original Euler data, for every allowed root sign and every weight. -/
theorem original_leadingMatrix_nonsingular {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1) :
    ∃ s : ℂ, (leadingMatrix m f ε s).det≠0 := by
  obtain ⟨n,hn⟩ := laurentMatrix_exists_nonsingular (phaseRoot m ε) (rootU f) (rootV f)
    ((Real.sqrt 2:ℂ)*f 2) (phaseRoot_sign m hε) (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData)
  refine ⟨((m+n:ℕ):ℂ),?_⟩
  rw [leadingMatrix_integer]
  exact hn

#print axioms leadingMatrix_integer
#print axioms original_leadingMatrix_nonsingular
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix

compact_certificate
/-- Meromorphic continuation of all 42 original additive transforms at
level 21. Every matrix, Taylor row, error estimate and nonsingularity
premise is derived from the original Euler input. -/
theorem original_grid_continuation {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ B : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=gridVector (2*m) f z := by
  obtain ⟨ε,hε,B,hF,hH,hrow⟩ := original_matrix_system hm hf
  refine ⟨B,?_⟩
  apply SmallLevelContinuation.closed_system_continuation B
    (gridVector (2*m) f) (leadingMatrix m f ε)
    (shiftMatrix m f ε) (errorVector m f ε) hF
    (leadingMatrix_analytic m f ε)
    (original_leadingMatrix_nonsingular hf ε hε)
    (shiftMatrix_analytic m f ε) hH
  intro n z hz i
  simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_apply] using
    congrFun (hrow n z hz) i

#print axioms original_grid_continuation
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneContinuedSystemV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix Filter Set
open scoped Topology

compact_certificate
/-- The level-21 continuation retains its coherent sign, initial analytic
half-plane, and every Taylor recurrence as a germ on the full domain of
its actual remainder. -/
theorem original_continued_system {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      (∀ z, B<z.re → G z=gridVector (2*m) f z) ∧
      (∀ i z, B<z.re → AnalyticAt ℂ (fun w => G w i) z) ∧
      (∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
        AnalyticAt ℂ (fun w => errorVector m f ε n w i) z) ∧
      ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
        (fun z => ∑ j, leadingMatrix m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => errorVector m f ε n z i+
            ∑ a∈Finset.range n, ∑ j, shiftMatrix m f ε a z i j*G (z+((a:ℂ)+1)) j) := by
  obtain ⟨ε,hε,B,hF,hH,hrow⟩ := original_matrix_system hm hf
  have hrows : ∀ n z, B<z.re → ∀ i,
      ∑ j, leadingMatrix m f ε z i j*gridVector (2*m) f z j=
        errorVector m f ε n z i+
          ∑ a∈Finset.range n, ∑ j, shiftMatrix m f ε a z i j*
            gridVector (2*m) f (z+((a:ℂ)+1)) j := by
    intro n z hz i
    simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using
      congrFun (hrow n z hz) i
  obtain ⟨G,hG,heG⟩ := SmallLevelContinuation.closed_system_continuation B
    (gridVector (2*m) f) (leadingMatrix m f ε) (shiftMatrix m f ε) (errorVector m f ε)
    hF (leadingMatrix_analytic m f ε) (original_leadingMatrix_nonsingular hf ε hε)
    (shiftMatrix_analytic m f ε) hH hrows
  refine ⟨ε,hε,B,G,hG,heG,?_,hH,?_⟩
  · intro i z hz
    apply (hF i z hz).congr
    have hn : ∀ᶠ w in 𝓝 z, B<w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hn] with w hw
    exact (congrFun (heG w hw) i).symm
  · exact SmallLevelContinuation.continued_rows B (gridVector (2*m) f) G
      (leadingMatrix m f ε) (shiftMatrix m f ε) (errorVector m f ε)
      (fun i z => (hG i z).meromorphicAt) heG (leadingMatrix_analytic m f ε)
      (shiftMatrix_analytic m f ε) hH hrow

compact_certificate
/-- Any pole of the actual level-21 continuation has a rightmost integer
translate whose nonzero leading Laurent vector is annihilated by the
actual leading matrix. In particular that determinant vanishes there. -/
theorem original_pole_constraint {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∃ B : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      (∀ z, B<z.re → G z=gridVector (2*m) f z) ∧
      ∀ x, (∃ i, meromorphicOrderAt (fun z => G z i) x<0) →
        ∃ n : ℕ, (∃ i, meromorphicOrderAt (fun z => G z i) (x+n)<0) ∧
          (∀ j : ℕ, 0<j → ∀ i, 0≤meromorphicOrderAt (fun z => G z i) (x+n+j)) ∧
          (∃ v : Fin 42 → ℂ, v≠0 ∧ leadingMatrix m f ε (x+n) *ᵥ v=0) ∧
          (leadingMatrix m f ε (x+n)).det=0 := by
  obtain ⟨ε,hε,B,G,hG,heG,hhalf,hH,hrow⟩ := original_continued_system hm hf
  refine ⟨ε,hε,B,G,hG,heG,?_⟩
  intro x hpole
  obtain ⟨n,hn,hshift⟩ := SmallLevelPoleGrid.rightmost_pole
    (fun i z => G z i) hpole B hhalf
  have hker := SmallLevelContinuation.continued_leading_kernel B G
    (leadingMatrix m f ε) (shiftMatrix m f ε) (errorVector m f ε) hG
    (leadingMatrix_analytic m f ε) (shiftMatrix_analytic m f ε) hH hrow (x+n) hn hshift
  exact ⟨n,hn,hshift,hker,SmallLevelContinuation.det_zero_of_kernel _ hker⟩

#print axioms original_continued_system
#print axioms original_pole_constraint
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneCoherentContinuationV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOne
open Complex Matrix Filter Set
open scoped Topology

compact_certificate
theorem continued_system_of_law {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    ∃ B : ℝ, ∃ G : ℂ → Fin 42 → ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      (∀ z, B<z.re → G z=gridVector (2*m) f z) ∧
      (∀ i z, B<z.re → AnalyticAt ℂ (fun w => G w i) z) ∧
      (∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
        AnalyticAt ℂ (fun w => errorVector m f ε n w i) z) ∧
      ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
        (fun z => ∑ j, leadingMatrix m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => errorVector m f ε n z i+
            ∑ a∈Finset.range n, ∑ j, shiftMatrix m f ε a z i j*G (z+((a:ℂ)+1)) j) := by
  obtain ⟨B,hF,hH,hrow⟩ := matrix_system_of_law hm hf ε hlaw
  have hrows : ∀ n z, B<z.re → ∀ i,
      ∑ j, leadingMatrix m f ε z i j*gridVector (2*m) f z j=
        errorVector m f ε n z i+
          ∑ a∈Finset.range n, ∑ j, shiftMatrix m f ε a z i j*
            gridVector (2*m) f (z+((a:ℂ)+1)) j := by
    intro n z hz i
    simpa only [Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using
      congrFun (hrow n z hz) i
  obtain ⟨G,hG,heG⟩ := SmallLevelContinuation.closed_system_continuation B
    (gridVector (2*m) f) (leadingMatrix m f ε) (shiftMatrix m f ε) (errorVector m f ε)
    hF (leadingMatrix_analytic m f ε) (original_leadingMatrix_nonsingular hf ε hε)
    (shiftMatrix_analytic m f ε) hH hrows
  refine ⟨B,G,hG,heG,?_,hH,?_⟩
  · intro i z hz
    apply (hF i z hz).congr
    have hn : ∀ᶠ w in 𝓝 z, B<w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hn] with w hw
    exact (congrFun (heG w hw) i).symm
  · exact SmallLevelContinuation.continued_rows B (gridVector (2*m) f) G
      (leadingMatrix m f ε) (shiftMatrix m f ε) (errorVector m f ε)
      (fun i z => (hG i z).meromorphicAt) heG (leadingMatrix_analytic m f ε)
      (shiftMatrix_analytic m f ε) hH hrow


#print axioms continued_system_of_law
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneComplexRatesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex SmallLevelTaylor

compact_certificate
theorem positive_zpow_cpow {p : ℝ} (hp : 0<p) (a : ℤ) (s : ℂ) :
    ((p:ℂ)^a)^s=((p:ℂ)^(-s))^(-a) := by
  have harg : (p:ℂ).arg=0 := arg_ofReal_of_nonneg hp.le
  rw [← Complex.cpow_int_mul' (by simp [harg,Real.pi_pos])
    (by simp [harg,Real.pi_pos.le]),← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

compact_certificate
theorem rate_complex_power (i : Fin 28) (s : ℂ) :
    (rowRate i:ℂ)^s=rateMonomial i ((2:ℂ)^(-s)) ((3:ℂ)^(-s)) ((7:ℂ)^(-s)) := by
  have hr : (rowRate i:ℝ)=(2:ℝ)^(ratePowers i).1*
      (3:ℝ)^(ratePowers i).2.1*(7:ℝ)^(ratePowers i).2.2 := by
    simpa only [Rat.cast_mul,Rat.cast_zpow,Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q:ℝ)) (rate_certificate i)
  have he : (rowRate i:ℂ)=(((2:ℝ)^(ratePowers i).1*
      (3:ℝ)^(ratePowers i).2.1*(7:ℝ)^(ratePowers i).2.2:ℝ):ℂ) := by
    simpa only [Complex.ofReal_ratCast] using congrArg (fun r : ℝ => (r:ℂ)) hr
  rw [he,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
  simp only [Complex.ofReal_zpow]
  rw [positive_zpow_cpow (by norm_num : (0:ℝ)<2),
    positive_zpow_cpow (by norm_num : (0:ℝ)<3),
    positive_zpow_cpow (by norm_num : (0:ℝ)<7)]
  rfl

compact_certificate
/-- The exact Laurent specialization holds at every complex point, not
only at the integer sequence used to witness nonsingularity. -/
theorem rowCoefficient_complex (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 28) :
    rowCoefficient (2*m) f ε i 0 s=
      phaseRoot m ε*localRoot (rootU f) (rootV f) (rowQ i)*
        rateMonomial i ((2:ℂ)^((m:ℂ)-s)) ((3:ℂ)^((m:ℂ)-s)) ((7:ℂ)^((m:ℂ)-s)) := by
  unfold rowCoefficient taylorRowScalar
  simp only [pow_zero,mul_one,Ring.choose_zero_right]
  rw [selected_root_scalar]
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  rw [hex]
  have hr : (((rowL i:ℝ)*((rowT i:ℝ)/42)^2:ℝ):ℂ)=(rowRate i:ℂ) := by
    unfold rowRate
    push_cast
    rfl
  rw [hr,rate_complex_power,neg_sub]

#print axioms rate_complex_power
#print axioms rowCoefficient_complex
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneComplexMatrixV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix SmallLevelTaylor FinitenessRamanujanSum

compact_certificate
theorem leadingRows_complex (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (w : Fin 42 → ℂ) :
    leadingRows m f ε s w=
      laurentRows (phaseRoot m ε) (rootU f) (rootV f)
        ((2:ℂ)^((m:ℂ)-s)) ((3:ℂ)^((m:ℂ)-s)) ((7:ℂ)^((m:ℂ)-s))
        ((Real.sqrt 2:ℂ)*f 2) w := by
  unfold leadingRows taylorLeading heckeLeading
  simp_rw [rowCoefficient_complex]
  funext i
  fin_cases i <;>
    norm_num [laurentRows,sampleSum,residues,rowQ,rowT,rowPartner,rowD,rowL,taylorSpecs,
      heckeSpecs,gridIndex,Finset.sum_filter,Finset.sum_range_succ,rateMonomial,ratePowers,localRoot] <;>
    ring1

compact_certificate
theorem leadingMatrix_complex (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) :
    leadingMatrix m f ε s=
      laurentMatrix (phaseRoot m ε) (rootU f) (rootV f)
        ((2:ℂ)^((m:ℂ)-s)) ((3:ℂ)^((m:ℂ)-s)) ((7:ℂ)^((m:ℂ)-s))
        ((Real.sqrt 2:ℂ)*f 2) := by
  ext i j
  rw [leadingMatrix_apply,laurentMatrix_apply,leadingRows_complex]

def originalDeterminantFactor (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : ℂ :=
  determinantFactor (phaseRoot m ε) (rootU f) (rootV f)
    ((2:ℂ)^((m:ℂ)-s)) ((3:ℂ)^((m:ℂ)-s)) ((7:ℂ)^((m:ℂ)-s)) ((Real.sqrt 2:ℂ)*f 2)

compact_certificate
/-- Every singularity of the actual leading matrix lies on the explicit
Laurent determinant locus, uniformly in the unrestricted Hecke eigenvalue. -/
theorem original_singular_factor {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) {ε s : ℂ}
    (hε : ε=1 ∨ ε= -1) (hs : (leadingMatrix m f ε s).det=0) :
    originalDeterminantFactor m f ε s=0 := by
  by_contra hD
  have hn := laurentMatrix_det_ne_zero (phaseRoot m ε) (rootU f) (rootV f)
    ((2:ℂ)^((m:ℂ)-s)) ((3:ℂ)^((m:ℂ)-s)) ((7:ℂ)^((m:ℂ)-s)) ((Real.sqrt 2:ℂ)*f 2)
    (phaseRoot_sign m hε) (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) hD
  rw [leadingMatrix_complex] at hs
  exact hn hs

#print axioms leadingMatrix_complex
#print axioms original_singular_factor
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneFullTaylorGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOne
open Complex Matrix Filter Set SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct
open scoped Topology

def fullTaylorCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t : ℤ) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (Nat.lcm 21 (q^2)) ((t:ℝ)/42)
    (root 21 f q*ε*I^k) n s

def fullTaylorError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t : ℤ) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f q) k)
    (Nat.lcm 21 (q^2)) ((t:ℝ)/42) (root 21 f q*ε*I^k) (M+1)) s

compact_certificate
theorem fullTaylorCoefficient_analytic (k : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    {q : ℕ} (hq : 0<q) {t : ℤ} (ht : t≠0) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fullTaylorCoefficient k f ε q t n) s := by
  apply taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<21) (pow_pos hq 2)
  · exact div_ne_zero (by exact_mod_cast ht) (by norm_num)

compact_certificate
theorem sampleSum_meromorphic (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicAt (fun w => G w i) z)
    (q : ℕ) (t : ℤ) (s : ℂ) :
    MeromorphicAt (fun z => sampleSum q t (G z)) s := by
  apply MeromorphicAt.fun_sum
  intro j _
  exact hG (gridIndex (t+(j:ℤ)*(42/q:ℕ))) s

compact_certificate
/-- Every closed Ramanujan Taylor row continues on the actual 42-grid,
not just the 28 rows selected to prove continuation. One original Fricke
sign works simultaneously for the whole family. -/
theorem full_taylor_germs_of_law {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) :
    ∀ q : ℕ, 0<q → q∣42 →
      ∀ t d : ℤ, t≠0 → (Nat.lcm 21 (q^2):ℤ)*d=(42:ℤ)^2 → t∣d →
      ∃ B : ℝ, ∀ M : ℕ,
        AnalyticOnNhd ℂ (fullTaylorError (2*m) f ε q t M)
          {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
        ∀ x : ℂ, B-((M:ℝ)+1)<x.re →
          (fun z => sampleSum q t (G z)-
            fullTaylorCoefficient (2*m) f ε q t 0 z*sampleSum q (-(d/t)) (G z))
            =ᶠ[𝓝[≠] x]
          (fun z => fullTaylorError (2*m) f ε q t M z+
            ∑ n∈Finset.range M, fullTaylorCoefficient (2*m) f ε q t (n+1) z*
              sampleSum q (-(d/t)) (G (z+((n:ℂ)+1)))) := by
  have hrows := QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
    (by decide : 0<21) (even_two_mul m) hf ε hlaw
  intro q hq hqQ t d ht hd htd
  obtain ⟨B,hB⟩ := hrows 42 q (by decide) hq hqQ t d ht hd htd
  refine ⟨B,?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro x hx
  have hS (q : ℕ) (t : ℤ) (s : ℂ) :=
    sampleSum_meromorphic G (fun i z => (hG i z).meromorphicAt) q t s
  have hFG (q : ℕ) (t : ℤ) (z : ℂ) (hz : BG<z.re) :
      sampleSum q t (G z)=gridSum (2*m) f 42 q t z := by
    rw [hGF z hz,sampleSum_grid]
  apply SmallLevelContinuation.halfplane_germ_identity
    (B-((M:ℝ)+1)) (max B BG) _ _ _ x hx
  · intro z _
    exact (hS q t z).sub ((fullTaylorCoefficient_analytic (2*m) f ε hq ht 0 z).meromorphicAt.mul
      (hS q (-(d/t)) z))
  · intro z hz
    apply ((hB M).1 z hz).meromorphicAt.add
    apply MeromorphicAt.fun_sum
    intro n _
    exact (fullTaylorCoefficient_analytic (2*m) f ε hq ht (n+1) z).meromorphicAt.mul
      ((hS q (-(d/t)) (z+((n:ℂ)+1))).comp_analyticAt
        (g:=fun w : ℂ => w+((n:ℂ)+1)) (by fun_prop))
  · intro z hz
    have hzB : B<z.re := lt_of_le_of_lt (le_max_left B BG) hz
    have hzG : BG<z.re := lt_of_le_of_lt (le_max_right B BG) hz
    dsimp only
    rw [hFG q t z hzG,hFG q (-(d/t)) z hzG]
    have he := (hB M).2 z hzB
    change gridSum (2*m) f 42 q t z-
      fullTaylorCoefficient (2*m) f ε q t 0 z*gridSum (2*m) f 42 q (-(d/t)) z=
      fullTaylorError (2*m) f ε q t M z+
        ∑ n∈Finset.range M, fullTaylorCoefficient (2*m) f ε q t (n+1) z*
          gridSum (2*m) f 42 q (-(d/t)) (z+((n:ℂ)+1)) at he
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have hs : BG<(z+((n:ℂ)+1)).re := by
      simp only [Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [hFG q (-(d/t)) _ hs]


#print axioms fullTaylorCoefficient_analytic
#print axioms sampleSum_meromorphic
#print axioms full_taylor_germs_of_law
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneFullHeckeGermsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix Filter Set SmallLevelTaylor SmallLevelAdditive
open scoped Topology

def completeSum (p : ℕ) (t : ℤ) (w : Fin 42 → ℂ) : ℂ :=
  ∑ a∈Finset.range p, w (gridIndex (t+(a:ℤ)*(42/p:ℕ)))

def fullHeckeRow (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (j : ℤ)
    (s : ℂ) (v : Fin 42 → ℂ) : ℂ :=
  completeSum p j v-((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-s)*v (gridIndex ((p:ℤ)*j))+
    if p∣21 then 0 else ((p:ℂ)^((m:ℂ)-s))^2*v (gridIndex ((p:ℤ)^2*j))

compact_certificate
theorem fullHeckeRow_grid (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (j : ℤ) (s : ℂ) :
    fullHeckeRow m f p j s (gridVector (2*m) f s)=
      SmallLevelTwentyOneFullHecke.heckeLeading m f p j s := by
  simp only [fullHeckeRow,completeSum,gridVector_index,
    SmallLevelTwentyOneFullHecke.heckeLeading]

compact_certificate
theorem fullHeckeRow_meromorphic (m : ℕ) (f : ℕ → ℂ)
    {p : ℕ} (hp : 0<p) (j : ℤ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicAt (fun w => G w i) z) (s : ℂ) :
    MeromorphicAt (fun z => fullHeckeRow m f p j z (G z)) s := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  have hP : AnalyticAt ℂ (fun z : ℂ => (p:ℂ)^((m:ℂ)-z)) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hp0]
    fun_prop
  have hsum : MeromorphicAt (fun z => completeSum p j (G z)) s := by
    apply MeromorphicAt.fun_sum
    intro a _
    exact hG _ s
  unfold fullHeckeRow
  apply (hsum.sub ((analyticAt_const.mul hP).meromorphicAt.mul (hG _ s))).add
  by_cases hb : p∣21
  · simpa only [ite_eq_left hb] using (analyticAt_const (v := (0:ℂ))).meromorphicAt
  · simpa only [ite_eq_right hb] using (hP.fun_pow 2).meromorphicAt.fun_mul (hG _ s)

compact_certificate
/-- Every good or bad prime row on the closed grid holds after continuation,
for every numerator. No prime eigenvalue is assumed nonzero. -/
theorem original_full_hecke_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    {p : ℕ} (hp : p.Prime) (hpQ : p∣42) (j : ℤ) (x : ℂ) :
    (fun z => fullHeckeRow m f p j z (G z))=ᶠ[𝓝[≠] x] (fun _ => 0) := by
  obtain ⟨B,hB⟩ := SmallLevelTwentyOneFullHecke.original_hecke_grid
    hm hf hp hpQ
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact fullHeckeRow_meromorphic m f hp.pos j G (fun i w => (hG i w).meromorphicAt) z
  · intro z _
    exact analyticAt_const.meromorphicAt
  · intro z hz
    dsimp only
    rw [hGF z (lt_of_le_of_lt (le_max_right B BG) hz),fullHeckeRow_grid]
    exact hB j z (lt_of_le_of_lt (le_max_left B BG) hz)

compact_certificate
/-- Every primitive Ramanujan sum on the grid is an actual entire Mellin
transform as a germ, not merely the eleven rows used in the selected matrix. -/
theorem original_full_entire_germs {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun w => G w i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    {q : ℕ} (hq : 0<q) (hqQ : q∣42) :
    (∀ x : ℂ, AnalyticAt ℂ (ramanujanEntire 21 (2*m) f q) x) ∧
      ∀ x : ℂ, (fun z => sampleSum q 0 (G z))=ᶠ[𝓝[≠] x]
        ramanujanEntire 21 (2*m) f q := by
  obtain ⟨hE,B,hB⟩ := original_ramanujan_entire (by decide : 0<21) (by omega : 0<2*m) hf hq
  refine ⟨hE,?_⟩
  intro x
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact sampleSum_meromorphic G (fun i w => (hG i w).meromorphicAt) q 0 z
  · intro z _
    exact (hE z).meromorphicAt
  · intro z hz
    dsimp only
    rw [hGF z (lt_of_le_of_lt (le_max_right B BG) hz),sampleSum_grid,
      hB z (lt_of_le_of_lt (le_max_left B BG) hz)]
    have he := ramanujanAdditive_grid (2*m) f (by decide : 0<42) hq hqQ 0 z
    simpa only [Int.cast_zero,zero_div,gridSum] using he.symm

#print axioms fullHeckeRow_grid
#print axioms fullHeckeRow_meromorphic
#print axioms original_full_hecke_germs
#print axioms original_full_entire_germs
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneLargeGridRootV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOne
open Complex FinitenessNormalizedTwistProduct

compact_certificate
/-- Multiplying a grid divisor by the good prime5 introduces no local sign. -/
theorem root_mul_five {q : ℕ} (hq : 0<q) (f : ℕ → ℂ) :
    root 21 f (5*q)=root 21 f q := by
  have hsign (n : ℕ) : FinitenessNormalizedTwistLocal.sign 21 f 5 n=1 := by
    by_cases hn : n=0 <;> simp [FinitenessNormalizedTwistLocal.sign,hn]
  have hterm (p : ℕ) (hp : p∈q.primeFactors) :
      FinitenessNormalizedTwistLocal.sign 21 f p ((5*q).factorization p)=
        FinitenessNormalizedTwistLocal.sign 21 f p (q.factorization p) := by
    obtain ⟨hprime,hdiv,hq0⟩ := Nat.mem_primeFactors.mp hp
    have hdiv' : p∣5*q := dvd_mul_of_dvd_right hdiv 5
    have hqf : q.factorization p≠0 := (hprime.factorization_pos_of_dvd hq0 hdiv).ne'
    have hqf' : (5*q).factorization p≠0 :=
      (hprime.factorization_pos_of_dvd (mul_ne_zero (by decide) hq0) hdiv').ne'
    simp only [FinitenessNormalizedTwistLocal.sign,hqf,hqf',ite_false]
  unfold root
  rw [Nat.primeFactors_mul (by decide : (5:ℕ)≠0) hq.ne']
  rw [(by decide : Nat.Prime 5).primeFactors]
  simp only [Finset.singleton_union]
  by_cases h5 : 5∈q.primeFactors
  · rw [Finset.insert_eq_of_mem h5]
    exact Finset.prod_congr rfl hterm
  · rw [Finset.prod_insert h5,hsign,one_mul]
    exact Finset.prod_congr rfl hterm

compact_certificate
/-- Every divisor of210 has exactly the same bad-prime signs as its
42-part. This includes all new Ramanujan rows at moduli divisible by5. -/
theorem root_large_grid_divisor (f : ℕ → ℂ) {q : ℕ} (hq : q∣210) :
    root 21 f q=localRoot (rootU f) (rootV f) q := by
  have hd : Nat.divisors 210=({1,2,3,5,6,7,10,14,15,21,30,35,42,70,105,210}:Finset ℕ) := by decide
  have hm := Nat.mem_divisors.mpr ⟨hq,(by decide : (210:ℕ)≠0)⟩
  rw [hd] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact root_grid_divisor f (by decide)
  · exact root_grid_divisor f (by decide)
  · exact root_grid_divisor f (by decide)
  · change root 21 f (5*1)=_
    rw [root_mul_five (by decide : 0<1),root_grid_divisor f (by decide)]
    norm_num [localRoot]
  · exact root_grid_divisor f (by decide)
  · exact root_grid_divisor f (by decide)
  · change root 21 f (5*2)=_
    rw [root_mul_five (by decide : 0<2),root_grid_divisor f (by decide)]
    norm_num [localRoot]
  · exact root_grid_divisor f (by decide)
  · change root 21 f (5*3)=_
    rw [root_mul_five (by decide : 0<3),root_grid_divisor f (by decide)]
    norm_num [localRoot]
  · exact root_grid_divisor f (by decide)
  · change root 21 f (5*6)=_
    rw [root_mul_five (by decide : 0<6),root_grid_divisor f (by decide)]
    norm_num [localRoot]
  · change root 21 f (5*7)=_
    rw [root_mul_five (by decide : 0<7),root_grid_divisor f (by decide)]
    norm_num [localRoot]
  · exact root_grid_divisor f (by decide)
  · change root 21 f (5*14)=_
    rw [root_mul_five (by decide : 0<14),root_grid_divisor f (by decide)]
    norm_num [localRoot]
  · change root 21 f (5*21)=_
    rw [root_mul_five (by decide : 0<21),root_grid_divisor f (by decide)]
    norm_num [localRoot]
  · change root 21 f (5*42)=_
    rw [root_mul_five (by decide : 0<42),root_grid_divisor f (by decide)]
    norm_num [localRoot]

#print axioms root_mul_five
#print axioms root_large_grid_divisor
end SmallLevelTwentyOne
end
end

/-! ## SmallLevelTwentyOneRankCertificateV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelTwentyOne
open Complex Matrix

compact_certificate
/-- All eight original sign cases of the exact 42-row kernel certificate. -/
theorem laurent_rank_coordinate (E u v X Y Z lam : ℂ)
    (hE : E=1 ∨ E= -1) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 42 → ℂ) (hw : laurentRows E u v X Y Z lam w=0) (hzero : w 28=0) : w=0 := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
  · exact laurent_rank_case7 X Y Z lam hX hY hZ w hw hzero
  · exact laurent_rank_case6 X Y Z lam hX hY hZ w hw hzero
  · exact laurent_rank_case5 X Y Z lam hX hY hZ w hw hzero
  · exact laurent_rank_case4 X Y Z lam hX hY hZ w hw hzero
  · exact laurent_rank_case3 X Y Z lam hX hY hZ w hw hzero
  · exact laurent_rank_case2 X Y Z lam hX hY hZ w hw hzero
  · exact laurent_rank_case1 X Y Z lam hX hY hZ w hw hzero
  · exact laurent_rank_case0 X Y Z lam hX hY hZ w hw hzero

compact_certificate
/-- The actual leading matrix has kernel dimension at most one, including
at its singular points and for every Hecke eigenvalue. -/
theorem original_rank_coordinate {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) {ε s : ℂ}
    (hε : ε=1 ∨ ε= -1) (w : Fin 42 → ℂ)
    (hw : leadingMatrix m f ε s *ᵥ w=0) (hzero : w 28=0) : w=0 := by
  rw [leadingMatrix_complex,laurentMatrix_mulVec] at hw
  exact laurent_rank_coordinate (phaseRoot m ε) (rootU f) (rootV f)
    ((2:ℂ)^((m:ℂ)-s)) ((3:ℂ)^((m:ℂ)-s)) ((7:ℂ)^((m:ℂ)-s)) ((Real.sqrt 2:ℂ)*f 2)
    (phaseRoot_sign m hε) (rootU_sign hf.toEulerData) (rootV_sign hf.toEulerData)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) w hw hzero

compact_certificate
theorem original_normalized_kernel_unique {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) {ε s : ℂ}
    (hε : ε=1 ∨ ε= -1)
    (hker : ∃ v : Fin 42 → ℂ, v≠0 ∧ leadingMatrix m f ε s *ᵥ v=0) :
    ∃! w : Fin 42 → ℂ, leadingMatrix m f ε s *ᵥ w=0 ∧ w 28=1 := by
  obtain ⟨v,hv,hAv⟩ := hker
  have h28 : v 28≠0 := fun h => hv (original_rank_coordinate hf hε v hAv h)
  let w : Fin 42 → ℂ := (v 28)⁻¹ • v
  have hw : leadingMatrix m f ε s *ᵥ w=0 := by
    simp only [w,Matrix.mulVec_smul,hAv,smul_zero]
  have hw28 : w 28=1 := by simp [w,h28]
  refine ⟨w,⟨hw,hw28⟩,?_⟩
  intro z hz
  apply sub_eq_zero.mp
  apply original_rank_coordinate hf hε (z-w)
  · rw [Matrix.mulVec_sub,hz.1,hw,sub_self]
  · simp only [Pi.sub_apply,hz.2,hw28,sub_self]

#print axioms laurent_rank_coordinate
#print axioms original_rank_coordinate
#print axioms original_normalized_kernel_unique
end SmallLevelTwentyOne
end
end
end
