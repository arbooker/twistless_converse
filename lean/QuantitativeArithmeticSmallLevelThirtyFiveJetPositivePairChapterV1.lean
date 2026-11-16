module
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticSmallLevelThirtyFiveJetPositiveGridChapterV1

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import QuantitativeArithmeticCompact35JetRowsNegative118TheoryV4
public import QuantitativeArithmeticCompact35JetRowsNegativeATheoryV4
public import QuantitativeArithmeticCompact35JetRowsNegativeBTheoryV4
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFivePositiveLastPairReducedRowsBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

certificate_batch {
theorem positive_last_pair_reduced_rows_chunk0 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h0 : (1)*v 0 + ((-1)*x^(2:ℕ)*z*w)*v 207 = 0)
    (h2 : (1)*v 0 + ((-1)*z*w)*v 204 = 0)
    (h8 : (1)*v 0 = 0)
    (h12 : ((-1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 2 = 0)
    (h16 : (1)*v 4 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z*w))*v 105 = 0)
    (h20 : ((-1)/(z*w))*v 0 + (1)*v 6 = 0)
    (h28 : (1)*v 12 + (((-1)*x^(2:ℕ))/(z*w))*v 105 = 0)
    (h62 : (1)*v 105 + (((-1)*z*w)/(x^(2:ℕ)))*v 198 = 0)
    (h128 : ((-1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 208 = 0)
    (h246 : (1)*v 102 + ((-1)*y^(2:ℕ))*v 208 = 0)
    (h248 : ((-1)/(x^(2:ℕ)))*v 0 + (1)*v 105 = 0)
    (h252 : (1)*v 108 + ((-1)*x^(2:ℕ))*v 207 = 0)
    (h360 : (1)*v 174 + (-1)*v 204 = 0)
    (h362 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 175 = 0)
    (h2796 : ((-1)/(z*w))*v 0 + ((-1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0)
    (h2798 : ((-1)/(z*w))*v 0 + (1)*v 68 + (1)*v 138 + ((-1)/(z*w))*v 140 = 0)
    (h2800 : (((-1)*x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + (((-1)*x^(2:ℕ))/(z*w))*v 105 + (1)*v 144 = 0)
    (h2802 : (1)*v 66 + (((-1)*x^(2:ℕ))/(z*w))*v 105 + (1)*v 136 + (((-1)*x^(2:ℕ))/(z*w))*v 175 = 0)
    (h2844 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 0 + (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h2846 : ((-1)/(y^(2:ℕ)*w))*v 0 + (1)*v 44 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + ((-1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0)
    (h2848 : ((-1)/(y^(2:ℕ)*w))*v 0 + (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((-1)/(y^(2:ℕ)*w))*v 168 = 0)
    (h2850 : ((-1)/(x^(2:ℕ)*w))*v 0 + (1)*v 45 + (1)*v 87 + (1)*v 129 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0)
    (h2854 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 130 + (1)*v 172 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2856 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2858 : ((-1)/(w))*v 0 + (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0)
    (h2860 : ((-1)/(w))*v 0 + (1)*v 36 + (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0)
    (h2872 : (1)*v 30 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 105 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + (((-1)*x^(2:ℕ))/(w))*v 189 = 0)
    (h2876 : (1)*v 28 + (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (((-1)*w)/(y^(2:ℕ)))*v 102 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0)
    (h2936 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 0 + (1)*v 29 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0)
    (h2950 : (1)*v 35 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 204 = 0)
    (h3060 : ((-1)/(x^(2:ℕ)*w))*v 0 + (1)*v 15 + ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h3064 : ((-1)/(w))*v 0 + ((-1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0)
    (h3092 : ((-1)/(z))*v 0 + (1)*v 8 + (1)*v 18 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + (1)*v 108 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + ((-1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + (1)*v 198 + ((-1)/(z))*v 200 = 0)
    (h3206 : (1)*v 2 + (((-1)*a)/(x))*v 4 + ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0)
    (h3210 : (1)*v 4 + (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0)
    (h3304 : (1)*v 51 + (((-1)*a)/(x))*v 102 + (1)*v 156 + ((1)/(x^(2:ℕ)))*v 204 = 0)
    (h3310 : ((1)/(x^(2:ℕ)))*v 6 + (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0)
    (h3358 : (1)*v 78 + ((1)/(x^(2:ℕ)))*v 102 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0)
    (h3424 : (1)*v 6 + (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0)
    (h3528 : (1)*v 58 + ((1)/(y^(2:ℕ)))*v 102 + (1)*v 128 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0)
    : (1)*v 175 = 0 ∧
      ((-1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0 ∧
      (1)*v 68 + (1)*v 138 + ((-1)/(z*w))*v 140 = 0 ∧
      (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 44 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + ((-1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0 ∧
      (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((-1)/(y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 45 + (1)*v 87 + (1)*v 129 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0 ∧
      (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0 ∧
      (1)*v 36 + (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0 ∧
      (1)*v 29 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0 ∧
      (1)*v 15 + ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0 ∧
      ((-1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0 ∧
      (1)*v 8 + (1)*v 18 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + (1)*v 108 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + ((-1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + (1)*v 198 + ((-1)/(z))*v 200 = 0 ∧
      (1)*v 108 = 0 ∧
      (1)*v 174 = 0 ∧
      (1)*v 35 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 ∧
      (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0 ∧
      (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 ∧
      (1)*v 28 + (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 51 + (1)*v 156 = 0 ∧
      (1)*v 78 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0 ∧
      (1)*v 58 + (1)*v 128 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0 ∧
      (1)*v 12 = 0 ∧
      (((-1)*z*w)/(x^(2:ℕ)))*v 198 = 0 ∧
      (((-1)*x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + (1)*v 144 = 0 ∧
      (1)*v 66 + (1)*v 136 + (((-1)*x^(2:ℕ))/(z*w))*v 175 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + (1)*v 172 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0 ∧
      (1)*v 30 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + (((-1)*x^(2:ℕ))/(w))*v 189 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0 ∧
      (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0 := by
  have h14126 : (1)*v 0 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h8
  have h14127 : ((-1)*x^(2:ℕ)*z*w)*v 207 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h0-(1)*h14126
  have h14128 : ((-1)*z*w)*v 204 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2-(1)*h14126
  have h14130 : (1)*v 2 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h12-((-1)/(y^(2:ℕ)*z*w))*h14126
  have h14132 : (1)*v 6 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20-((-1)/(z*w))*h14126
  have h14136 : (1)*v 208 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h128-((-1)/(y^(2:ℕ)*z*w))*h14126
  have h14139 : (1)*v 105 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h248-((-1)/(x^(2:ℕ)))*h14126
  have h14144 : (1)*v 175 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h362-((-1)/(x^(2:ℕ)*y^(2:ℕ)))*h14126
  have h14320 : ((-1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2796-((-1)/(z*w))*h14126
  have h14321 : (1)*v 68 + (1)*v 138 + ((-1)/(z*w))*v 140 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2798-((-1)/(z*w))*h14126
  have h14327 : (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2844-((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*h14126
  have h14328 : (1)*v 44 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + ((-1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2846-((-1)/(y^(2:ℕ)*w))*h14126
  have h14329 : (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((-1)/(y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2848-((-1)/(y^(2:ℕ)*w))*h14126
  have h14330 : (1)*v 45 + (1)*v 87 + (1)*v 129 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2850-((-1)/(x^(2:ℕ)*w))*h14126
  have h14332 : (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2858-((-1)/(w))*h14126
  have h14333 : (1)*v 36 + (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2860-((-1)/(w))*h14126
  have h14347 : (1)*v 29 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2936-((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*h14126
  have h14378 : (1)*v 15 + ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3060-((-1)/(x^(2:ℕ)*w))*h14126
  have h14380 : ((-1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3064-((-1)/(w))*h14126
  have h14389 : (1)*v 8 + (1)*v 18 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + (1)*v 108 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + ((-1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + (1)*v 198 + ((-1)/(z))*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3092-((-1)/(z))*h14126
  have h14618 : (1)*v 207 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(x^(2:ℕ)*z*w))*h14127
  have h14626 : (1)*v 108 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h252-((-1)*x^(2:ℕ))*h14618
  have h14693 : (1)*v 204 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(z*w))*h14128
  have h14707 : (1)*v 174 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h360-(-1)*h14693
  have h14755 : (1)*v 35 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2950-(((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*h14693
  have h14780 : (1)*v 51 + (((-1)*a)/(x))*v 102 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3304-((1)/(x^(2:ℕ)))*h14693
  have h14861 : (1)*v 2 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h14130
  have h14901 : (((-1)*a)/(x))*v 4 + ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3206-(1)*h14861
  have h15005 : (1)*v 6 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h14132
  have h15128 : (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3310-((1)/(x^(2:ℕ)))*h15005
  have h15130 : (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3424-(1)*h15005
  have h15186 : (1)*v 208 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h14136
  have h15191 : (1)*v 102 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h246-((-1)*y^(2:ℕ))*h15186
  have h15249 : (1)*v 102 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h15191
  have h15281 : (1)*v 28 + (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2876-(((-1)*w)/(y^(2:ℕ)))*h15249
  have h15308 : (1)*v 51 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14780-(((-1)*a)/(x))*h15249
  have h15309 : (1)*v 78 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3358-((1)/(x^(2:ℕ)))*h15249
  have h15313 : (1)*v 58 + (1)*v 128 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3528-((1)/(y^(2:ℕ)))*h15249
  have h15342 : (1)*v 105 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h14139
  have h15344 : (1)*v 4 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*z*w))*h15342
  have h15345 : (1)*v 12 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h28-(((-1)*x^(2:ℕ))/(z*w))*h15342
  have h15346 : (((-1)*z*w)/(x^(2:ℕ)))*v 198 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h62-(1)*h15342
  have h15432 : (((-1)*x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + (1)*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2800-(((-1)*x^(2:ℕ))/(z*w))*h15342
  have h15433 : (1)*v 66 + (1)*v 136 + (((-1)*x^(2:ℕ))/(z*w))*v 175 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2802-(((-1)*x^(2:ℕ))/(z*w))*h15342
  have h15436 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + (1)*v 172 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2854-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h15342
  have h15437 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2856-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h15342
  have h15439 : (1)*v 30 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + (((-1)*x^(2:ℕ))/(w))*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2872-(((-1)*x^(2:ℕ))/(w))*h15342
  have h15612 : (1)*v 4 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h15344
  have h15648 : ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14901-(((-1)*a)/(x))*h15612
  have h15649 : (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3210-(1)*h15612
  exact ⟨h14144, h14320, h14321, h14327, h14328, h14329, h14330, h14332, h14333, h14347, h14378, h14380, h14389, h14626, h14707, h14755, h15128, h15130, h15281, h15308, h15309, h15313, h15345, h15346, h15432, h15433, h15436, h15437, h15439, h15648, h15649⟩

#print axioms positive_last_pair_reduced_rows_chunk0

theorem positive_last_pair_reduced_rows_chunk1 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h4 : (((-1)*x^(2:ℕ)*y^(2:ℕ)*w)/(z))*v 205 = 0)
    (h18 : (1)*v 5 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h22 : (1)*v 7 + (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0)
    (h26 : (1)*v 10 = 0)
    (h30 : (1)*v 14 + (((-1)*w)/(y^(2:ℕ)*z))*v 120 = 0)
    (h32 : (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h34 : (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0)
    (h44 : (1)*v 35 + (((-1)*z*w)/(x^(2:ℕ)*y^(2:ℕ)))*v 174 = 0)
    (h46 : (1)*v 36 + (((-1)*x^(2:ℕ)*y^(2:ℕ))/(z*w))*v 175 = 0)
    (h266 : (1)*v 110 + ((-1)*x^(2:ℕ))*v 205 = 0)
    (h2866 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 14 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0)
    (h2874 : (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (((-1)*w)/(y^(2:ℕ)))*v 108 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0)
    (h3032 : (1)*v 15 + (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0)
    (h3058 : (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0)
    (h3084 : (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0)
    (h3212 : (1)*v 5 + (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 = 0)
    (h3216 : (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112 = 0)
    (h3226 : (1)*v 12 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0)
    (h3230 : (1)*v 14 + (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0)
    (h3232 : (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 = 0)
    (h3256 : (1)*v 27 + (((-1)*a)/(x))*v 54 + ((1)/(x^(2:ℕ)))*v 108 + (1)*v 132 = 0)
    (h3376 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 + (((-1)*a)/(x))*v 174 = 0)
    (h3426 : (1)*v 7 + (((-1)*b)/(y))*v 21 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0)
    (h3432 : (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0)
    (h3436 : (1)*v 12 + (((-1)*b)/(y))*v 36 + (1)*v 82 + ((1)/(y^(2:ℕ)))*v 108 + (1)*v 152 = 0)
    (h14144 : (1)*v 175 = 0)
    (h14332 : (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0)
    (h14333 : (1)*v 36 + (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0)
    (h14378 : (1)*v 15 + ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h14380 : ((-1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0)
    (h14389 : (1)*v 8 + (1)*v 18 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + (1)*v 108 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + ((-1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + (1)*v 198 + ((-1)/(z))*v 200 = 0)
    (h14626 : (1)*v 108 = 0)
    (h14707 : (1)*v 174 = 0)
    (h14755 : (1)*v 35 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0)
    (h15128 : (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0)
    (h15313 : (1)*v 58 + (1)*v 128 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0)
    (h15345 : (1)*v 12 = 0)
    (h15346 : (((-1)*z*w)/(x^(2:ℕ)))*v 198 = 0)
    (h15432 : (((-1)*x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + (1)*v 144 = 0)
    (h15433 : (1)*v 66 + (1)*v 136 + (((-1)*x^(2:ℕ))/(z*w))*v 175 = 0)
    : ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0 ∧
      (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0 ∧
      (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0 ∧
      (1)*v 54 + (1)*v 159 = 0 ∧
      (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 = 0 ∧
      (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 58 + (1)*v 128 = 0 ∧
      (1)*v 74 + (1)*v 144 = 0 ∧
      (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 ∧
      (1)*v 66 + (1)*v 136 = 0 ∧
      (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0 ∧
      (1)*v 82 + (1)*v 152 = 0 ∧
      (1)*v 110 = 0 ∧
      (((-1)*b)/(y))*v 21 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0 ∧
      (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0 ∧
      (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + ((-1)/(x^(2:ℕ)*z))*v 120 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0 ∧
      (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0 ∧
      (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 28 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 112 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 = 0 ∧
      (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + ((w)/(y^(2:ℕ)*z))*v 120 = 0 ∧
      (1)*v 45 + (1)*v 75 + ((z)/(x^(2:ℕ)*w))*v 126 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0 ∧
      ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0 ∧
      (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 ∧
      (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 8 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + ((-1)/(z))*v 200 = 0 := by
  have h15666 : (1)*v 12 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h15345
  have h15740 : ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3226-(1)*h15666
  have h15742 : (((-1)*b)/(y))*v 36 + (1)*v 82 + ((1)/(y^(2:ℕ)))*v 108 + (1)*v 152 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3436-(1)*h15666
  have h15779 : (1)*v 198 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*x^(2:ℕ))/(z*w))*h15346
  have h15848 : ((-1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14380-(1)*h15779
  have h15850 : (1)*v 8 + (1)*v 18 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + (1)*v 108 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + ((-1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + ((-1)/(z))*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14389-(1)*h15779
  have h15873 : (1)*v 58 + (1)*v 128 + (((-1)*b)/(y))*v 174 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15313-(1)*h15779
  have h16004 : (1)*v 108 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h14626
  have h16074 : (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2874-(((-1)*w)/(y^(2:ℕ)))*h16004
  have h16082 : (1)*v 8 + (1)*v 18 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + ((-1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + ((-1)/(z))*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15850-(1)*h16004
  have h16102 : (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3256-((1)/(x^(2:ℕ)))*h16004
  have h16103 : (1)*v 54 + (1)*v 159 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15128-(((-1)*a)/(x))*h16004
  have h16104 : (((-1)*b)/(y))*v 36 + (1)*v 82 + (1)*v 152 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15742-((1)/(y^(2:ℕ)))*h16004
  have h16209 : (1)*v 174 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h14707
  have h16210 : (1)*v 35 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h44-(((-1)*z*w)/(x^(2:ℕ)*y^(2:ℕ)))*h16209
  have h16255 : (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14332-(1)*h16209
  have h16283 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3376-(((-1)*a)/(x))*h16209
  have h16286 : (1)*v 58 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15873-(((-1)*b)/(y))*h16209
  have h16336 : (1)*v 35 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16210
  have h16399 : (1)*v 74 + (1)*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15432-(((-1)*x^(2:ℕ))/(z*w))*h16336
  have h16404 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14755-(1)*h16336
  have h16452 : (1)*v 175 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h14144
  have h16453 : (1)*v 36 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h46-(((-1)*x^(2:ℕ)*y^(2:ℕ))/(z*w))*h16452
  have h16495 : (1)*v 66 + (1)*v 136 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15433-(((-1)*x^(2:ℕ))/(z*w))*h16452
  have h16553 : (1)*v 36 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16453
  have h16630 : (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14333-(1)*h16553
  have h16661 : (1)*v 82 + (1)*v 152 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16104-(((-1)*b)/(y))*h16553
  have h16707 : (1)*v 205 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*h4
  have h16711 : (1)*v 110 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h266-((-1)*x^(2:ℕ))*h16707
  have h16853 : (1)*v 5 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18
  have h16891 : (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3212-(1)*h16853
  have h16911 : (1)*v 7 + (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22
  have h16946 : (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 112 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3216-(1)*h16911
  have h16947 : (((-1)*b)/(y))*v 21 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3426-(1)*h16911
  have h17030 : (1)*v 10 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h26
  have h17060 : (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3084-(1)*h17030
  have h17077 : ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16891-(((-1)*a)/(x))*h17030
  have h17080 : (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3432-(1)*h17030
  have h17105 : (1)*v 14 + (((-1)*w)/(y^(2:ℕ)*z))*v 120 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h30
  have h17122 : (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + ((-1)/(x^(2:ℕ)*z))*v 120 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2866-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h17105
  have h17128 : (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3058-(1)*h17105
  have h17130 : (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15848-((-1)/(w))*h17105
  have h17145 : ((1)/(x^(2:ℕ)))*v 28 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 112 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16946-(((-1)*a)/(x))*h17105
  have h17146 : (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + ((w)/(y^(2:ℕ)*z))*v 120 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3230-(1)*h17105
  have h17170 : (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h32
  have h17201 : (1)*v 45 + (1)*v 75 + ((z)/(x^(2:ℕ)*w))*v 126 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3032-(1)*h17170
  have h17202 : ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14378-(1)*h17170
  have h17218 : (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3232-(1)*h17170
  have h17248 : (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h34
  have h17288 : (1)*v 8 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + ((-1)/(z))*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16082-(1)*h17248
  exact ⟨h15740, h16074, h16102, h16103, h16255, h16283, h16286, h16399, h16404, h16495, h16630, h16661, h16711, h16947, h17060, h17077, h17080, h17122, h17128, h17130, h17145, h17146, h17201, h17202, h17218, h17248, h17288⟩

#print axioms positive_last_pair_reduced_rows_chunk1

theorem positive_last_pair_reduced_rows_chunk2 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h36 : (1)*v 20 + (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0)
    (h38 : (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0)
    (h40 : (1)*v 28 + (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h42 : (1)*v 30 + (((-1)*z)/(w))*v 168 = 0)
    (h48 : (((-1)*w)/(z))*v 180 = 0)
    (h50 : (1)*v 45 + (((-1)*y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182 = 0)
    (h52 : (1)*v 60 + (((-1)*x^(2:ℕ)*z)/(w))*v 189 = 0)
    (h54 : (1)*v 63 + (((-1)*y^(2:ℕ)*w)/(x^(2:ℕ)*z))*v 190 = 0)
    (h68 : (1)*v 180 + (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0)
    (h294 : (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189 = 0)
    (h316 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98 = 0)
    (h320 : ((-1)/(y^(2:ℕ)))*v 30 + (1)*v 100 = 0)
    (h2932 : (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180 = 0)
    (h3006 : (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189 = 0)
    (h3242 : (1)*v 20 + (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0)
    (h3262 : (1)*v 30 + (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 = 0)
    (h3292 : (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180 = 0)
    (h3316 : ((1)/(x^(2:ℕ)))*v 18 + (1)*v 57 + (((-1)*a)/(x))*v 114 + (1)*v 162 = 0)
    (h3392 : (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (((-1)*a)/(x))*v 190 + (1)*v 200 = 0)
    (h3448 : (1)*v 18 + (((-1)*b)/(y))*v 54 + (1)*v 88 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h14347 : (1)*v 29 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0)
    (h15130 : (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0)
    (h15281 : (1)*v 28 + (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0)
    (h15436 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + (1)*v 172 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h15437 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h15439 : (1)*v 30 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + (((-1)*x^(2:ℕ))/(w))*v 189 = 0)
    (h16074 : (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0)
    (h16947 : (((-1)*b)/(y))*v 21 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0)
    (h17060 : (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0)
    (h17077 : ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h17080 : (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0)
    (h17128 : (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0)
    (h17130 : (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 = 0)
    (h17145 : ((1)/(x^(2:ℕ)))*v 28 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 112 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 = 0)
    (h17146 : (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + ((w)/(y^(2:ℕ)*z))*v 120 = 0)
    (h17202 : ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h17218 : (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h17248 : (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0)
    (h17288 : (1)*v 8 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + ((-1)/(z))*v 200 = 0)
    : (1)*v 57 + (((-1)*a)/(x))*v 114 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 162 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (((-1)*y*b)/(z*w))*v 140 + (1)*v 146 = 0 ∧
      (((-1)*b)/(y))*v 54 + (1)*v 88 + ((y^(2:ℕ))/(z*w))*v 140 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 110 + ((z)/(y^(2:ℕ)*w))*v 147 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0 ∧
      (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + ((w)/(y^(2:ℕ)*z))*v 120 + (((-1)*x*w*a)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 100 + (((-1)*z)/(y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0 ∧
      (1)*v 112 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 + ((w)/(y^(2:ℕ)*z))*v 165 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0 ∧
      (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 + ((z)/(w))*v 168 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0 ∧
      (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 + (((-1)*z*b)/(y*w))*v 168 = 0 ∧
      (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0 ∧
      (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + ((z)/(w))*v 168 = 0 ∧
      (1)*v 8 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + (1)*v 188 + ((-1)/(z))*v 200 = 0 ∧
      (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (1)*v 196 = 0 ∧
      (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0 ∧
      (1)*v 46 + ((-1)/(y^(2:ℕ)*z))*v 60 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 172 = 0 ∧
      (1)*v 38 + ((-1)/(y^(2:ℕ)*z))*v 60 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 164 = 0 ∧
      ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((z)/(w))*v 168 = 0 ∧
      ((w)/(x^(2:ℕ)*z))*v 60 + (1)*v 63 + (1)*v 147 + ((w)/(x^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 + (1)*v 200 = 0 ∧
      (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (1)*v 200 = 0 := by
  have h17309 : (1)*v 57 + (((-1)*a)/(x))*v 114 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3316-((1)/(x^(2:ℕ)))*h17248
  have h17311 : ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (((-1)*y*b)/(z*w))*v 140 + (1)*v 146 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15130-(((-1)*b)/(y))*h17248
  have h17312 : (((-1)*b)/(y))*v 54 + (1)*v 88 + ((y^(2:ℕ))/(z*w))*v 140 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3448-(1)*h17248
  have h17343 : (1)*v 20 + (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h36
  have h17359 : (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17060-(1)*h17343
  have h17361 : (1)*v 8 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + ((-1)/(z))*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17288-((-1)/(z))*h17343
  have h17376 : (1)*v 110 + ((z)/(y^(2:ℕ)*w))*v 147 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17077-((1)/(x^(2:ℕ)))*h17343
  have h17378 : (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3242-(1)*h17343
  have h17398 : (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h38
  have h17400 : (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h316-(((-1)*x^(2:ℕ))/(y^(2:ℕ)))*h17398
  have h17414 : (1)*v 46 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 172 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15436-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h17398
  have h17415 : (1)*v 38 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 164 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15437-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h17398
  have h17422 : (1)*v 63 + (1)*v 147 + ((w)/(x^(2:ℕ)*z))*v 150 + (1)*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3006-(1)*h17398
  have h17438 : ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16947-(((-1)*b)/(y))*h17398
  have h17473 : (1)*v 28 + (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h40
  have h17489 : (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15281-(1)*h17473
  have h17497 : (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (1)*v 182 + (1)*v 196 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17128-(1)*h17473
  have h17498 : (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17202-((-1)/(x^(2:ℕ)*w))*h17473
  have h17512 : ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 112 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 + ((w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17145-((1)/(x^(2:ℕ)))*h17473
  have h17513 : ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + ((w)/(y^(2:ℕ)*z))*v 120 + (((-1)*x*w*a)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17146-(((-1)*a)/(x))*h17473
  have h17537 : (1)*v 30 + (((-1)*z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h42
  have h17543 : (1)*v 100 + (((-1)*z)/(y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h320-((-1)/(y^(2:ℕ)))*h17537
  have h17606 : (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((z)/(w))*v 168 + (((-1)*x^(2:ℕ))/(w))*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15439-(1)*h17537
  have h17610 : (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + ((z)/(w))*v 168 + (1)*v 180 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2932-(1)*h17537
  have h17611 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14347-((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*h17537
  have h17633 : (1)*v 16 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1 + z)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17130-(1)*h17537
  have h17640 : (1)*v 8 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + ((-1)/(z))*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17361-((-1)/(z))*h17537
  have h17666 : (1)*v 112 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 + ((w)/(y^(2:ℕ)*z))*v 165 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17512-((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*h17537
  have h17667 : ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17218-(((-1)*a)/(x))*h17537
  have h17668 : (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3262-(1)*h17537
  have h17670 : ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17438-((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*h17537
  have h17671 : (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 + (((-1)*z*b)/(y*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17080-(((-1)*b)/(y))*h17537
  have h17778 : (1)*v 180 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*z)/(w))*h48
  have h17779 : (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h68-(1)*h17778
  have h17832 : (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17610-(1)*h17778
  have h17860 : (1)*v 8 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + (1)*v 188 + ((-1)/(z))*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17640-((-1)/(z))*h17778
  have h17885 : (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3292-((1)/(x^(2:ℕ)))*h17778
  have h18007 : (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 182 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*h50
  have h18019 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16074-(1)*h18007
  have h18027 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (1)*v 196 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17497-(1)*h18007
  have h18029 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17633-((-1)/(w))*h18007
  have h18073 : (((-1)*w)/(x^(2:ℕ)*z))*v 60 + (1)*v 189 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*w)/(x^(2:ℕ)*z))*h52
  have h18075 : (((-1)*w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h294-(((-1)*x^(2:ℕ))/(y^(2:ℕ)))*h18073
  have h18091 : (1)*v 46 + ((-1)/(y^(2:ℕ)*z))*v 60 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 172 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17414-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h18073
  have h18092 : (1)*v 38 + ((-1)/(y^(2:ℕ)*z))*v 60 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17415-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h18073
  have h18093 : ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17606-(((-1)*x^(2:ℕ))/(w))*h18073
  have h18099 : ((w)/(x^(2:ℕ)*z))*v 60 + (1)*v 63 + (1)*v 147 + ((w)/(x^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17422-(1)*h18073
  have h18167 : (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 190 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*h54
  have h18183 : (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 + (1)*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17359-(1)*h18167
  have h18201 : (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (1)*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3392-(((-1)*a)/(x))*h18167
  exact ⟨h17309, h17311, h17312, h17376, h17378, h17400, h17489, h17498, h17513, h17543, h17611, h17666, h17667, h17668, h17670, h17671, h17779, h17832, h17860, h17885, h18019, h18027, h18029, h18075, h18091, h18092, h18093, h18099, h18183, h18201⟩

#print axioms positive_last_pair_reduced_rows_chunk2

theorem positive_last_pair_reduced_rows_chunk3 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h56 : (1)*v 70 = 0)
    (h58 : (((-1)*x^(2:ℕ)*w)/(z))*v 195 = 0)
    (h60 : (1)*v 90 + (((-1)*y^(2:ℕ)*z)/(w))*v 196 = 0)
    (h64 : (1)*v 126 + (((-1)*y^(2:ℕ)*w)/(z))*v 200 = 0)
    (h66 : (1)*v 140 + (((-1)*x^(2:ℕ)*z*w)/(y^(2:ℕ)))*v 201 = 0)
    (h150 : ((-1)*y^(2:ℕ))*v 8 + (1)*v 186 = 0)
    (h162 : (1)*v 202 = 0)
    (h262 : (1)*v 107 + ((-1)/(x^(2:ℕ)))*v 202 = 0)
    (h268 : (1)*v 72 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 199 = 0)
    (h270 : (1)*v 90 + ((-1)*y^(2:ℕ))*v 200 = 0)
    (h272 : (1)*v 96 + ((-1)*x^(2:ℕ))*v 201 = 0)
    (h274 : (1)*v 99 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h300 : (1)*v 120 + ((-1)*x^(2:ℕ))*v 195 = 0)
    (h358 : (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203 = 0)
    (h364 : (1)*v 176 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 201 = 0)
    (h366 : (1)*v 177 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h2790 : (1)*v 70 + (1)*v 140 = 0)
    (h2868 : (1)*v 33 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 70 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 196 = 0)
    (h3218 : (1)*v 8 + (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0)
    (h3302 : (1)*v 50 + (((-1)*a)/(x))*v 100 + (1)*v 155 + ((1)/(x^(2:ℕ)))*v 200 = 0)
    (h3362 : (1)*v 80 + ((1)/(x^(2:ℕ)))*v 110 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0)
    (h3530 : (1)*v 59 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 + (1)*v 199 = 0)
    (h14320 : ((-1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0)
    (h15648 : ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0)
    (h15649 : (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0)
    (h16255 : (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 = 0)
    (h16711 : (1)*v 110 = 0)
    (h17201 : (1)*v 45 + (1)*v 75 + ((z)/(x^(2:ℕ)*w))*v 126 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0)
    (h17376 : (1)*v 110 + ((z)/(y^(2:ℕ)*w))*v 147 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h17489 : (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0)
    (h17498 : (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h17611 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0)
    (h17779 : (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0)
    (h17832 : (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + ((z)/(w))*v 168 = 0)
    (h17860 : (1)*v 8 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + (1)*v 188 + ((-1)/(z))*v 200 = 0)
    (h18027 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (1)*v 196 = 0)
    (h18183 : (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 + (1)*v 200 = 0)
    (h18201 : (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (1)*v 200 = 0)
    : (1)*v 140 = 0 ∧
      (1)*v 72 + (1)*v 142 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 120 = 0 ∧
      (1)*v 45 + (1)*v 75 + ((z)/(x^(2:ℕ)*w))*v 126 + (1)*v 135 + (1)*v 165 = 0 ∧
      (1)*v 50 + (((-1)*a)/(x))*v 100 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 155 = 0 ∧
      (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((z)/(y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)))*v 170 = 0 ∧
      (1)*v 96 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      ((-1)/(z*w))*v 140 + (1)*v 176 = 0 ∧
      (1)*v 168 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 + (((-1)*a)/(x*y^(2:ℕ)))*v 186 = 0 ∧
      (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 + ((1)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 99 = 0 ∧
      (1)*v 177 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 100 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 = 0 ∧
      ((z)/(y^(2:ℕ)*w))*v 147 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 80 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0 ∧
      (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 = 0 ∧
      (1)*v 90 + (((-1)*z)/(w))*v 126 = 0 ∧
      (1)*v 48 + ((-1 + z)/(w))*v 126 + (1)*v 132 = 0 ∧
      (1)*v 33 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 = 0 ∧
      (1)*v 60 + (1)*v 120 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0 ∧
      (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + ((1)/(y^(2:ℕ)))*v 126 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 29 + (1)*v 57 + (1)*v 99 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + (1)*v 197 = 0 ∧
      (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + (1)*v 98 + ((-1)/(z))*v 120 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
  have h18226 : (1)*v 70 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h56
  have h18270 : (1)*v 140 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2790-(1)*h18226
  have h18272 : (1)*v 72 + (1)*v 142 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14320-((-1)/(z*w))*h18226
  have h18275 : (1)*v 33 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 196 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2868-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h18226
  have h18276 : (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17489-(1)*h18226
  have h18289 : (1)*v 29 + (1)*v 57 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17498-((-1)/(x^(2:ℕ)*w))*h18226
  have h18389 : (1)*v 195 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*z)/(x^(2:ℕ)*w))*h58
  have h18393 : (1)*v 120 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h300-((-1)*x^(2:ℕ))*h18389
  have h18422 : (1)*v 45 + (1)*v 75 + ((z)/(x^(2:ℕ)*w))*v 126 + (1)*v 135 + (1)*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17201-(1)*h18389
  have h18511 : (((-1)*w)/(y^(2:ℕ)*z))*v 90 + (1)*v 196 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*w)/(y^(2:ℕ)*z))*h60
  have h18532 : (1)*v 33 + (1)*v 75 + ((-1)/(x^(2:ℕ)*z))*v 90 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18275-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h18511
  have h18538 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + ((w)/(y^(2:ℕ)*z))*v 90 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18027-(1)*h18511
  have h18539 : (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 99 + (1)*v 113 + ((-1 + z)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18289-((-1)/(x^(2:ℕ)*w))*h18511
  have h18596 : (((-1)*z)/(y^(2:ℕ)*w))*v 126 + (1)*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*z)/(y^(2:ℕ)*w))*h64
  have h18600 : (1)*v 90 + (((-1)*z)/(w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h270-((-1)*y^(2:ℕ))*h18596
  have h18630 : (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 100 + (1)*v 110 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18183-(1)*h18596
  have h18632 : (1)*v 8 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17860-((-1)/(z))*h18596
  have h18647 : (1)*v 50 + (((-1)*a)/(x))*v 100 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 155 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3302-((1)/(x^(2:ℕ)))*h18596
  have h18648 : (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((z)/(y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)))*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18201-(1)*h18596
  have h18719 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 201 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*y^(2:ℕ))/(x^(2:ℕ)*z*w))*h66
  have h18723 : (1)*v 96 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h272-((-1)*x^(2:ℕ))*h18719
  have h18724 : ((-1)/(z*w))*v 140 + (1)*v 176 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h364-(((-1)*x^(2:ℕ))/(y^(2:ℕ)))*h18719
  have h18836 : (1)*v 203 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*h17779
  have h18840 : (1)*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h358-((-1)*x^(2:ℕ)*y^(2:ℕ))*h18836
  have h18889 : (1)*v 8 + ((-1)/(y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(y^(2:ℕ)))*h150
  have h18911 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18632-(1)*h18889
  have h18924 : (1)*v 107 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15648-((1)/(x^(2:ℕ)))*h18889
  have h18925 : ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 + (((-1)*a)/(x*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15649-(((-1)*a)/(x))*h18889
  have h18926 : (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 + ((1)/(y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3218-(1)*h18889
  have h18980 : (1)*v 202 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h162
  have h18982 : (1)*v 107 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h262-((-1)/(x^(2:ℕ)))*h18980
  have h18983 : (1)*v 99 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h274-(((-1)*y^(2:ℕ))/(x^(2:ℕ)))*h18980
  have h18984 : (1)*v 177 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h366-(((-1)*y^(2:ℕ))/(x^(2:ℕ)))*h18980
  have h19041 : (1)*v 107 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18982
  have h19066 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18924-(1)*h19041
  have h19080 : (1)*v 110 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16711
  have h19116 : (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 100 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18630-(1)*h19080
  have h19118 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + ((-1)/(z))*v 120 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18911-((-1)/(z))*h19080
  have h19133 : ((z)/(y^(2:ℕ)*w))*v 147 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17376-(1)*h19080
  have h19135 : (1)*v 80 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3362-((1)/(x^(2:ℕ)))*h19080
  have h19163 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 199 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*h268
  have h19179 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3530-(1)*h19163
  have h19189 : (1)*v 90 + (((-1)*z)/(w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18600
  have h19224 : (1)*v 48 + ((-1 + z)/(w))*v 126 + (1)*v 132 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16255-(1)*h19189
  have h19226 : (1)*v 33 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18532-((-1)/(x^(2:ℕ)*z))*h19189
  have h19230 : (1)*v 60 + (1)*v 120 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17832-(1)*h19189
  have h19232 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17611-((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*h19189
  have h19253 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + ((1)/(y^(2:ℕ)))*v 126 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18538-((w)/(y^(2:ℕ)*z))*h19189
  have h19254 : (1)*v 29 + (1)*v 57 + (1)*v 99 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18539-((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*h19189
  have h19260 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + (1)*v 98 + ((-1)/(z))*v 120 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19118-((-1)/(z))*h19189
  exact ⟨h18270, h18272, h18276, h18393, h18422, h18647, h18648, h18723, h18724, h18840, h18925, h18926, h18983, h18984, h19066, h19116, h19133, h19135, h19179, h19189, h19224, h19226, h19230, h19232, h19253, h19254, h19260⟩

#print axioms positive_last_pair_reduced_rows_chunk3

theorem positive_last_pair_reduced_rows_chunk4 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h288 : (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0)
    (h292 : (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0)
    (h296 : (1)*v 114 = 0)
    (h298 : (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h304 : (1)*v 144 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 197 = 0)
    (h312 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0)
    (h2806 : (1)*v 65 + (((-1)*z)/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*z)/(x^(2:ℕ)*w))*v 168 = 0)
    (h2808 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + (((-1)*w)/(x^(2:ℕ)*z))*v 120 + (1)*v 147 = 0)
    (h3250 : (((-1)*a)/(x))*v 48 + ((1)/(x^(2:ℕ)))*v 96 + (1)*v 129 = 0)
    (h3364 : (1)*v 81 + ((1)/(x^(2:ℕ)))*v 114 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0)
    (h3386 : (1)*v 92 + ((1)/(x^(2:ℕ)))*v 158 + (((-1)*a)/(x))*v 184 + (1)*v 197 = 0)
    (h3434 : (1)*v 11 + (((-1)*b)/(y))*v 33 + (1)*v 81 + ((1)/(y^(2:ℕ)))*v 99 + (1)*v 151 = 0)
    (h3478 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (((-1)*b)/(y))*v 99 + (1)*v 103 + (1)*v 173 = 0)
    (h15740 : ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0)
    (h16404 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0)
    (h16630 : (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0)
    (h17122 : (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + ((-1)/(x^(2:ℕ)*z))*v 120 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0)
    (h17309 : (1)*v 57 + (((-1)*a)/(x))*v 114 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 162 = 0)
    (h17400 : (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0)
    (h17513 : ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + ((w)/(y^(2:ℕ)*z))*v 120 + (((-1)*x*w*a)/(y^(2:ℕ)*z))*v 165 = 0)
    (h17666 : (1)*v 112 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 + ((w)/(y^(2:ℕ)*z))*v 165 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0)
    (h17667 : ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0)
    (h17668 : (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 + ((z)/(w))*v 168 = 0)
    (h17671 : (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 + (((-1)*z*b)/(y*w))*v 168 = 0)
    (h17885 : (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 = 0)
    (h18019 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 = 0)
    (h18029 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0)
    (h18075 : (((-1)*w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0)
    (h18093 : ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((z)/(w))*v 168 = 0)
    (h18276 : (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0)
    (h18393 : (1)*v 120 = 0)
    (h18723 : (1)*v 96 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0)
    (h18925 : ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 + (((-1)*a)/(x*y^(2:ℕ)))*v 186 = 0)
    (h18983 : (1)*v 99 = 0)
    (h19179 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 = 0)
    (h19189 : (1)*v 90 + (((-1)*z)/(w))*v 126 = 0)
    (h19226 : (1)*v 33 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 = 0)
    (h19230 : (1)*v 60 + (1)*v 120 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0)
    (h19232 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0)
    (h19253 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 98 + (1)*v 112 + ((w)/(y^(2:ℕ)*z))*v 120 + ((1)/(y^(2:ℕ)))*v 126 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h19254 : (1)*v 29 + (1)*v 57 + (1)*v 99 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + (1)*v 197 = 0)
    (h19260 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + (1)*v 98 + ((-1)/(z))*v 120 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0)
    : (1)*v 45 + (((-1)*z*a)/(x*w))*v 126 + (1)*v 150 = 0 ∧
      (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 150 + (((-1)*z*b)/(y*w))*v 168 = 0 ∧
      (((-1)*a)/(x))*v 48 + (1)*v 129 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 = 0 ∧
      (1)*v 11 + (((-1)*b)/(y))*v 33 + (1)*v 81 + (1)*v 151 = 0 ∧
      (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (1)*v 103 + (1)*v 173 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 16 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 + (((-1)*a)/(x*y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 + (((-1)*b)/(y))*v 177 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 60 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 ∧
      ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((z)/(w))*v 168 = 0 ∧
      (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 ∧
      (1)*v 57 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 162 = 0 ∧
      (1)*v 81 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0 ∧
      (1)*v 33 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 48 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + (1)*v 147 = 0 ∧
      (1)*v 78 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0 ∧
      (1)*v 60 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0 ∧
      (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0 ∧
      (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + (1)*v 98 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 ∧
      ((w)/(y^(2:ℕ)*z))*v 60 + ((w)/(y^(2:ℕ)*z))*v 165 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + (((-1)*x*w*a)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 60 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0 ∧
      (((-1)*a)/(x))*v 60 + (1)*v 135 + ((z)/(w))*v 168 = 0 ∧
      (1)*v 29 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 = 0 ∧
      (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((1)/(x^(2:ℕ)))*v 158 + (((-1)*a)/(x))*v 184 = 0 ∧
      (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 65 + (1)*v 135 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 + (((-1)*z)/(x^(2:ℕ)*w))*v 168 = 0 ∧
      ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + ((-1)/(x^(2:ℕ)*z))*v 150 + (1)*v 177 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 140 + ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + ((w)/(y^(2:ℕ)*z))*v 60 + ((1)/(y^(2:ℕ)))*v 126 + ((w)/(y^(2:ℕ)*z))*v 150 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + (1)*v 100 + ((-1)/(w))*v 140 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0 := by
  have h19300 : (1)*v 45 + (((-1)*z*a)/(x*w))*v 126 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17885-(((-1)*a)/(x))*h19189
  have h19306 : (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 150 + (((-1)*z*b)/(y*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17671-((1)/(y^(2:ℕ)))*h19189
  have h19395 : (1)*v 96 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18723
  have h19449 : (((-1)*a)/(x))*v 48 + (1)*v 129 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3250-((1)/(x^(2:ℕ)))*h19395
  have h19483 : (1)*v 99 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18983
  have h19502 : (1)*v 29 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19254-(1)*h19483
  have h19514 : (1)*v 11 + (((-1)*b)/(y))*v 33 + (1)*v 81 + (1)*v 151 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3434-((1)/(y^(2:ℕ)))*h19483
  have h19516 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (1)*v 103 + (1)*v 173 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3478-(((-1)*b)/(y))*h19483
  have h19532 : (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h288
  have h19551 : ((1)/(x^(2:ℕ)))*v 16 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 + (((-1)*a)/(x*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18925-(1)*h19532
  have h19563 : (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h292
  have h19601 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 + (((-1)*b)/(y))*v 177 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19179-((1)/(y^(2:ℕ)))*h19563
  have h19620 : (((-1)*w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18075
  have h19638 : (1)*v 33 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + (1)*v 117 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19226-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h19620
  have h19639 : ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 60 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18276-(1)*h19620
  have h19642 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + ((w)/(y^(2:ℕ)*z))*v 60 + (1)*v 98 + ((w)/(y^(2:ℕ)*z))*v 120 + ((1)/(y^(2:ℕ)))*v 126 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19253-(1)*h19620
  have h19659 : ((w)/(y^(2:ℕ)*z))*v 60 + (((-1)*w*a)/(x*y^(2:ℕ)*z))*v 120 + ((w)/(y^(2:ℕ)*z))*v 165 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17666-(1)*h19620
  have h19689 : (1)*v 114 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h296
  have h19717 : ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18093-(1)*h19689
  have h19719 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16404-(((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*h19689
  have h19723 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + ((-1)/(y^(2:ℕ)*z))*v 120 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18029-(1)*h19689
  have h19749 : (1)*v 57 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17309-(((-1)*a)/(x))*h19689
  have h19750 : (1)*v 81 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3364-((1)/(x^(2:ℕ)))*h19689
  have h19784 : (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h298
  have h19792 : (1)*v 33 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19638-(1)*h19784
  have h19805 : ((1)/(x^(2:ℕ)))*v 48 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15740-(1)*h19784
  have h19820 : (1)*v 120 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18393
  have h19849 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + (1)*v 147 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2808-(((-1)*w)/(x^(2:ℕ)*z))*h19820
  have h19851 : (1)*v 78 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h16630-(1)*h19820
  have h19853 : (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17122-((-1)/(x^(2:ℕ)*z))*h19820
  have h19857 : (1)*v 60 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19230-(1)*h19820
  have h19859 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19232-((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*h19820
  have h19880 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + ((w)/(y^(2:ℕ)*z))*v 60 + (1)*v 98 + ((1)/(y^(2:ℕ)))*v 126 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19642-((w)/(y^(2:ℕ)*z))*h19820
  have h19882 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19723-((-1)/(y^(2:ℕ)*z))*h19820
  have h19887 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + (1)*v 98 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19260-((-1)/(z))*h19820
  have h19927 : ((w)/(y^(2:ℕ)*z))*v 60 + ((w)/(y^(2:ℕ)*z))*v 165 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19659-(((-1)*w*a)/(x*y^(2:ℕ)*z))*h19820
  have h19928 : ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + (((-1)*x*w*a)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17513-((w)/(y^(2:ℕ)*z))*h19820
  have h19929 : ((1)/(x^(2:ℕ)))*v 60 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17667-(1)*h19820
  have h19930 : (((-1)*a)/(x))*v 60 + (1)*v 135 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17668-((1)/(x^(2:ℕ)))*h19820
  have h20020 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 197 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*h304
  have h20028 : (1)*v 29 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19502-(1)*h20020
  have h20033 : (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((1)/(x^(2:ℕ)))*v 158 + (((-1)*a)/(x))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3386-(1)*h20020
  have h20062 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h312
  have h20068 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19853-(1)*h20062
  have h20096 : (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h17400
  have h20110 : (1)*v 65 + (1)*v 135 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 + (((-1)*z)/(x^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2806-(((-1)*z)/(x^(2:ℕ)*w))*h20096
  have h20112 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + ((-1)/(x^(2:ℕ)*z))*v 150 + (1)*v 177 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20068-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h20096
  have h20113 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 140 + ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18019-(1)*h20096
  have h20116 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + ((w)/(y^(2:ℕ)*z))*v 60 + ((1)/(y^(2:ℕ)))*v 126 + ((w)/(y^(2:ℕ)*z))*v 150 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19880-(1)*h20096
  have h20117 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + (1)*v 100 + ((-1)/(w))*v 140 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19882-((-1)/(w))*h20096
  exact ⟨h19300, h19306, h19449, h19514, h19516, h19551, h19601, h19639, h19717, h19719, h19749, h19750, h19792, h19805, h19849, h19851, h19857, h19859, h19887, h19927, h19928, h19929, h19930, h20028, h20033, h20096, h20110, h20112, h20113, h20116, h20117⟩

#print axioms positive_last_pair_reduced_rows_chunk4

theorem positive_last_pair_reduced_rows_chunk5 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h326 : (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h342 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 11 + (1)*v 138 = 0)
    (h368 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 37 + (1)*v 138 = 0)
    (h370 : ((-1)*y^(2:ℕ))*v 38 + (1)*v 156 = 0)
    (h374 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 40 + (1)*v 165 = 0)
    (h378 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0)
    (h2840 : (1)*v 126 + (1)*v 168 = 0)
    (h3276 : (1)*v 37 + (((-1)*a)/(x))*v 74 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h3290 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 + ((1)/(x^(2:ℕ)))*v 176 = 0)
    (h3326 : ((1)/(x^(2:ℕ)))*v 38 + (1)*v 62 + (((-1)*a)/(x))*v 124 + (1)*v 167 = 0)
    (h14327 : (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h14328 : (1)*v 44 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + ((-1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0)
    (h14329 : (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((-1)/(y^(2:ℕ)*w))*v 168 = 0)
    (h14330 : (1)*v 45 + (1)*v 87 + (1)*v 129 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0)
    (h17378 : (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0)
    (h17543 : (1)*v 100 + (((-1)*z)/(y^(2:ℕ)*w))*v 168 = 0)
    (h17670 : ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0)
    (h18092 : (1)*v 38 + ((-1)/(y^(2:ℕ)*z))*v 60 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 164 = 0)
    (h18647 : (1)*v 50 + (((-1)*a)/(x))*v 100 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 155 = 0)
    (h18724 : ((-1)/(z*w))*v 140 + (1)*v 176 = 0)
    (h18840 : (1)*v 168 = 0)
    (h18984 : (1)*v 177 = 0)
    (h19116 : (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 100 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 = 0)
    (h19133 : ((z)/(y^(2:ℕ)*w))*v 147 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h19306 : (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 150 + (((-1)*z*b)/(y*w))*v 168 = 0)
    (h19514 : (1)*v 11 + (((-1)*b)/(y))*v 33 + (1)*v 81 + (1)*v 151 = 0)
    (h19516 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (1)*v 103 + (1)*v 173 = 0)
    (h19601 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 + (((-1)*b)/(y))*v 177 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h19717 : ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((z)/(w))*v 168 = 0)
    (h19851 : (1)*v 78 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0)
    (h19857 : (1)*v 60 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0)
    (h19859 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 + (1)*v 179 = 0)
    (h19887 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + (1)*v 98 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0)
    (h19927 : ((w)/(y^(2:ℕ)*z))*v 60 + ((w)/(y^(2:ℕ)*z))*v 165 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 = 0)
    (h19929 : ((1)/(x^(2:ℕ)))*v 60 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0)
    (h19930 : (((-1)*a)/(x))*v 60 + (1)*v 135 + ((z)/(w))*v 168 = 0)
    (h20028 : (1)*v 29 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 = 0)
    (h20096 : (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0)
    (h20110 : (1)*v 65 + (1)*v 135 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 + (((-1)*z)/(x^(2:ℕ)*w))*v 168 = 0)
    (h20112 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + ((-1)/(x^(2:ℕ)*z))*v 150 + (1)*v 177 = 0)
    (h20117 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + (1)*v 100 + ((-1)/(w))*v 140 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + ((-1 + z)/(w))*v 168 + (1)*v 184 = 0)
    : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (1)*v 173 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      (((-1)*b)/(y))*v 33 + (1)*v 81 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 151 = 0 ∧
      (1)*v 65 + (1)*v 135 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 = 0 ∧
      (1)*v 126 = 0 ∧
      (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 = 0 ∧
      (1)*v 45 + (1)*v 87 + (1)*v 129 + (1)*v 171 = 0 ∧
      (1)*v 78 + ((-1)/(w))*v 126 + (1)*v 162 = 0 ∧
      ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 = 0 ∧
      (1)*v 60 + ((z)/(w))*v 126 + (1)*v 150 = 0 ∧
      (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0 ∧
      (1)*v 29 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + (1)*v 183 = 0 ∧
      (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 140 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0 ∧
      ((z)/(y^(2:ℕ)*w))*v 147 = 0 ∧
      ((w)/(y^(2:ℕ)*z))*v 60 + ((w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 60 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 ∧
      (((-1)*a)/(x))*v 60 + (1)*v 135 = 0 ∧
      (1)*v 50 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 155 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0 ∧
      (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 150 = 0 ∧
      (1)*v 44 + (((-1)*a)/(x))*v 88 + ((1)/(x^(2:ℕ)*z*w))*v 140 + (1)*v 149 = 0 ∧
      ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + ((-1)/(x^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      (((-1)*a)/(x))*v 74 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0 ∧
      ((-1)/(y^(2:ℕ)*z))*v 60 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((-1)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0 ∧
      (1)*v 82 + (1)*v 124 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 + (1)*v 166 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (((-1)*x*a)/(y^(2:ℕ)))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0 ∧
      (1)*v 44 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 = 0 ∧
      ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
  have h20119 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + (1)*v 158 + ((-1 + w)/(w))*v 168 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19887-(1)*h20096
  have h20159 : (1)*v 100 + (((-1)*z)/(y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h17543
  have h20180 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 140 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + ((z + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 168 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20117-(1)*h20159
  have h20182 : (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + ((z)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19116-(1)*h20159
  have h20200 : (1)*v 50 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 155 + (((-1)*z*a)/(x*y^(2:ℕ)*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18647-(((-1)*a)/(x))*h20159
  have h20246 : (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h326
  have h20262 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (1)*v 173 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19516-(1)*h20246
  have h20271 : (1)*v 11 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*h342
  have h20283 : (((-1)*b)/(y))*v 33 + (1)*v 81 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 151 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19514-(1)*h20271
  have h20291 : (1)*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18840
  have h20347 : (1)*v 65 + (1)*v 135 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20110-(((-1)*z)/(x^(2:ℕ)*w))*h20291
  have h20349 : (1)*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2840-(1)*h20291
  have h20350 : (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14327-((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*h20291
  have h20351 : (1)*v 44 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14328-((-1)/(y^(2:ℕ)*w))*h20291
  have h20352 : (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14329-((-1)/(y^(2:ℕ)*w))*h20291
  have h20353 : (1)*v 45 + (1)*v 87 + (1)*v 129 + (1)*v 171 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14330-((-1)/(x^(2:ℕ)*w))*h20291
  have h20355 : (1)*v 78 + ((-1)/(w))*v 126 + (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19851-((-1)/(w))*h20291
  have h20356 : ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19717-((z)/(w))*h20291
  have h20368 : (1)*v 60 + ((z)/(w))*v 126 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19857-((z)/(w))*h20291
  have h20369 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19859-((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*h20291
  have h20405 : (1)*v 29 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + (1)*v 183 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20028-((-1)/(x^(2:ℕ)*w))*h20291
  have h20406 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 140 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20180-((z + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(y^(2:ℕ)*w))*h20291
  have h20413 : (1)*v 40 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20182-((z)/(y^(2:ℕ)*w))*h20291
  have h20417 : (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + (1)*v 158 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20119-((-1 + w)/(w))*h20291
  have h20454 : ((z)/(y^(2:ℕ)*w))*v 147 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19133-((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*h20291
  have h20455 : ((w)/(y^(2:ℕ)*z))*v 60 + ((w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19927-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h20291
  have h20456 : ((1)/(x^(2:ℕ)))*v 60 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19929-(((-1)*z*a)/(x*w))*h20291
  have h20458 : (((-1)*a)/(x))*v 60 + (1)*v 135 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19930-((z)/(w))*h20291
  have h20460 : (1)*v 50 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 155 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20200-(((-1)*z*a)/(x*y^(2:ℕ)*w))*h20291
  have h20466 : ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17670-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h20291
  have h20467 : (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19306-(((-1)*z*b)/(y*w))*h20291
  have h20624 : ((-1)/(z*w))*v 140 + (1)*v 176 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18724
  have h20650 : (1)*v 44 + (((-1)*a)/(x))*v 88 + ((1)/(x^(2:ℕ)*z*w))*v 140 + (1)*v 149 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3290-((1)/(x^(2:ℕ)))*h20624
  have h20670 : (1)*v 177 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18984
  have h20685 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + ((-1)/(x^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20112-(1)*h20670
  have h20701 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19601-(((-1)*b)/(y))*h20670
  have h20727 : (1)*v 37 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*h368
  have h20740 : (((-1)*a)/(x))*v 74 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3276-(1)*h20727
  have h20754 : (1)*v 38 + ((-1)/(y^(2:ℕ)))*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(y^(2:ℕ)))*h370
  have h20762 : ((-1)/(y^(2:ℕ)*z))*v 60 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((-1)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18092-(1)*h20754
  have h20764 : (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + ((-1)/(z))*v 170 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20417-(1)*h20754
  have h20777 : (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3326-((1)/(x^(2:ℕ)))*h20754
  have h20842 : (1)*v 40 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*h374
  have h20856 : (1)*v 82 + (1)*v 124 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 + (1)*v 166 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20352-(1)*h20842
  have h20866 : (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20413-(1)*h20842
  have h20882 : ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (((-1)*x*a)/(y^(2:ℕ)))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17378-(((-1)*a)/(x))*h20842
  have h20920 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h378
  have h20930 : (1)*v 44 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20351-(1)*h20920
  have h20940 : ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20866-(1)*h20920
  have h20942 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20764-((-1)/(z))*h20920
  exact ⟨h20262, h20283, h20347, h20349, h20350, h20353, h20355, h20356, h20368, h20369, h20405, h20406, h20454, h20455, h20456, h20458, h20460, h20466, h20467, h20650, h20685, h20701, h20740, h20762, h20777, h20856, h20882, h20920, h20930, h20940, h20942⟩

#print axioms positive_last_pair_reduced_rows_chunk5

theorem positive_last_pair_reduced_rows_chunk6 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h380 : ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0)
    (h382 : ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0)
    (h384 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0)
    (h394 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0)
    (h398 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0)
    (h400 : ((-1)*x^(2:ℕ))*v 33 + (1)*v 186 = 0)
    (h3284 : (1)*v 41 + (((-1)*a)/(x))*v 82 + (1)*v 146 + ((1)/(x^(2:ℕ)))*v 164 = 0)
    (h3338 : ((1)/(x^(2:ℕ)))*v 62 + (1)*v 68 + (((-1)*a)/(x))*v 136 + (1)*v 173 = 0)
    (h3350 : (1)*v 74 + ((1)/(x^(2:ℕ)))*v 86 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0)
    (h3380 : (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (((-1)*a)/(x))*v 178 + (1)*v 194 = 0)
    (h14321 : (1)*v 68 + (1)*v 138 + ((-1)/(z*w))*v 140 = 0)
    (h15308 : (1)*v 51 + (1)*v 156 = 0)
    (h15309 : (1)*v 78 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0)
    (h16103 : (1)*v 54 + (1)*v 159 = 0)
    (h16399 : (1)*v 74 + (1)*v 144 = 0)
    (h16495 : (1)*v 66 + (1)*v 136 = 0)
    (h16661 : (1)*v 82 + (1)*v 152 = 0)
    (h17311 : ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (((-1)*y*b)/(z*w))*v 140 + (1)*v 146 = 0)
    (h17312 : (((-1)*b)/(y))*v 54 + (1)*v 88 + ((y^(2:ℕ))/(z*w))*v 140 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h18091 : (1)*v 46 + ((-1)/(y^(2:ℕ)*z))*v 60 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 172 = 0)
    (h18270 : (1)*v 140 = 0)
    (h18648 : (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((z)/(y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)))*v 170 = 0)
    (h18926 : (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 + ((1)/(y^(2:ℕ)))*v 186 = 0)
    (h19066 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h19449 : (((-1)*a)/(x))*v 48 + (1)*v 129 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 = 0)
    (h19551 : ((1)/(x^(2:ℕ)))*v 16 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 + (((-1)*a)/(x*y^(2:ℕ)))*v 186 = 0)
    (h19639 : ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 60 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0)
    (h19749 : (1)*v 57 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 162 = 0)
    (h19750 : (1)*v 81 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0)
    (h19792 : (1)*v 33 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h20113 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 140 + ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 150 = 0)
    (h20262 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (1)*v 173 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h20283 : (((-1)*b)/(y))*v 33 + (1)*v 81 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 151 = 0)
    (h20353 : (1)*v 45 + (1)*v 87 + (1)*v 129 + (1)*v 171 = 0)
    (h20405 : (1)*v 29 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 + (1)*v 183 = 0)
    (h20406 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(w))*v 140 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0)
    (h20650 : (1)*v 44 + (((-1)*a)/(x))*v 88 + ((1)/(x^(2:ℕ)*z*w))*v 140 + (1)*v 149 = 0)
    (h20685 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + ((-1)/(x^(2:ℕ)*z))*v 150 = 0)
    (h20701 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h20740 : (((-1)*a)/(x))*v 74 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h20856 : (1)*v 82 + (1)*v 124 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 + (1)*v 166 = 0)
    (h20920 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0)
    (h20942 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*w + y^(2:ℕ))/(z*w))*v 140 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0)
    : ((1)/(y^(2:ℕ)))*v 45 + (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((z)/(y^(2:ℕ)*w))*v 126 = 0 ∧
      (1)*v 45 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 87 + (1)*v 129 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + ((-1)/(y^(2:ℕ)*z))*v 60 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + ((-1)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (((-1)*x*a)/(y^(2:ℕ)))*v 27 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (1)*v 194 = 0 ∧
      (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 78 + (((-1)*a)/(x))*v 156 = 0 ∧
      (1)*v 68 + (1)*v 138 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0 ∧
      (((-1)*a)/(x))*v 48 + (1)*v 129 = 0 ∧
      (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0 ∧
      (1)*v 57 + (1)*v 162 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 ∧
      (((-1)*b)/(y))*v 54 + (1)*v 88 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 142 + ((a)/(x))*v 144 + ((1)/(x^(2:ℕ)))*v 148 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + (1)*v 68 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 ∧
      ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 60 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 16 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0 ∧
      (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0 ∧
      (1)*v 81 + (((-1)*a)/(x))*v 162 = 0 ∧
      (1)*v 81 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 151 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 87 = 0 ∧
      (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 = 0 ∧
      ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + ((-1)/(x^(2:ℕ)*z))*v 150 + (-1)*v 156 = 0 ∧
      (-1)*v 54 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      (1)*v 124 + (-1)*v 152 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 + (1)*v 166 = 0 ∧
      (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0 := by
  have h20957 : ((1)/(y^(2:ℕ)))*v 45 + (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((z)/(y^(2:ℕ)*w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18648-((1)/(x^(2:ℕ)))*h20920
  have h20980 : ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h380
  have h20989 : (1)*v 45 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 87 + (1)*v 129 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20353-(1)*h20980
  have h21020 : ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h382
  have h21028 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + ((-1)/(y^(2:ℕ)*z))*v 60 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + ((-1)/(y^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18091-(1)*h21020
  have h21058 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h384
  have h21073 : ((1)/(x^(2:ℕ)))*v 62 + (1)*v 68 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (((-1)*a)/(x))*v 136 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3338-(1)*h21058
  have h21074 : (1)*v 33 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 87 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20262-(1)*h21058
  have h21085 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h394
  have h21107 : (((-1)*x*a)/(y^(2:ℕ)))*v 27 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (1)*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3380-(((-1)*a)/(x))*h21085
  have h21123 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h398
  have h21133 : (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20405-(1)*h21123
  have h21144 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 78 + (((-1)*a)/(x))*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h15309-(1)*h21123
  have h21161 : (1)*v 33 + ((-1)/(x^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)/(x^(2:ℕ)))*h400
  have h21183 : ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + ((1)/(x^(2:ℕ)))*v 186 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19792-(1)*h21161
  have h21197 : (1)*v 81 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 151 + (((-1)*b)/(x^(2:ℕ)*y))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20283-(((-1)*b)/(y))*h21161
  have h21199 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 87 + ((1 + y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21074-(1)*h21161
  have h21293 : (1)*v 140 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18270
  have h21295 : (1)*v 68 + (1)*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h14321-((-1)/(z*w))*h21293
  have h21298 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + ((-1)/(x^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20685-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h21293
  have h21300 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20113-(1)*h21293
  have h21325 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20406-((-1)/(w))*h21293
  have h21333 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 186 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20942-(((-1)*w + y^(2:ℕ))/(z*w))*h21293
  have h21371 : (((-1)*a)/(x))*v 48 + (1)*v 129 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19449-((y^(2:ℕ))/(x^(2:ℕ)*z*w))*h21293
  have h21373 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20650-((1)/(x^(2:ℕ)*z*w))*h21293
  have h21375 : (1)*v 57 + (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19749-((y^(2:ℕ))/(x^(2:ℕ)*z*w))*h21293
  have h21382 : ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17311-(((-1)*y*b)/(z*w))*h21293
  have h21383 : (((-1)*b)/(y))*v 54 + (1)*v 88 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17312-((y^(2:ℕ))/(z*w))*h21293
  have h21504 : (1)*v 74 + (1)*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16399
  have h21517 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 142 + ((a)/(x))*v 144 + ((1)/(x^(2:ℕ)))*v 148 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20740-(((-1)*a)/(x))*h21504
  have h21519 : ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3350-(1)*h21504
  have h21529 : (1)*v 66 + (1)*v 136 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16495
  have h21544 : ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + (1)*v 68 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21073-(((-1)*a)/(x))*h21529
  have h21554 : (1)*v 186 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (x^(2:ℕ)*y^(2:ℕ))*h19066
  have h21555 : ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21183-((1)/(x^(2:ℕ)))*h21554
  have h21556 : ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 60 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19639-(((-1)*w)/(y^(2:ℕ)))*h21554
  have h21576 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21333-((1)/(y^(2:ℕ)))*h21554
  have h21603 : ((1)/(x^(2:ℕ)))*v 16 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19551-(((-1)*a)/(x*y^(2:ℕ)))*h21554
  have h21605 : (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18926-((1)/(y^(2:ℕ)))*h21554
  have h21607 : (1)*v 81 + (((-1)*a)/(x))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19750-(1)*h21554
  have h21612 : (1)*v 81 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 151 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21197-(((-1)*b)/(x^(2:ℕ)*y))*h21554
  have h21614 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 87 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21199-((1 + y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*h21554
  have h21619 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20701-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h21554
  have h21708 : (1)*v 51 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h15308
  have h21709 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + ((-1)/(x^(2:ℕ)*z))*v 150 + (-1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21298-(1)*h21708
  have h21755 : (1)*v 54 + (1)*v 159 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16103
  have h21756 : (-1)*v 54 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21555-(1)*h21755
  have h21780 : (1)*v 82 + (1)*v 152 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16661
  have h21781 : (1)*v 124 + (-1)*v 152 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 + (1)*v 166 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20856-(1)*h21780
  have h21794 : (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3284-(((-1)*a)/(x))*h21780
  exact ⟨h20957, h20989, h21028, h21107, h21133, h21144, h21295, h21300, h21325, h21371, h21373, h21375, h21382, h21383, h21517, h21519, h21544, h21556, h21576, h21603, h21605, h21607, h21612, h21614, h21619, h21709, h21756, h21781, h21794⟩

#print axioms positive_last_pair_reduced_rows_chunk6

theorem positive_last_pair_reduced_rows_chunk7 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h2812 : (((-1)*z)/(w))*v 56 + (1)*v 80 + (((-1)*z)/(w))*v 126 + (1)*v 150 = 0)
    (h2814 : (1)*v 60 + (1)*v 130 + (((-1)*z)/(w))*v 154 = 0)
    (h16286 : (1)*v 58 + (1)*v 128 = 0)
    (h18099 : ((w)/(x^(2:ℕ)*z))*v 60 + (1)*v 63 + (1)*v 147 + ((w)/(x^(2:ℕ)*z))*v 150 = 0)
    (h18272 : (1)*v 72 + (1)*v 142 = 0)
    (h18422 : (1)*v 45 + (1)*v 75 + ((z)/(x^(2:ℕ)*w))*v 126 + (1)*v 135 + (1)*v 165 = 0)
    (h19224 : (1)*v 48 + ((-1 + z)/(w))*v 126 + (1)*v 132 = 0)
    (h19300 : (1)*v 45 + (((-1)*z*a)/(x*w))*v 126 + (1)*v 150 = 0)
    (h19849 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + (1)*v 147 = 0)
    (h20116 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + ((w)/(y^(2:ℕ)*z))*v 60 + ((1)/(y^(2:ℕ)))*v 126 + ((w)/(y^(2:ℕ)*z))*v 150 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h20349 : (1)*v 126 = 0)
    (h20350 : (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 = 0)
    (h20355 : (1)*v 78 + ((-1)/(w))*v 126 + (1)*v 162 = 0)
    (h20356 : ((-1)/(z))*v 60 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 = 0)
    (h20368 : (1)*v 60 + ((z)/(w))*v 126 + (1)*v 150 = 0)
    (h20369 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0)
    (h20454 : ((z)/(y^(2:ℕ)*w))*v 147 = 0)
    (h20455 : ((w)/(y^(2:ℕ)*z))*v 60 + ((w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h20456 : ((1)/(x^(2:ℕ)))*v 60 + ((z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h20458 : (((-1)*a)/(x))*v 60 + (1)*v 135 = 0)
    (h20460 : (1)*v 50 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 155 = 0)
    (h20466 : ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0)
    (h20467 : (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 150 = 0)
    (h20762 : ((-1)/(y^(2:ℕ)*z))*v 60 + (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((-1)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0)
    (h20882 : ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (((-1)*x*a)/(y^(2:ℕ)))*v 165 = 0)
    (h20930 : (1)*v 44 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 = 0)
    (h20940 : ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0)
    (h20957 : ((1)/(y^(2:ℕ)))*v 45 + (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 + ((z)/(y^(2:ℕ)*w))*v 126 = 0)
    (h21028 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + ((-1)/(y^(2:ℕ)*z))*v 60 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 + ((-1)/(y^(2:ℕ)*z))*v 150 = 0)
    (h21133 : (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 = 0)
    (h21295 : (1)*v 68 + (1)*v 138 = 0)
    (h21325 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 58 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0)
    (h21517 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 142 + ((a)/(x))*v 144 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h21544 : ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + (1)*v 68 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0)
    (h21556 : ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 60 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h21576 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0)
    (h21603 : ((1)/(x^(2:ℕ)))*v 16 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0)
    (h21709 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + ((-1)/(x^(2:ℕ)*z))*v 150 + (-1)*v 156 = 0)
    (h21756 : (-1)*v 54 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + ((-1)/(x^(2:ℕ)*w))*v 126 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (-1)*v 128 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0 ∧
      (-1)*v 72 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + ((a)/(x))*v 144 + ((1)/(x^(2:ℕ)))*v 148 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (-1)*v 138 = 0 ∧
      (((-1)*z)/(w))*v 56 + (1)*v 80 + (1)*v 150 = 0 ∧
      (1)*v 41 + (1)*v 83 + (1)*v 125 + (1)*v 167 = 0 ∧
      (1)*v 44 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 86 + (1)*v 128 = 0 ∧
      (1)*v 48 + (1)*v 132 = 0 ∧
      (1)*v 78 + (1)*v 162 = 0 ∧
      (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 = 0 ∧
      (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 45 + (1)*v 150 = 0 ∧
      (1)*v 50 + (1)*v 155 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 45 + (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 = 0 ∧
      (1)*v 80 + (1)*v 150 = 0 ∧
      (1)*v 130 + (-1)*v 150 + (((-1)*z)/(w))*v 154 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 = 0 ∧
      (-1)*v 54 + (1)*v 75 + ((1)/(x^(2:ℕ)*z))*v 150 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)))*v 144 + (((-1)*w + z*w)/(y^(2:ℕ)*z))*v 150 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 29 + (1)*v 59 + (1)*v 89 + (1)*v 119 + (1)*v 149 + (1)*v 179 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)*z))*v 150 + ((w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 150 = 0 ∧
      (1)*v 135 + ((a)/(x))*v 150 = 0 ∧
      (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (-1)*v 63 + (1)*v 77 = 0 ∧
      ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      (1)*v 72 + ((1)/(z))*v 150 + (1)*v 156 = 0 ∧
      ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + (1)*v 80 + (1)*v 130 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 78 + (1)*v 128 + ((w + y^(2:ℕ))/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 ∧
      (((-1)*z)/(y^(2:ℕ)*w))*v 63 = 0 ∧
      (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + (((-1)*x*a)/(y^(2:ℕ)))*v 165 = 0 ∧
      ((1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)))*v 63 + (1)*v 77 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0 ∧
      (1)*v 16 + ((1)/(y^(2:ℕ)))*v 162 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + ((-1)/(x^(2:ℕ)*z))*v 150 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
  have h21805 : (1)*v 58 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16286
  have h21808 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (-1)*v 128 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21325-(1)*h21805
  have h21852 : (1)*v 72 + (1)*v 142 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18272
  have h21865 : (-1)*v 72 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + ((a)/(x))*v 144 + ((1)/(x^(2:ℕ)))*v 148 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21517-(1)*h21852
  have h21877 : (1)*v 68 + (1)*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21295
  have h21892 : ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (-1)*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21544-(1)*h21877
  have h21902 : (1)*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h20349
  have h21904 : (((-1)*z)/(w))*v 56 + (1)*v 80 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2812-(((-1)*z)/(w))*h21902
  have h21908 : (1)*v 41 + (1)*v 83 + (1)*v 125 + (1)*v 167 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20350-((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*h21902
  have h21909 : (1)*v 44 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 86 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20930-((-1)/(y^(2:ℕ)*w))*h21902
  have h21911 : (1)*v 48 + (1)*v 132 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19224-((-1 + z)/(w))*h21902
  have h21912 : (1)*v 78 + (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20355-((-1)/(w))*h21902
  have h21914 : (-1)*v 54 + ((-1)/(x^(2:ℕ)*z))*v 60 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21756-((-1)/(x^(2:ℕ)*w))*h21902
  have h21923 : (1)*v 60 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20368-((z)/(w))*h21902
  have h21925 : (1)*v 29 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + (1)*v 119 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20369-((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*h21902
  have h21956 : (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18422-((z)/(x^(2:ℕ)*w))*h21902
  have h21965 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + ((w)/(y^(2:ℕ)*z))*v 60 + ((w)/(y^(2:ℕ)*z))*v 150 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20116-((1)/(y^(2:ℕ)))*h21902
  have h21966 : (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21133-((-1 + (-1)*y^(2:ℕ) + y^(2:ℕ)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*h21902
  have h21974 : ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 130 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20940-((z)/(y^(2:ℕ)*w))*h21902
  have h21977 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + (1)*v 128 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w)/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21576-((-1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)*w))*h21902
  have h22021 : ((1)/(x^(2:ℕ)))*v 60 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20456-((z)/(x^(2:ℕ)*w))*h21902
  have h22023 : (1)*v 45 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19300-(((-1)*z*a)/(x*w))*h21902
  have h22025 : (1)*v 50 + (1)*v 155 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20460-((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*h21902
  have h22031 : ((1)/(y^(2:ℕ)))*v 45 + (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20957-((z)/(y^(2:ℕ)*w))*h21902
  have h22035 : (1)*v 80 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20467-((z)/(y^(2:ℕ)*w))*h21902
  have h22163 : (1)*v 60 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21923
  have h22165 : (1)*v 130 + (-1)*v 150 + (((-1)*z)/(w))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2814-(1)*h22163
  have h22168 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21028-((-1)/(y^(2:ℕ)*z))*h22163
  have h22169 : (1)*v 80 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20762-((-1)/(y^(2:ℕ)*z))*h22163
  have h22170 : (-1)*v 54 + (1)*v 75 + ((1)/(x^(2:ℕ)*z))*v 150 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21914-((-1)/(x^(2:ℕ)*z))*h22163
  have h22171 : (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 147 + ((1)/(z))*v 150 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20356-((-1)/(z))*h22163
  have h22172 : (((-1)*w)/(y^(2:ℕ)))*v 144 + (((-1)*w + z*w)/(y^(2:ℕ)*z))*v 150 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21556-((w + (-1)*z*w)/(y^(2:ℕ)*z))*h22163
  have h22179 : (1)*v 29 + (1)*v 59 + (1)*v 89 + (1)*v 119 + (1)*v 149 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21925-((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*h22163
  have h22194 : (1)*v 63 + (1)*v 147 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h18099-((w)/(x^(2:ℕ)*z))*h22163
  have h22203 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21965-((w)/(y^(2:ℕ)*z))*h22163
  have h22213 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + (1)*v 78 + (1)*v 128 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + ((w + y^(2:ℕ))/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21977-((-1)/(z))*h22163
  have h22246 : (((-1)*w)/(y^(2:ℕ)*z))*v 150 + ((w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20455-((w)/(y^(2:ℕ)*z))*h22163
  have h22247 : ((-1)/(x^(2:ℕ)))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22021-((1)/(x^(2:ℕ)))*h22163
  have h22249 : (1)*v 135 + ((a)/(x))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20458-(((-1)*a)/(x))*h22163
  have h22342 : (1)*v 63 + (1)*v 147 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22194
  have h22343 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (-1)*v 63 + (1)*v 77 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19849-(1)*h22342
  have h22345 : ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22169-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h22342
  have h22347 : (1)*v 72 + ((1)/(z))*v 150 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22171-(((-1)*x^(2:ℕ))/(w))*h22342
  have h22361 : ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + (1)*v 80 + (1)*v 130 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21974-((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*h22342
  have h22363 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 78 + (1)*v 128 + ((w + y^(2:ℕ))/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22213-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h22342
  have h22384 : (((-1)*z)/(y^(2:ℕ)*w))*v 63 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20454-((z)/(y^(2:ℕ)*w))*h22342
  have h22386 : (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + (((-1)*x*a)/(y^(2:ℕ)))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20882-((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*h22342
  have h22388 : ((1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)))*v 63 + (1)*v 77 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20466-(1)*h22342
  have h22427 : (1)*v 16 + ((1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (x^(2:ℕ))*h21603
  have h22428 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + ((-1)/(x^(2:ℕ)*z))*v 150 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21709-((y^(2:ℕ))/(x^(2:ℕ)))*h22427
  exact ⟨h21808, h21865, h21892, h21904, h21908, h21909, h21911, h21912, h21956, h21966, h22023, h22025, h22031, h22035, h22165, h22168, h22170, h22172, h22179, h22203, h22246, h22247, h22249, h22343, h22345, h22347, h22361, h22363, h22384, h22386, h22388, h22427, h22428⟩

#print axioms positive_last_pair_reduced_rows_chunk7

theorem positive_last_pair_reduced_rows_chunk8 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h3444 : (1)*v 16 + (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 = 0)
    (h16102 : (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0)
    (h19719 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0)
    (h19805 : ((1)/(x^(2:ℕ)))*v 48 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h19928 : ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 + (((-1)*x*w*a)/(y^(2:ℕ)*z))*v 165 = 0)
    (h20347 : (1)*v 65 + (1)*v 135 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 = 0)
    (h20989 : (1)*v 45 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 87 + (1)*v 129 = 0)
    (h21107 : (((-1)*x*a)/(y^(2:ℕ)))*v 27 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (1)*v 194 = 0)
    (h21300 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + ((w + (-1)*z*w)/(y^(2:ℕ)*z))*v 150 = 0)
    (h21605 : (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0)
    (h21781 : (1)*v 124 + (-1)*v 152 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 + (1)*v 166 = 0)
    (h21808 : (1)*v 16 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (-1)*v 128 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + (1)*v 184 = 0)
    (h21904 : (((-1)*z)/(w))*v 56 + (1)*v 80 + (1)*v 150 = 0)
    (h21909 : (1)*v 44 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 86 + (1)*v 128 = 0)
    (h21956 : (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 = 0)
    (h21966 : (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(y^(2:ℕ)*z))*v 165 = 0)
    (h22023 : (1)*v 45 + (1)*v 150 = 0)
    (h22031 : ((1)/(y^(2:ℕ)))*v 45 + (((-1)*x*z*a)/(y^(2:ℕ)*w))*v 63 + (1)*v 95 = 0)
    (h22035 : (1)*v 80 + (1)*v 150 = 0)
    (h22165 : (1)*v 130 + (-1)*v 150 + (((-1)*z)/(w))*v 154 = 0)
    (h22168 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (1)*v 130 = 0)
    (h22170 : (-1)*v 54 + (1)*v 75 + ((1)/(x^(2:ℕ)*z))*v 150 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h22172 : (((-1)*w)/(y^(2:ℕ)))*v 144 + (((-1)*w + z*w)/(y^(2:ℕ)*z))*v 150 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h22203 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h22246 : (((-1)*w)/(y^(2:ℕ)*z))*v 150 + ((w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h22247 : ((-1)/(x^(2:ℕ)))*v 150 = 0)
    (h22249 : (1)*v 135 + ((a)/(x))*v 150 = 0)
    (h22343 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (-1)*v 63 + (1)*v 77 = 0)
    (h22345 : ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 80 + (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0)
    (h22347 : (1)*v 72 + ((1)/(z))*v 150 + (1)*v 156 = 0)
    (h22361 : ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + (1)*v 80 + (1)*v 130 + (1)*v 160 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0)
    (h22363 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 78 + (1)*v 128 + ((w + y^(2:ℕ))/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0)
    (h22384 : (((-1)*z)/(y^(2:ℕ)*w))*v 63 = 0)
    (h22386 : (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + (((-1)*x*a)/(y^(2:ℕ)))*v 165 = 0)
    (h22388 : ((1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)))*v 63 + (1)*v 77 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0)
    (h22427 : (1)*v 16 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h22428 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + ((-1)/(x^(2:ℕ)*z))*v 150 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0)
    : ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 162 = 0 ∧
      (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 = 0 ∧
      (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 + (1)*v 130 = 0 ∧
      (1)*v 80 + (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 45 + (1)*v 95 = 0 ∧
      (((-1)*z)/(w))*v 56 + (1)*v 80 = 0 ∧
      (1)*v 130 + (((-1)*z)/(w))*v 154 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 = 0 ∧
      (1)*v 72 + (1)*v 156 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (-1)*v 128 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + (1)*v 78 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 ∧
      (1)*v 77 = 0 ∧
      (1)*v 80 = 0 ∧
      (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 154 = 0 ∧
      (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 = 0 ∧
      ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + (1)*v 80 + (1)*v 130 + (1)*v 160 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0 ∧
      ((-1)/(y^(2:ℕ)))*v 48 + (((-1)*a^(2:ℕ))/(y^(2:ℕ)))*v 54 + (1)*v 89 + ((x*a)/(y^(2:ℕ)))*v 132 + ((1)/(x^(2:ℕ)))*v 146 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 45 + (1)*v 75 = 0 ∧
      (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 95 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 ∧
      (1)*v 45 = 0 ∧
      (1)*v 44 + (1)*v 86 + (1)*v 128 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 48 + (1)*v 87 + (1)*v 129 = 0 := by
  have h22434 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (-1)*v 128 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21808-(1)*h22427
  have h22450 : ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21605-(((-1)*a)/(x))*h22427
  have h22453 : (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3444-(1)*h22427
  have h22473 : (1)*v 63 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*y^(2:ℕ)*w)/(z))*h22384
  have h22474 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22343-(-1)*h22473
  have h22478 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 + (1)*v 130 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22168-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*h22473
  have h22479 : (1)*v 80 + (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22345-((x^(2:ℕ))/(y^(2:ℕ)*w))*h22473
  have h22505 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + (1)*v 78 + (1)*v 128 + ((w + y^(2:ℕ))/(y^(2:ℕ)*z))*v 150 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22363-((x^(2:ℕ))/(y^(2:ℕ)*w))*h22473
  have h22535 : ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 + (((-1)*x*a)/(y^(2:ℕ)))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22386-(((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*h22473
  have h22539 : ((1)/(y^(2:ℕ)))*v 45 + (1)*v 95 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22031-(((-1)*x*z*a)/(y^(2:ℕ)*w))*h22473
  have h22541 : (1)*v 77 + (((-1)*w*b)/(x^(2:ℕ)*y*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22388-((1 + (-1)*y^(2:ℕ))/(y^(2:ℕ)))*h22473
  have h22596 : ((1)/(y^(2:ℕ)))*v 48 + (1)*v 194 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((x^(2:ℕ))/(y^(2:ℕ)))*h19805
  have h22597 : ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 + (1)*v 75 + ((1)/(x^(2:ℕ)*z))*v 150 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22170-((y^(2:ℕ))/(x^(2:ℕ)))*h22596
  have h22619 : (((-1)*x*a)/(y^(2:ℕ)))*v 27 + ((-1)/(y^(2:ℕ)))*v 48 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21107-(1)*h22596
  have h22642 : (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)*x^(2:ℕ))*h22247
  have h22644 : (1)*v 65 + (1)*v 135 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20347-((-1)/(x^(2:ℕ)*y^(2:ℕ)))*h22642
  have h22645 : (((-1)*z)/(w))*v 56 + (1)*v 80 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21904-(1)*h22642
  have h22646 : (1)*v 130 + (((-1)*z)/(w))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22165-(-1)*h22642
  have h22651 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 135 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22428-((-1)/(x^(2:ℕ)*z))*h22642
  have h22652 : ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22597-((1)/(x^(2:ℕ)*z))*h22642
  have h22654 : (1)*v 72 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22347-((1)/(z))*h22642
  have h22655 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21300-((w + (-1)*z*w)/(y^(2:ℕ)*z))*h22642
  have h22656 : (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22172-(((-1)*w + z*w)/(y^(2:ℕ)*z))*h22642
  have h22679 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (-1)*v 128 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22434-((-1)/(y^(2:ℕ)*z))*h22642
  have h22690 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + (1)*v 78 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22505-((w + y^(2:ℕ))/(y^(2:ℕ)*z))*h22642
  have h22715 : ((w)/(y^(2:ℕ)*z))*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22246-(((-1)*w)/(y^(2:ℕ)*z))*h22642
  have h22718 : (1)*v 135 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22249-((a)/(x))*h22642
  have h22719 : (1)*v 45 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22023-(1)*h22642
  have h22728 : (1)*v 77 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22541-(((-1)*w*b)/(x^(2:ℕ)*y*z))*h22642
  have h22729 : (1)*v 80 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22035-(1)*h22642
  have h22817 : (1)*v 165 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((y^(2:ℕ)*z)/(w))*h22715
  have h22818 : (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21781-((x^(2:ℕ))/(y^(2:ℕ)))*h22817
  have h22820 : (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22656-((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*h22817
  have h22838 : (1)*v 45 + (1)*v 75 + (1)*v 135 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21956-(1)*h22817
  have h22841 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22203-((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*h22817
  have h22842 : (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21966-((-1)/(y^(2:ℕ)*z))*h22817
  have h22846 : ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + (1)*v 80 + (1)*v 130 + (1)*v 160 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22361-((x^(2:ℕ))/(y^(2:ℕ)))*h22817
  have h22872 : ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19928-(((-1)*x*w*a)/(y^(2:ℕ)*z))*h22817
  have h22873 : ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22535-(((-1)*x*a)/(y^(2:ℕ)))*h22817
  have h22982 : (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16102
  have h23006 : ((-1)/(y^(2:ℕ)))*v 48 + (((-1)*a^(2:ℕ))/(y^(2:ℕ)))*v 54 + (1)*v 89 + ((x*a)/(y^(2:ℕ)))*v 132 + ((1)/(x^(2:ℕ)))*v 146 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22619-(((-1)*x*a)/(y^(2:ℕ)))*h22982
  have h23026 : (1)*v 135 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22718
  have h23027 : (1)*v 65 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22644-(1)*h23026
  have h23029 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22651-(1)*h23026
  have h23039 : (1)*v 45 + (1)*v 75 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22838-(1)*h23026
  have h23072 : (1)*v 65 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23027
  have h23074 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 95 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19719-(1)*h23072
  have h23118 : (1)*v 45 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22719
  have h23119 : (1)*v 44 + (1)*v 86 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21909-((x^(2:ℕ))/(y^(2:ℕ)))*h23118
  have h23120 : ((1)/(x^(2:ℕ)))*v 48 + (1)*v 87 + (1)*v 129 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20989-(1)*h23118
  exact ⟨h22450, h22453, h22474, h22478, h22479, h22539, h22645, h22646, h22652, h22654, h22655, h22679, h22690, h22728, h22729, h22818, h22820, h22841, h22842, h22846, h22872, h22873, h23006, h23029, h23039, h23074, h23118, h23119, h23120⟩

#print axioms positive_last_pair_reduced_rows_chunk8

theorem positive_last_pair_reduced_rows_chunk9 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h16283 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0)
    (h19135 : (1)*v 80 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0)
    (h21144 : ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 78 + (((-1)*a)/(x))*v 156 = 0)
    (h21375 : (1)*v 57 + (1)*v 162 = 0)
    (h21614 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((1)/(y^(2:ℕ)))*v 87 = 0)
    (h22025 : (1)*v 50 + (1)*v 155 = 0)
    (h22450 : ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 162 = 0)
    (h22474 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 = 0)
    (h22478 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 + (1)*v 130 = 0)
    (h22479 : (1)*v 80 + (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0)
    (h22539 : ((1)/(y^(2:ℕ)))*v 45 + (1)*v 95 = 0)
    (h22645 : (((-1)*z)/(w))*v 56 + (1)*v 80 = 0)
    (h22646 : (1)*v 130 + (((-1)*z)/(w))*v 154 = 0)
    (h22652 : ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 = 0)
    (h22655 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 = 0)
    (h22679 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (-1)*v 128 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0)
    (h22690 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*v 45 + (1)*v 48 + ((-1)/(z))*v 50 + (1)*v 78 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0)
    (h22728 : (1)*v 77 = 0)
    (h22729 : (1)*v 80 = 0)
    (h22820 : (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 = 0)
    (h22841 : ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 56 + (1)*v 154 = 0)
    (h22842 : (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 57 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 = 0)
    (h22846 : ((x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 50 + (1)*v 80 + (1)*v 130 + (1)*v 160 = 0)
    (h22872 : ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0)
    (h22873 : ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0)
    (h23029 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0)
    (h23039 : (1)*v 45 + (1)*v 75 = 0)
    (h23074 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 95 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0)
    (h23118 : (1)*v 45 = 0)
    (h23120 : ((1)/(x^(2:ℕ)))*v 48 + (1)*v 87 + (1)*v 129 = 0)
    : (-1)*v 128 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0 ∧
      ((-1)/(y^(2:ℕ)))*v 78 + (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 156 + ((a)/(x*y^(2:ℕ)))*v 162 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 48 + (1)*v 129 + ((-1)/(x^(2:ℕ)))*v 138 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 48 + (1)*v 78 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 ∧
      (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 185 = 0 ∧
      (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      (1)*v 125 = 0 ∧
      (((-1)*a)/(x))*v 160 + (1)*v 185 = 0 ∧
      (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)))*v 66 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)))*v 144 = 0 ∧
      (1)*v 29 + (-1)*v 78 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((a)/(x))*v 156 + (-1)*v 162 = 0 ∧
      (1)*v 119 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 ∧
      (1)*v 160 = 0 := by
  have h23121 : (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22655-((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*h23118
  have h23139 : (1)*v 75 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23039-(1)*h23118
  have h23142 : (1)*v 56 + (1)*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22841-((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*h23118
  have h23144 : (-1)*v 128 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22679-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*h23118
  have h23147 : (1)*v 50 + (1)*v 80 + (1)*v 130 + (1)*v 160 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22846-((x^(2:ℕ))/(y^(2:ℕ)))*h23118
  have h23149 : (1)*v 48 + ((-1)/(z))*v 50 + (1)*v 78 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22690-(((-1)*x^(2:ℕ))/(y^(2:ℕ)*z))*h23118
  have h23176 : (1)*v 95 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22539-((1)/(y^(2:ℕ)))*h23118
  have h23227 : (1)*v 75 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23139
  have h23230 : ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22652-(1)*h23227
  have h23291 : (1)*v 56 + (1)*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23142
  have h23292 : (1)*v 80 + ((z)/(w))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22645-(((-1)*z)/(w))*h23291
  have h23294 : ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23029-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h23291
  have h23295 : (((-1)*w)/(y^(2:ℕ)))*v 66 + (-1)*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23121-(1)*h23291
  have h23316 : (1)*v 119 + ((-1)/(x^(2:ℕ)))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22872-((1)/(x^(2:ℕ)))*h23291
  have h23360 : (1)*v 57 + (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21375
  have h23363 : (1)*v 29 + ((y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + (-1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22842-(1)*h23360
  have h23413 : (1)*v 32 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 78 + (((-1)*x*a)/(y^(2:ℕ)))*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((x^(2:ℕ))/(y^(2:ℕ)))*h21144
  have h23418 : (1)*v 29 + (-1)*v 78 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((a)/(x))*v 156 + (-1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23363-((y^(2:ℕ))/(x^(2:ℕ)))*h23413
  have h23436 : ((-1)/(y^(2:ℕ)))*v 78 + (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 156 + ((a)/(x*y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22450-((1)/(x^(2:ℕ)))*h23413
  have h23468 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h16283
  have h23469 : ((1)/(x^(2:ℕ)))*v 48 + (1)*v 129 + ((-1)/(x^(2:ℕ)))*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23120-(1)*h23468
  have h23484 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21614-((1)/(y^(2:ℕ)))*h23468
  have h23493 : (1)*v 95 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23176
  have h23494 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23074-(1)*h23493
  have h23511 : (1)*v 77 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22728
  have h23512 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22474-(1)*h23511
  have h23529 : (1)*v 50 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*x^(2:ℕ)*z)/(w))*h23512
  have h23537 : (1)*v 80 + (1)*v 130 + (1)*v 160 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23147-(1)*h23529
  have h23538 : (1)*v 48 + (1)*v 78 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23149-((-1)/(z))*h23529
  have h23555 : (1)*v 155 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22025-(1)*h23529
  have h23574 : (1)*v 155 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23555
  have h23575 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23494-(1)*h23574
  have h23577 : (1)*v 29 + (-1)*v 78 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((-1)/(x^(2:ℕ)*w))*v 154 + ((a)/(x))*v 156 + (-1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23418-(1)*h23574
  have h23592 : (1)*v 80 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22729
  have h23593 : ((z)/(w))*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23292-(1)*h23592
  have h23595 : (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22479-(1)*h23592
  have h23603 : (1)*v 130 + (1)*v 160 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23537-(1)*h23592
  have h23618 : (1)*v 125 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22873-((1)/(x^(2:ℕ)))*h23592
  have h23620 : (((-1)*a)/(x))*v 160 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19135-(1)*h23592
  have h23636 : (1)*v 154 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((w)/(z))*h23593
  have h23637 : (1)*v 130 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22646-(((-1)*z)/(w))*h23636
  have h23640 : (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23294-((y^(2:ℕ))/(x^(2:ℕ)*w))*h23636
  have h23641 : ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23230-(((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*h23636
  have h23642 : (((-1)*w)/(y^(2:ℕ)))*v 66 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23295-(-1)*h23636
  have h23643 : (((-1)*w)/(y^(2:ℕ)))*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22820-(1)*h23636
  have h23656 : (1)*v 29 + (-1)*v 78 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((a)/(x))*v 156 + (-1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23577-((-1)/(x^(2:ℕ)*w))*h23636
  have h23682 : (1)*v 119 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23316-((-1)/(x^(2:ℕ)))*h23636
  have h23720 : (1)*v 130 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23637
  have h23722 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22478-(1)*h23720
  have h23730 : (1)*v 160 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23603-(1)*h23720
  exact ⟨h23144, h23436, h23469, h23484, h23538, h23575, h23595, h23618, h23620, h23640, h23641, h23642, h23643, h23656, h23682, h23722, h23730⟩

#print axioms positive_last_pair_reduced_rows_chunk9

theorem positive_last_pair_reduced_rows_chunk10 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h3294 : (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0)
    (h3368 : (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0)
    (h20033 : (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((1)/(x^(2:ℕ)))*v 158 + (((-1)*a)/(x))*v 184 = 0)
    (h20777 : (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0)
    (h21371 : (((-1)*a)/(x))*v 48 + (1)*v 129 = 0)
    (h21373 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0)
    (h21382 : ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0)
    (h21519 : ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0)
    (h21607 : (1)*v 81 + (((-1)*a)/(x))*v 162 = 0)
    (h21612 : (1)*v 81 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 151 = 0)
    (h21619 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 129 = 0)
    (h21794 : (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0)
    (h21865 : (-1)*v 72 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + ((a)/(x))*v 144 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h21892 : ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (-1)*v 138 = 0)
    (h21908 : (1)*v 41 + (1)*v 83 + (1)*v 125 + (1)*v 167 = 0)
    (h21911 : (1)*v 48 + (1)*v 132 = 0)
    (h21912 : (1)*v 78 + (1)*v 162 = 0)
    (h22179 : (1)*v 29 + (1)*v 59 + (1)*v 89 + (1)*v 119 + (1)*v 149 + (1)*v 179 = 0)
    (h22453 : (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 = 0)
    (h22818 : (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0)
    (h23006 : ((-1)/(y^(2:ℕ)))*v 48 + (((-1)*a^(2:ℕ))/(y^(2:ℕ)))*v 54 + (1)*v 89 + ((x*a)/(y^(2:ℕ)))*v 132 + ((1)/(x^(2:ℕ)))*v 146 = 0)
    (h23119 : (1)*v 44 + (1)*v 86 + (1)*v 128 = 0)
    (h23436 : ((-1)/(y^(2:ℕ)))*v 78 + (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 156 + ((a)/(x*y^(2:ℕ)))*v 162 = 0)
    (h23469 : ((1)/(x^(2:ℕ)))*v 48 + (1)*v 129 + ((-1)/(x^(2:ℕ)))*v 138 = 0)
    (h23484 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0)
    (h23538 : (1)*v 48 + (1)*v 78 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (1)*v 188 = 0)
    (h23575 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 185 = 0)
    (h23618 : (1)*v 125 = 0)
    (h23620 : (((-1)*a)/(x))*v 160 + (1)*v 185 = 0)
    (h23656 : (1)*v 29 + (-1)*v 78 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((a)/(x))*v 156 + (-1)*v 162 = 0)
    (h23682 : (1)*v 119 = 0)
    (h23722 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0)
    (h23730 : (1)*v 160 = 0)
    : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 = 0 ∧
      (1)*v 29 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((a)/(x))*v 156 = 0 ∧
      (1)*v 48 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (-1)*v 162 + (1)*v 188 = 0 ∧
      (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 156 + ((a + x)/(x*y^(2:ℕ)))*v 162 = 0 ∧
      ((a)/(x))*v 48 + (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 ∧
      ((-1 + (-1)*x*a)/(y^(2:ℕ)))*v 48 + ((-1 + (-1)*x^(2:ℕ)*a^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 ∧
      ((1 + x*a)/(x^(2:ℕ)))*v 48 + ((-1)/(x^(2:ℕ)))*v 72 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 ∧
      (-1)*v 46 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (((-1)*a)/(x^(3:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((a)/(x))*v 162 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0 ∧
      (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (1)*v 59 + (((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*v 72 + ((a)/(x))*v 88 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 + (1 + (-1)*a^(2:ℕ))*v 144 = 0 ∧
      (-1)*v 44 + (((-1)*b)/(y))*v 48 + (-1)*v 128 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (-1)*v 62 + (1)*v 76 + ((-1)/(x^(2:ℕ)))*v 122 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + ((-1)/(x^(2:ℕ)))*v 164 + (-1)*v 188 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 := by
  have h23764 : (1)*v 160 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23730
  have h23791 : (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23620-(((-1)*a)/(x))*h23764
  have h23826 : (1)*v 119 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23682
  have h23829 : (1)*v 29 + (1)*v 59 + (1)*v 89 + (1)*v 149 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22179-(1)*h23826
  have h23844 : (1)*v 125 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23618
  have h23845 : (1)*v 41 + (1)*v 83 + (1)*v 167 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21908-(1)*h23844
  have h23847 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23575-(1)*h23844
  have h23952 : (1)*v 185 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23791
  have h23953 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23847-(1)*h23952
  have h23988 : (1)*v 48 + (1)*v 132 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21911
  have h24040 : ((-1 + (-1)*x*a)/(y^(2:ℕ)))*v 48 + (((-1)*a^(2:ℕ))/(y^(2:ℕ)))*v 54 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23006-((x*a)/(y^(2:ℕ)))*h23988
  have h24079 : (1)*v 78 + (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21912
  have h24093 : (1)*v 29 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((a)/(x))*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23656-(-1)*h24079
  have h24097 : (1)*v 48 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (-1)*v 162 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23538-(1)*h24079
  have h24128 : (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 156 + ((a + x)/(x*y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23436-((-1)/(y^(2:ℕ)))*h24079
  have h24263 : (((-1)*a)/(x))*v 48 + (1)*v 129 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21371
  have h24264 : ((1 + x*a)/(x^(2:ℕ)))*v 48 + ((-1)/(x^(2:ℕ)))*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23469-(1)*h24263
  have h24278 : ((a)/(x))*v 48 + (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21619-(1)*h24263
  have h24310 : (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21794
  have h24311 : (1)*v 83 + (-1)*v 146 + (((-1)*a)/(x))*v 152 + ((-1)/(x^(2:ℕ)))*v 164 + (1)*v 167 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23845-(1)*h24310
  have h24332 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21373
  have h24333 : (1)*v 29 + (-1)*v 44 + (1)*v 59 + ((a)/(x))*v 88 + (1)*v 89 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23829-(1)*h24332
  have h24343 : (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h3294
  have h24349 : (-1)*v 46 + (1)*v 81 + ((a)/(x))*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + ((-1)/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21612-(1)*h24343
  have h24376 : (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h20777
  have h24377 : (-1)*v 62 + (1)*v 83 + ((a)/(x))*v 124 + (-1)*v 146 + (((-1)*a)/(x))*v 152 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + ((-1)/(x^(2:ℕ)))*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24311-(1)*h24376
  have h24409 : ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21519
  have h24410 : (1)*v 29 + (-1)*v 44 + (1)*v 59 + ((-1)/(x^(2:ℕ)))*v 86 + ((a)/(x))*v 88 + (1)*v 89 + (1)*v 144 + ((a)/(x))*v 148 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24333-(1)*h24409
  have h24431 : (1)*v 81 + (((-1)*a)/(x))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21607
  have h24446 : (-1)*v 46 + ((a)/(x))*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + ((a)/(x))*v 162 + ((-1)/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24349-(1)*h24431
  have h24456 : (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h3368
  have h24457 : (-1)*v 62 + ((-1)/(x^(2:ℕ)))*v 122 + ((a)/(x))*v 124 + (-1)*v 146 + (((-1)*a)/(x))*v 152 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + ((-1)/(x^(2:ℕ)))*v 164 + ((a)/(x))*v 166 + (-1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24377-(1)*h24456
  have h24489 : (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((1)/(x^(2:ℕ)))*v 158 + (((-1)*a)/(x))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h20033
  have h24510 : (-1)*v 46 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (((-1)*a)/(x^(3:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((a)/(x))*v 162 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24446-((a)/(x))*h24489
  have h24570 : ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21382
  have h24571 : ((1)/(y^(2:ℕ)))*v 54 + (-1)*v 62 + (1)*v 76 + ((-1)/(x^(2:ℕ)))*v 122 + ((a)/(x))*v 124 + (((-1)*a)/(x))*v 152 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + ((-1)/(x^(2:ℕ)))*v 164 + ((a)/(x))*v 166 + (-1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24457-(-1)*h24570
  have h24590 : ((-1 + (-1)*x*a)/(y^(2:ℕ)))*v 48 + ((-1 + (-1)*x^(2:ℕ)*a^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24040-((1)/(x^(2:ℕ)))*h24570
  have h24604 : (-1)*v 72 + (1)*v 138 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)*x^(2:ℕ)*y^(2:ℕ))*h23484
  have h24605 : ((1 + x*a)/(x^(2:ℕ)))*v 48 + ((-1)/(x^(2:ℕ)))*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24264-((-1)/(x^(2:ℕ)))*h24604
  have h24661 : ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + ((a)/(x))*v 144 + ((1)/(x^(2:ℕ)))*v 148 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21865-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h24604
  have h24663 : ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21892-(-1)*h24604
  have h24664 : (-1)*v 46 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (((-1)*a)/(x^(3:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((a)/(x))*v 162 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24510-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h24604
  have h24719 : ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(y^(2:ℕ)))*v 72 + (x*a)*v 144 + (1)*v 148 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (x^(2:ℕ))*h24661
  have h24722 : (1)*v 29 + (-1)*v 44 + (1)*v 59 + (((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*v 72 + ((-1)/(x^(2:ℕ)))*v 86 + ((a)/(x))*v 88 + (1)*v 89 + (1 + (-1)*a^(2:ℕ))*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24410-((a)/(x))*h24719
  have h24792 : (1)*v 44 + (1)*v 86 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23119
  have h24796 : (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (1)*v 59 + (((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*v 72 + ((a)/(x))*v 88 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 + (1 + (-1)*a^(2:ℕ))*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24722-((-1)/(x^(2:ℕ)))*h24792
  have h24816 : (-1)*v 44 + (((-1)*b)/(y))*v 48 + (-1)*v 128 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22453-(1)*h24792
  have h24839 : (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22818
  have h24840 : ((1)/(y^(2:ℕ)))*v 54 + (-1)*v 62 + (1)*v 76 + ((-1)/(x^(2:ℕ)))*v 122 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + ((-1)/(x^(2:ℕ)))*v 164 + (-1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24571-((a)/(x))*h24839
  have h24886 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23722
  exact ⟨h23953, h24093, h24097, h24128, h24278, h24590, h24605, h24663, h24664, h24796, h24816, h24840, h24886⟩

#print axioms positive_last_pair_reduced_rows_chunk10

theorem positive_last_pair_reduced_rows_chunk11 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h21383 : (((-1)*b)/(y))*v 54 + (1)*v 88 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h22654 : (1)*v 72 + (1)*v 156 = 0)
    (h23144 : (-1)*v 128 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0)
    (h23595 : (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0)
    (h23640 : (-1)*v 156 + ((-1)/(x^(2:ℕ)))*v 162 = 0)
    (h23641 : ((-1)/(x^(2:ℕ)))*v 48 + (-1)*v 54 = 0)
    (h23642 : (((-1)*w)/(y^(2:ℕ)))*v 66 = 0)
    (h23643 : (((-1)*w)/(y^(2:ℕ)))*v 144 = 0)
    (h23953 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 = 0)
    (h24093 : (1)*v 29 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + ((a)/(x))*v 156 = 0)
    (h24097 : (1)*v 48 + (1)*v 128 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 158 + (-1)*v 162 + (1)*v 188 = 0)
    (h24128 : (1)*v 113 + ((a)/(x*y^(2:ℕ)))*v 156 + ((a + x)/(x*y^(2:ℕ)))*v 162 = 0)
    (h24278 : ((a)/(x))*v 48 + (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0)
    (h24590 : ((-1 + (-1)*x*a)/(y^(2:ℕ)))*v 48 + ((-1 + (-1)*x^(2:ℕ)*a^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0)
    (h24605 : ((1 + x*a)/(x^(2:ℕ)))*v 48 + ((-1)/(x^(2:ℕ)))*v 72 = 0)
    (h24663 : ((1)/(x^(2:ℕ)))*v 62 + ((a)/(x))*v 66 + ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0)
    (h24664 : (-1)*v 46 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (((-1)*a)/(x^(3:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((a)/(x))*v 162 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0)
    (h24796 : (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (1)*v 59 + (((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*v 72 + ((a)/(x))*v 88 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 + (1 + (-1)*a^(2:ℕ))*v 144 = 0)
    (h24816 : (-1)*v 44 + (((-1)*b)/(y))*v 48 + (-1)*v 128 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 + ((-1)/(y^(2:ℕ)))*v 162 = 0)
    (h24840 : ((1)/(y^(2:ℕ)))*v 54 + (-1)*v 62 + (1)*v 76 + ((-1)/(x^(2:ℕ)))*v 122 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + ((-1)/(x^(2:ℕ)))*v 164 + (-1)*v 188 = 0)
    (h24886 : (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0)
    : (-1)*v 62 + (1)*v 76 + (-1)*v 188 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 ∧
      (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (1)*v 59 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 = 0 ∧
      (1)*v 29 + (1)*v 113 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 62 = 0 ∧
      (1)*v 59 = 0 ∧
      (-1)*v 128 + (1)*v 184 = 0 ∧
      (1)*v 128 + (1)*v 158 + (1)*v 188 = 0 ∧
      (-1)*v 46 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0 ∧
      (-1)*v 44 + (-1)*v 128 = 0 ∧
      (-1)*v 46 + (1)*v 158 = 0 ∧
      (1)*v 113 = 0 := by
  have h24890 : (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (((-1)*a)/(x*y^(2:ℕ)))*v 54 + (1)*v 59 + (((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*v 72 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 + (1 + (-1)*a^(2:ℕ))*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24796-((a)/(x))*h24886
  have h24909 : (-1)*v 46 + ((-1 + (-1)*y*b)/(y^(2:ℕ)))*v 54 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h21383-(1)*h24886
  have h24930 : (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h23595
  have h24931 : ((1)/(y^(2:ℕ)))*v 54 + (-1)*v 62 + (1)*v 76 + (-1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24840-((-1)/(x^(2:ℕ)))*h24930
  have h24964 : (1)*v 72 + (1)*v 156 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h22654
  have h24966 : (1)*v 72 + ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23640-(-1)*h24964
  have h24990 : (1)*v 29 + (((-1)*a)/(x))*v 72 + (1)*v 113 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24093-((a)/(x))*h24964
  have h24991 : (-1)*v 72 + (-1)*v 128 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23144-(1)*h24964
  have h24998 : (1)*v 48 + ((-1)/(y^(2:ℕ)))*v 72 + (1)*v 128 + (1)*v 158 + (-1)*v 162 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24097-((1)/(y^(2:ℕ)))*h24964
  have h25040 : (((-1)*a)/(x*y^(2:ℕ)))*v 72 + (1)*v 113 + ((a + x)/(x*y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24128-((a)/(x*y^(2:ℕ)))*h24964
  have h25047 : (-1)*v 44 + (((-1)*b)/(y))*v 48 + (-1)*v 72 + (-1)*v 128 + ((1)/(y^(2:ℕ)))*v 144 + ((-1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24816-(1)*h24964
  have h25117 : (1)*v 66 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*y^(2:ℕ))/(w))*h23642
  have h25172 : ((1)/(x^(2:ℕ)))*v 62 + ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24663-((a)/(x))*h25117
  have h25225 : (1)*v 144 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*y^(2:ℕ))/(w))*h23643
  have h25230 : (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (((-1)*a)/(x*y^(2:ℕ)))*v 54 + (1)*v 59 + (((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*v 72 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24890-(1 + (-1)*a^(2:ℕ))*h25225
  have h25233 : (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23953-(((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*h25225
  have h25251 : (1)*v 29 + (((-1)*a)/(x))*v 72 + (1)*v 113 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24990-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h25225
  have h25292 : (-1)*v 46 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((a)/(x))*v 162 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24664-(((-1)*a)/(x^(3:ℕ)*y^(2:ℕ)))*h25225
  have h25293 : (-1)*v 44 + (((-1)*b)/(y))*v 48 + (-1)*v 72 + (-1)*v 128 + ((-1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25047-((1)/(y^(2:ℕ)))*h25225
  have h25352 : (1)*v 54 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*x^(2:ℕ)*y^(2:ℕ))/(z))*h25233
  have h25353 : (-1)*v 62 + (1)*v 76 + (-1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24931-((1)/(y^(2:ℕ)))*h25352
  have h25354 : ((-1)/(x^(2:ℕ)))*v 48 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h23641-(-1)*h25352
  have h25359 : (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (1)*v 59 + (((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*v 72 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25230-(((-1)*a)/(x*y^(2:ℕ)))*h25352
  have h25424 : ((-1 + (-1)*x*a)/(y^(2:ℕ)))*v 48 + ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24590-((-1 + (-1)*x^(2:ℕ)*a^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*h25352
  have h25428 : (-1)*v 46 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24909-((-1 + (-1)*y*b)/(y^(2:ℕ)))*h25352
  have h25488 : (1)*v 48 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)*x^(2:ℕ))*h25354
  have h25489 : ((-1)/(x^(2:ℕ)))*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24605-((1 + x*a)/(x^(2:ℕ)))*h25488
  have h25523 : ((-1)/(y^(2:ℕ)))*v 72 + (1)*v 128 + (1)*v 158 + (-1)*v 162 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24998-(1)*h25488
  have h25560 : ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25424-((-1 + (-1)*x*a)/(y^(2:ℕ)))*h25488
  have h25565 : (-1)*v 44 + (-1)*v 72 + (-1)*v 128 + ((-1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25293-(((-1)*b)/(y))*h25488
  have h25580 : (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24278-((a)/(x))*h25488
  have h25631 : (1)*v 72 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)*x^(2:ℕ))*h25489
  have h25634 : ((-1)/(x^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24966-(1)*h25631
  have h25642 : (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (1)*v 59 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25359-(((-1)*a + x^(2:ℕ)*y^(2:ℕ)*a)/(x*y^(2:ℕ)))*h25631
  have h25685 : (1)*v 29 + (1)*v 113 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25251-(((-1)*a)/(x))*h25631
  have h25687 : (-1)*v 128 + ((-1)/(y^(2:ℕ)))*v 162 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h24991-(-1)*h25631
  have h25697 : (1)*v 128 + (1)*v 158 + (-1)*v 162 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25523-((-1)/(y^(2:ℕ)))*h25631
  have h25743 : (1)*v 113 + ((a + x)/(x*y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25040-(((-1)*a)/(x*y^(2:ℕ)))*h25631
  have h25751 : ((1)/(x^(2:ℕ)))*v 62 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25172-((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)))*h25631
  have h25756 : (-1)*v 46 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((a)/(x))*v 162 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25292-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h25631
  have h25757 : (-1)*v 44 + (-1)*v 128 + ((-1)/(y^(2:ℕ)))*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25565-(-1)*h25631
  have h25774 : (1)*v 59 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25580-((1)/(x^(2:ℕ)*y^(2:ℕ)))*h25631
  have h25878 : (1)*v 162 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)*x^(2:ℕ))*h25634
  have h25906 : (-1)*v 128 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25687-((-1)/(y^(2:ℕ)))*h25878
  have h25913 : (1)*v 128 + (1)*v 158 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25697-(-1)*h25878
  have h25947 : (1)*v 113 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25743-((a + x)/(x*y^(2:ℕ)))*h25878
  have h25954 : (-1)*v 46 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25756-((a)/(x))*h25878
  have h25956 : (-1)*v 44 + (-1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25757-((-1)/(y^(2:ℕ)))*h25878
  have h25957 : (-1)*v 46 + (1)*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25428-((1)/(y^(2:ℕ)))*h25878
  have h26021 : (1)*v 113 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h25947
  exact ⟨h25353, h25560, h25642, h25685, h25751, h25774, h25906, h25913, h25954, h25956, h25957, h26021⟩

#print axioms positive_last_pair_reduced_rows_chunk11

theorem positive_last_pair_reduced_rows_chunk12 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h25353 : (-1)*v 62 + (1)*v 76 + (-1)*v 188 = 0)
    (h25560 : ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0)
    (h25642 : (1)*v 29 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (1)*v 59 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 = 0)
    (h25685 : (1)*v 29 + (1)*v 113 = 0)
    (h25751 : ((1)/(x^(2:ℕ)))*v 62 = 0)
    (h25774 : (1)*v 59 = 0)
    (h25906 : (-1)*v 128 + (1)*v 184 = 0)
    (h25913 : (1)*v 128 + (1)*v 158 + (1)*v 188 = 0)
    (h25954 : (-1)*v 46 + (((-1)*a)/(x^(3:ℕ)))*v 158 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 184 = 0)
    (h25956 : (-1)*v 44 + (-1)*v 128 = 0)
    (h25957 : (-1)*v 46 + (1)*v 158 = 0)
    (h26021 : (1)*v 113 = 0)
    : ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 128 + (((-1)*a + (-1)*x^(3:ℕ))/(x^(3:ℕ)))*v 158 = 0 ∧
      (1 + (-1)*x^(2:ℕ))*v 128 + (1 + x*a)*v 158 = 0 := by
  have h26022 : (1)*v 29 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25685-(1)*h26021
  have h26032 : (1)*v 29 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h26022
  have h26033 : ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (1)*v 59 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25642-(1)*h26032
  have h26043 : (1)*v 62 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (x^(2:ℕ))*h25751
  have h26044 : (1)*v 76 + (-1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25353-(-1)*h26043
  have h26093 : (1)*v 59 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h25774
  have h26094 : ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + (1)*v 89 + ((1)/(x^(2:ℕ)))*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h26033-(1)*h26093
  have h26159 : (-1)*v 76 + (1)*v 188 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (-1)*h26044
  have h26171 : (1)*v 76 + (1)*v 128 + (1)*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25913-(1)*h26159
  have h26227 : (-1)*v 128 + (1)*v 184 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h25906
  have h26262 : (-1)*v 46 + ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 128 + (((-1)*a)/(x^(3:ℕ)))*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h25954-((-1 + a^(2:ℕ))/(x^(2:ℕ)))*h26227
  have h26358 : ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h25560
  have h26359 : ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 44 + (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 76 + ((1)/(x^(2:ℕ)))*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h26094-(1)*h26358
  have h26369 : (1)*v 44 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (-1)*h25956
  have h26370 : (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 76 + (1)*v 128 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h26359-((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*h26369
  have h26481 : (1)*v 46 + (-1)*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (-1)*h25957
  have h26483 : ((1)/(x^(2:ℕ)))*v 76 + (1)*v 128 + (((-1)*a)/(x))*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h26370-(((-1)*a)/(x))*h26481
  have h26507 : ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 128 + (((-1)*a + (-1)*x^(3:ℕ))/(x^(3:ℕ)))*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h26262-(-1)*h26481
  have h26628 : (1)*v 76 + (x^(2:ℕ))*v 128 + ((-1)*x*a)*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (x^(2:ℕ))*h26483
  have h26644 : (1 + (-1)*x^(2:ℕ))*v 128 + (1 + x*a)*v 158 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h26171-(1)*h26628
  exact ⟨h26507, h26644⟩

#print axioms positive_last_pair_reduced_rows_chunk12

}

end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

