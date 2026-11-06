module

public import AsymptoticMobiusFoldV1
public import AsymptoticWeightedBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public section

namespace AsymptoticCompactBranch

open MeasureTheory UpperHalfPlane Set Filter ContinuousLinearMap
open AsymptoticHyperbolicSlash AsymptoticMobiusFold

noncomputable def cap (ε : ℝ) (t : ℕ) (z : ℍ) : ℝ := (min (z.im/ε) 1)^t

theorem cap_pos {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) : 0<cap ε t z :=
  pow_pos (lt_min (div_pos z.im_pos hε) zero_lt_one) t

theorem cap_continuous (ε : ℝ) (t : ℕ) : Continuous (cap ε t) := by
  unfold cap
  fun_prop

noncomputable def ratio (g : GL (Fin 2) ℝ) (ε : ℝ) (t : ℕ) (z : ℍ) : ℝ :=
  cap ε t z/cap ε t (g • z)

theorem ratio_pos (g : GL (Fin 2) ℝ) {ε : ℝ} (hε : 0<ε) (t : ℕ) (z : ℍ) :
    0<ratio g ε t z := div_pos (cap_pos hε t z) (cap_pos hε t (g • z))

theorem ratio_continuous (g : GL (Fin 2) ℝ) {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    Continuous (ratio g ε t) :=
  (cap_continuous ε t).div₀ ((cap_continuous ε t).comp (continuous_const_smul g))
    (fun z => (cap_pos hε t (g • z)).ne')

/-- Finite folding and a bounded capped-weight ratio on an actual compact
observation region. Both bounds are independent of holomorphic weight. -/
structure Data (g : GL (Fin 2) ℝ) (s : Set ℍ) (ε : ℝ) (t : ℕ) where
  folds : Finset ℤ
  fold_mem : ∀ z∈s,Int.floor (g • z).re∈folds
  bound : ℝ
  bound_nonneg : 0≤bound
  ratio_le : ∀ z∈s,ratio g ε t z≤bound

theorem data_exists (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : Nonempty (Data g s ε t) := by
  obtain ⟨I,hI⟩ := compact_folds g hs
  obtain ⟨C,hC⟩ := hs.bddAbove_image (ratio_continuous g hε t).continuousOn
  exact ⟨⟨I,hI,max C 0,le_max_right _ _,fun z hz =>
    (hC (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩⟩

noncomputable def data (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : Data g s ε t := Classical.choice (data_exists g hs hε t)

noncomputable def coefficient (g : GL (Fin 2) ℝ) (s : Set ℍ) (ε : ℝ) (t : ℕ) : ℍ → ℂ :=
  s.indicator (fun z => (ratio g ε t z:ℂ))

theorem coefficient_measurable (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) : Measurable (coefficient g s ε t) :=
  (Complex.continuous_ofReal.comp (ratio_continuous g hε t)).measurable.indicator hs

theorem coefficient_norm_le (g : GL (Fin 2) ℝ) {s : Set ℍ} {ε : ℝ} (hε : 0<ε)
    (t : ℕ) (D : Data g s ε t) (z : ℍ) : ‖coefficient g s ε t z‖≤D.bound := by
  classical
  by_cases hz : z∈s
  · rw [coefficient,Set.indicator_of_mem hz,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (ratio_pos g hε t z)]
    exact D.ratio_le z hz
  · rw [coefficient,Set.indicator_of_notMem hz,norm_zero]
    exact D.bound_nonneg

noncomputable def term (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ) (n : ℤ) : Space →L[ℂ] Space :=
  (AsymptoticL2Multiplier.operator (coefficient g s ε t)
    (coefficient_measurable g hs hε t).aestronglyMeasurable
    (Filter.Eventually.of_forall (coefficient_norm_le g hε t D))).comp
      (AsymptoticHyperbolicSlash.operator (fold g n) (2*m))

theorem term_norm_le (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ) (n : ℤ) :
    ‖term g hs hε t D m n‖≤D.bound := by
  apply (opNorm_comp_le _ _).trans
  have hc := AsymptoticL2Multiplier.operator_norm_le (μ:=volume) (coefficient g s ε t)
    (coefficient_measurable g hs hε t).aestronglyMeasurable D.bound_nonneg
    (Filter.Eventually.of_forall (coefficient_norm_le g hε t D))
  have hp := AsymptoticHyperbolicSlash.operator_norm_le (fold g n) (2*m)
  simpa only [mul_one] using mul_le_mul hc hp (norm_nonneg _) D.bound_nonneg

theorem term_coeFn (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ) (n : ℤ) (u : Space) :
    term g hs hε t D m n u =ᵐ[volume] (fun z =>
      coefficient g s ε t z*phase (fold g n) (2*m) z*u (fold g n • z)) := by
  filter_upwards [AsymptoticL2Multiplier.operator_coeFn (coefficient g s ε t)
    (coefficient_measurable g hs hε t).aestronglyMeasurable
    (Filter.Eventually.of_forall (coefficient_norm_le g hε t D))
    (AsymptoticHyperbolicSlash.operator (fold g n) (2*m) u),
    AsymptoticHyperbolicSlash.operator_coeFn (fold g n) (2*m) u] with z hc hp
  exact hc.trans (by rw [hp]; ring)

noncomputable def operator (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ) : Space →L[ℂ] Space :=
  ∑ n∈D.folds,term g hs hε t D m n

theorem operator_norm_le (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ) :
    ‖operator g hs hε t D m‖≤D.folds.card*D.bound := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => term_norm_le g hs hε t D m n)).trans_eq
  simp

theorem operator_coeFn (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ) (u : Space) :
    operator g hs hε t D m u =ᵐ[volume] (fun z =>
      ∑ n∈D.folds,coefficient g s ε t z*phase (fold g n) (2*m) z*u (fold g n • z)) := by
  rw [operator,_root_.sum_apply]
  apply (Lp.coeFn_fun_finsetSum _ _).trans
  have hh := ae_all_iff.mpr (fun n => term_coeFn g hs hε t D m n u)
  filter_upwards [hh] with z hz
  exact Finset.sum_congr rfl (fun n _ => hz n)

#print axioms data_exists
#print axioms operator_norm_le
#print axioms operator_coeFn

end AsymptoticCompactBranch
