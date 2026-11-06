module

public import AsymptoticCutEmbeddingLimitV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPositiveCoordinateWeight

open MeasureTheory Filter ContinuousLinearMap AsymptoticRegularTrace AsymptoticOrbitDiagonal
open AsymptoticCoordinateCut
open scoped lp Topology

variable {α : Type*}

def region (b : α → ℝ) (n : ℕ) : Set α := {x | b x≤(n+1:ℕ)}

theorem region_measurable [MeasurableSpace α] (b : α → ℝ) (hb : Measurable b) (n : ℕ) :
    MeasurableSet (region b n) := measurableSet_le hb measurable_const

theorem region_exhaust (b : α → ℝ) (x : α) : ∀ᶠ n in atTop,x∈region b n := by
  obtain ⟨n,hn⟩ := exists_nat_gt (b x)
  apply eventually_atTop.mpr
  refine ⟨n,?_⟩
  intro m hm
  change b x≤((m+1:ℕ):ℝ)
  have hnm : (n:ℝ)≤(m+1:ℕ) := by exact_mod_cast (show n≤m+1 by omega)
  exact hn.le.trans hnm

noncomputable def coefficient (b : α → ℝ) (n : ℕ) : α → ℂ :=
  (region b n).indicator (fun x => (b x:ℂ))

theorem coefficient_norm_le (b : α → ℝ) (hb : ∀ x,0<b x) (n : ℕ) (x : α) :
    ‖coefficient b n x‖≤(n+1:ℕ) := by
  classical
  by_cases hx : x∈region b n
  · rw [coefficient,Set.indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hb x)]
    exact hx
  · rw [coefficient,Set.indicator_of_notMem hx,norm_zero]
    positivity

theorem coefficient_measurable [MeasurableSpace α] (b : α → ℝ) (hb : Measurable b) (n : ℕ) :
    Measurable (coefficient b n) :=
  (Complex.measurable_ofReal.comp hb).indicator (region_measurable b hb n)

variable {G : Type*} [Group G] [MulAction G α]

noncomputable def multiplier (b : α → ℝ) (hb : ∀ x,0<b x) (n : ℕ) (x : α) :
    ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) :=
  operator (fun g => coefficient b n (g • x)) (Nat.cast_nonneg (n+1))
    (fun g => coefficient_norm_le b hb n (g • x))

theorem multiplier_norm_le (b : α → ℝ) (hb : ∀ x,0<b x) (n : ℕ) (x : α) :
    ‖multiplier (G:=G) b hb n x‖≤(n+1:ℕ) := operator_norm_le _ _ _

theorem multiplier_on_cut (b : α → ℝ) (hb : ∀ x,0<b x) (n : ℕ) (x : α)
    (U : Submodule ℂ ℓ²(G,ℂ)) (v : ℓ²(G,ℂ)) (hv : v∈cutSpace U (region b n) x) (g : G) :
    multiplier b hb n x v g=(b (g • x):ℂ)*v g := by
  classical
  change coefficient b n (g • x)*v g=_
  by_cases hg : g • x∈region b n
  · rw [coefficient,Set.indicator_of_mem hg]
  · have he := congrArg (fun w : ℓ²(G,ℂ) => w g) ((cutSpace_mem U (region b n) x v).mp hv).2
    rw [corner_apply,ite_eq_right hg] at he
    rw [coefficient,Set.indicator_of_notMem hg,← he,mul_zero,mul_zero]

theorem multiplier_injective_on_cut (b : α → ℝ) (hb : ∀ x,0<b x) (n : ℕ) (x : α)
    (U : Submodule ℂ ℓ²(G,ℂ)) (v : ℓ²(G,ℂ)) (hv : v∈cutSpace U (region b n) x)
    (hz : multiplier b hb n x v=0) : v=0 := by
  apply lp.ext
  funext g
  have he := congrArg (fun w : ℓ²(G,ℂ) => w g) hz
  rw [multiplier_on_cut b hb n x U v hv g] at he
  change (b (g • x):ℂ)*v g=0 at he
  exact (mul_eq_zero.mp he).resolve_left (Complex.ofReal_ne_zero.mpr (hb (g • x)).ne')

theorem multiplier_covariant (b : α → ℝ) (hb : ∀ x,0<b x) (n : ℕ) :
    Covariant (multiplier (G:=G) b hb n) := by
  intro x a g h
  simp only [multiplier,operator_matrix,mul_smul]
  by_cases hgh : g=h
  · simp [hgh]
  · have hga : g*a≠h*a := fun he => hgh (mul_right_cancel he)
    simp [hgh,hga]

theorem multiplier_matrix_measurable [MeasurableSpace α]
    (hact : ∀ g : G,Measurable (fun x : α => g • x))
    (b : α → ℝ) (hb : ∀ x,0<b x) (hm : Measurable b) (n : ℕ) (g h : G) :
    Measurable (fun x => matrix (multiplier b hb n x) g h) := by
  classical
  simp only [multiplier,operator_matrix]
  split_ifs
  · exact (coefficient_measurable b hm n).comp (hact g)
  · exact measurable_const

#print axioms region_measurable
#print axioms region_exhaust
#print axioms coefficient_norm_le
#print axioms coefficient_measurable
#print axioms multiplier_norm_le
#print axioms multiplier_on_cut
#print axioms multiplier_injective_on_cut
#print axioms multiplier_covariant
#print axioms multiplier_matrix_measurable

end AsymptoticPositiveCoordinateWeight
