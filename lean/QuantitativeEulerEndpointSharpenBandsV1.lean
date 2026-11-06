module

public import QuantitativeEulerEndpointSharpenScalarV1
public import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial MeasureTheory
open scoped unitInterval

def bandCenter (J : ℕ) (j : Fin J) : ℝ := 1-2/(J:ℝ)+((j:ℝ)+1/2)/(J:ℝ)^2
def bandWidth (J : ℕ) : ℝ := (1/4)/(J:ℝ)^2

theorem bandWidth_pos {J : ℕ} (hJ : 0<J) : 0<bandWidth J := by
  unfold bandWidth
  have : 0<(J:ℝ) := by exact_mod_cast hJ
  positivity

theorem bandCenter_lower {J : ℕ} (hJ : 0<J) (j : Fin J) :
    1-2*(1/(J:ℝ))≤bandCenter J j := by
  have : 0<(J:ℝ) := by exact_mod_cast hJ
  have hj : 0≤(j:ℝ) := Nat.cast_nonneg j.val
  unfold bandCenter
  rw [show 2/(J:ℝ)=2*(1/(J:ℝ)) by ring]
  have hn : 0≤((j:ℝ)+1/2)/(J:ℝ)^2 := by positivity
  linarith

theorem bandCenter_upper {J : ℕ} (hJ : 0<J) (j : Fin J) : bandCenter J j≤1 := by
  have hJR : 0<(J:ℝ) := by exact_mod_cast hJ
  have hj : (j:ℝ)+1≤(J:ℝ) := by exact_mod_cast j.is_lt
  have he : ((j:ℝ)+1/2)/(J:ℝ)^2 ≤ 1/(J:ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hJR)).mpr
    have hc : (1/(J:ℝ))*(J:ℝ)^2=(J:ℝ) := by field_simp
    rw [hc]
    linarith
  unfold bandCenter
  rw [show 2/(J:ℝ)=2*(1/(J:ℝ)) by ring]
  have hpos : 0≤1/(J:ℝ) := by positivity
  linarith

theorem bands_separated {J : ℕ} (hJ : 0<J) (i j : Fin J) (hij : i<j) :
    bandCenter J i+bandWidth J < bandCenter J j-bandWidth J := by
  have hJR : 0<(J:ℝ) := by exact_mod_cast hJ
  have hijR : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast hij
  calc
    bandCenter J i+bandWidth J = 1-2/(J:ℝ)+((i:ℝ)+3/4)/(J:ℝ)^2 := by
      unfold bandCenter bandWidth
      ring
    _ < 1-2/(J:ℝ)+((j:ℝ)+1/4)/(J:ℝ)^2 := by
      apply add_lt_add_right
      apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hJR)).mpr
      linarith
    _ = bandCenter J j-bandWidth J := by unfold bandCenter bandWidth; ring

/-- One of the J explicitly disjoint transition bands has mass at most T/J. -/
theorem exists_light_band {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsFiniteMeasure μ] (f : β → ℝ) (hf : Measurable f)
    {J : ℕ} (hJ : 0<J) :
    ∃ j : Fin J, μ.real {x | f x∈Set.Icc (bandCenter J j-bandWidth J) (bandCenter J j+bandWidth J)} ≤
      μ.real Set.univ/(J:ℝ) := by
  let E := fun j : Fin J => {x | f x∈Set.Icc (bandCenter J j-bandWidth J) (bandCenter J j+bandWidth J)}
  have hm (j : Fin J) : MeasurableSet (E j) := hf isClosed_Icc.measurableSet
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin J))) E := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change _≤f x ∧ f x≤_ at hxi hxj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := bands_separated hJ i j hlt
      linarith [hxi.2,hxj.1]
    · have h := bands_separated hJ j i hgt
      linarith [hxj.2,hxi.1]
  have hsum := sum_measureReal_le_measureReal_univ (μ := μ) (fun j _ => hm j) hd
  have hJR : 0<(J:ℝ) := by exact_mod_cast hJ
  by_contra h
  push Not at h
  have hstrict : (∑ _j : Fin J, μ.real Set.univ/(J:ℝ)) < ∑ j : Fin J, μ.real (E j) := by
    apply Finset.sum_lt_sum (fun j _ => (h j).le)
    exact ⟨⟨0,hJ⟩,Finset.mem_univ _,h ⟨0,hJ⟩⟩
  have he : (∑ _j : Fin J, μ.real Set.univ/(J:ℝ))=μ.real Set.univ := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [he] at hstrict
  exact (not_lt_of_ge hsum) hstrict

/-- Monotone sharpening at polynomial degree: for EVERY finite spectral
measure there is an explicit Bernstein-tail polynomial of degree at most
16 J^5+1, with integral idempotency defect at most 4T/J. -/
theorem exists_polynomial_sharpening {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsFiniteMeasure μ] (f : β → I)
    (hf : Measurable (fun x => (f x : ℝ))) {J : ℕ} (hJ : 0<J) :
    ∃ p : ℝ[X], p.natDegree≤16*J^5+1 ∧ p.eval 0=0 ∧ p.eval 1=1 ∧
      (∀ x : I, 0≤p.eval (x:ℝ) ∧ p.eval (x:ℝ)≤(x:ℝ)) ∧
      (∫ x, p.eval (f x : ℝ)-(p.eval (f x : ℝ))^2 ∂μ)≤4*μ.real Set.univ/(J:ℝ) := by
  obtain ⟨j,hj⟩ := exists_light_band μ (fun x => (f x : ℝ)) hf hJ
  let n := 16*J^5
  have hn : 0<n := by dsimp [n]; positivity
  have hJR : 0<(J:ℝ) := by exact_mod_cast hJ
  refine ⟨sharpen n (bandCenter J j),sharpen_natDegree_le _ _,sharpen_zero _ _,
    sharpen_one (Nat.ne_of_gt hn) (bandCenter_upper hJ j),sharpen_bounds _ _,?_⟩
  have he : 1/((n:ℝ)*(bandWidth J)^2)=1/(J:ℝ) := by
    dsimp [n,bandWidth]
    push_cast
    field_simp
    ring
  have hh := sharpen_defect_integral μ f hf hn (by positivity : 0≤1/(J:ℝ))
    (bandWidth_pos hJ) (bandCenter_lower hJ j)
  rw [he] at hh
  calc
    _ ≤ (2*(1/(J:ℝ))+1/(J:ℝ))*μ.real Set.univ+
        μ.real {x | (f x : ℝ)∈Set.Icc (bandCenter J j-bandWidth J) (bandCenter J j+bandWidth J)} := hh
    _ ≤ (2*(1/(J:ℝ))+1/(J:ℝ))*μ.real Set.univ+μ.real Set.univ/(J:ℝ) := add_le_add le_rfl hj
    _ = 4*μ.real Set.univ/(J:ℝ) := by ring

#print axioms bands_separated
#print axioms exists_light_band
#print axioms exists_polynomial_sharpening
end QuantitativeEulerEndpointBernstein
