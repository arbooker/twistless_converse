module

public import GridSelectedWindowsV1

set_option autoImplicit false

@[expose] public section

namespace QuantitativeArithmeticGoodLabelWindows

open GridPrimeParts GridAdmissibleGap GridRadius GridSelectedWindows
  GridLabelDetection SpanningActualKernel SpanningWindows

/-- A strict good-label inequality gives a positive ratio excess, with
no uniform admissible-level numerical gap assumed. -/
theorem good_ratio {N s : ℕ} (hN : 0 < N)
    (hgood : levelPart N s < s ^ 2) :
    0 < (s : ℝ) / Real.sqrt (levelPart N s) - 1 := by
  have hn : 0 < levelPart N s :=
    Nat.pos_of_ne_zero (part_ne_zero (Nat.ne_of_gt hN) _)
  have hp : (0 : ℝ) < Real.sqrt (levelPart N s) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hs : (levelPart N s : ℝ) < (s : ℝ) ^ 2 := by exact_mod_cast hgood
  have he := Real.sq_sqrt (Nat.cast_nonneg (levelPart N s))
  have hroot : Real.sqrt (levelPart N s) < (s : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ s from Nat.cast_nonneg s]
  exact sub_pos.mpr ((one_lt_div hp).mpr hroot)

/-- The grid scale may absorb an arbitrarily small positive ratio gap. -/
theorem exists_scale {gap : ℝ} (hgap : 0 < gap) (r : ℕ) :
    ∃ R : ℕ, 0 < R ∧ r ≤ R ∧ (r : ℝ) ≤ 4 * R * gap := by
  obtain ⟨R, hR⟩ := exists_nat_gt (max (r : ℝ) ((r : ℝ) / (4 * gap)) + 1)
  have hRr : (r : ℝ) < R := by linarith [le_max_left (r : ℝ) ((r : ℝ) / (4 * gap))]
  have hRgap : (r : ℝ) / (4 * gap) < R := by
    linarith [le_max_right (r : ℝ) ((r : ℝ) / (4 * gap))]
  refine ⟨R, ?_, ?_, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (Nat.cast_nonneg r) hRr)
  · exact_mod_cast hRr.le
  · have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * gap)).mp hRgap
    nlinarith

/-- A quarter-width radius surplus leaves an eighth-width right buffer. -/
theorem window_from_small_excess {rad centre v R : ℝ} {t u : ℤ}
    (hR : 0 < R) (hv : 16 * R ≤ v)
    (hcentre : v / R ≤ centre) (hrad : centre + v / (4 * R) ≤ rad)
    (ht : |(t : ℝ)| ≤ v / (8 * R)) (hu : (u : ℝ) = centre + (t : ℝ)) :
    Legal rad u ∧ v / (8 * R) - 1 ≤ rad - 1 - (u : ℝ) := by
  have hv0 : 0 < v := by nlinarith
  have ht1 := (le_abs_self (t : ℝ)).trans ht
  have ht2 : -(v / (8 * R)) ≤ (t : ℝ) := by
    have := neg_le_abs (t : ℝ)
    linarith
  have hrat : v / (4 * R) = 2 * (v / (8 * R)) := by ring
  have hrat' : v / R = 8 * (v / (8 * R)) := by ring
  have hpos : 2 ≤ v / (8 * R) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * R)).mpr
    nlinarith
  have hmargin : v / (8 * R) - 1 ≤ rad - 1 - (u : ℝ) := by rw [hu]; linarith
  have hu0 : 0 < (u : ℝ) := by rw [hu]; linarith
  refine ⟨⟨?_, ?_⟩, hmargin⟩ <;> linarith

/-- The selected good-label row is legal and buffered at any scale that
absorbs its actual ratio gap. Retained bad labels require a different row. -/
theorem selected_good_window {N G r R v w : ℕ} (hN : 0 < N)
    (hG : 0 < G) (hNG : N ∣ G) (a : Fin G)
    (hr : 0 < r) (hrG : Nat.Coprime r G) (hrR : r ≤ R)
    (hgap : (r : ℝ) ≤ 4 * R *
      ((labelOrder a : ℝ) / Real.sqrt (levelPart N (labelOrder a)) - 1))
    (hv : 16 * R ≤ v) (hvw : v = r * w) (t : ℤ)
    (ht : |(t : ℝ)| ≤ (v : ℝ) / (8 * R)) :
    let c := labelModulus a / labelOrder a
    let d := primePart G (fun p => ¬p ∣ labelOrder a)
    Legal (radius N (G * v) (d * r)) ((c * w : ℕ) + t) ∧
      (v : ℝ) / (8 * R) - 1 ≤
        radius N (G * v) (d * r) - 1 - (((c * w : ℕ) : ℤ) + t : ℤ) := by
  let m := labelModulus a
  let c := m / labelOrder a
  let d := primePart G (fun p => ¬p ∣ labelOrder a)
  let gap : ℝ := (labelOrder a : ℝ) / Real.sqrt (levelPart N (labelOrder a)) - 1
  have hc : 1 ≤ c := center_positive hG a
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hmc : m = c * labelOrder a := (Nat.div_mul_cancel (label_order_dvd_modulus hG a)).symm
  have hmc' : (m : ℝ) = (c : ℝ) * labelOrder a := by exact_mod_cast hmc
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrR' : (r : ℝ) ≤ R := by exact_mod_cast hrR
  have hR : (0 : ℝ) < R := hr'.trans_le hrR'
  have hv' : (16 : ℝ) * R ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hvw' : (v : ℝ) = (r : ℝ) * w := by exact_mod_cast hvw
  have hcentre : (v : ℝ) / R ≤ (c : ℝ) * w := by
    have hvr : (v : ℝ) / R ≤ (v : ℝ) / r :=
      div_le_div_of_nonneg_left hv0 hr' hrR'
    have he : (v : ℝ) / r = w := by rw [hvw', mul_div_cancel_left₀ _ hr'.ne']
    rw [he] at hvr
    nlinarith [show (0 : ℝ) ≤ w from Nat.cast_nonneg w]
  have hgap' : (r : ℝ) ≤ 4 * R * gap := hgap
  have hgap0 : 0 < gap := by nlinarith
  have hsmall : (v : ℝ) / (4 * R) ≤ gap * ((v : ℝ) / r) := by
    have hh : (1 : ℝ) / (4 * R) ≤ gap / r := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * R) hr').mpr
      nlinarith
    have hh' := mul_le_mul_of_nonneg_right hh hv0
    convert hh' using 1 <;> ring
  have hrad := grid_radius (s := labelOrder a) hN hG hr hNG hrG v
  change radius N (G * v) (d * r) =
    (m : ℝ) * v / ((r : ℝ) * Real.sqrt (levelPart N (labelOrder a))) at hrad
  have hid : radius N (G * v) (d * r) = (c : ℝ) * w + (c : ℝ) * gap * ((v : ℝ) / r) := by
    rw [hrad, hmc', hvw']
    dsimp [gap]
    field_simp
    ring
  have hex : (c : ℝ) * w + (v : ℝ) / (4 * R) ≤ radius N (G * v) (d * r) := by
    rw [hid]
    have hh := mul_nonneg hgap0.le (div_nonneg hv0 hr'.le)
    nlinarith
  apply window_from_small_excess hR hv' hcentre hex ht
  norm_cast

/-- A single natural scale accommodates every good label and an arbitrary
finite family of chosen center multipliers. -/
theorem exists_uniform_scale {N G : ℕ} (hN : 0 < N) (r : Fin G → ℕ) :
    ∃ R : ℕ, 0 < R ∧ (∀ a, r a ≤ R) ∧
      ∀ a, levelPart N (labelOrder a) < (labelOrder a) ^ 2 →
        (r a : ℝ) ≤ 4 * R *
          ((labelOrder a : ℝ) / Real.sqrt (levelPart N (labelOrder a)) - 1) := by
  classical
  have hlocal : ∀ a : Fin G, ∃ R : ℕ, 0 < R ∧ r a ≤ R ∧
      (levelPart N (labelOrder a) < (labelOrder a) ^ 2 →
        (r a : ℝ) ≤ 4 * R *
          ((labelOrder a : ℝ) / Real.sqrt (levelPart N (labelOrder a)) - 1)) := by
    intro a
    by_cases ha : levelPart N (labelOrder a) < (labelOrder a) ^ 2
    · obtain ⟨R, hR, hr, hg⟩ := exists_scale (good_ratio hN ha) (r a)
      exact ⟨R, hR, hr, fun _ => hg⟩
    · exact ⟨r a + 1, by omega, by omega, fun h => (ha h).elim⟩
  choose R _hR hr hg using hlocal
  let T := Finset.univ.sup R + 1
  have hRT (a : Fin G) : R a ≤ T :=
    (Finset.le_sup (f := R) (Finset.mem_univ a)).trans (Nat.le_succ _)
  refine ⟨T, by dsimp [T]; omega, fun a => (hr a).trans (hRT a), ?_⟩
  intro a ha
  have hgap := good_ratio hN ha
  have hRT' : (R a : ℝ) ≤ T := by exact_mod_cast hRT a
  have hga := hg a ha
  nlinarith

/-- The same selected row with the legacy buffer used by the grid
concentration and closure APIs. -/
theorem selected_good_window_compatible {N G r R v w : ℕ} (hN : 0 < N)
    (hG : 0 < G) (hNG : N ∣ G) (a : Fin G)
    (hr : 0 < r) (hrG : Nat.Coprime r G) (hrR : r ≤ R)
    (hgap : (r : ℝ) ≤ 4 * R *
      ((labelOrder a : ℝ) / Real.sqrt (levelPart N (labelOrder a)) - 1))
    (hv : 16 * R ≤ v) (hvw : v = r * w) (t : ℤ)
    (ht : |(t : ℝ)| ≤ (v : ℝ) / (8 * R)) :
    let c := labelModulus a / labelOrder a
    let d := primePart G (fun p => ¬p ∣ labelOrder a)
    Legal (radius N (G * v) (d * r)) ((c * w : ℕ) + t) ∧
      3 * (v : ℝ) / (40 * R) - 1 ≤
        radius N (G * v) (d * r) - 1 - (((c * w : ℕ) : ℤ) + t : ℤ) := by
  obtain ⟨hlegal, hbuffer⟩ := selected_good_window hN hG hNG a hr hrG hrR hgap hv hvw t ht
  refine ⟨hlegal, le_trans ?_ hbuffer⟩
  have hnonneg : (0 : ℝ) ≤ (v : ℝ) / (40 * R) := by positivity
  have hid : (v : ℝ) / (8 * R) = 5 * ((v : ℝ) / (40 * R)) := by ring
  have hid' : 3 * (v : ℝ) / (40 * R) = 3 * ((v : ℝ) / (40 * R)) := by ring
  linarith

#print axioms good_ratio
#print axioms exists_scale
#print axioms window_from_small_excess
#print axioms selected_good_window
#print axioms exists_uniform_scale
#print axioms selected_good_window_compatible

end QuantitativeArithmeticGoodLabelWindows
