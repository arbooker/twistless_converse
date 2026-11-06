module

public import QuantitativeHolomorphicCompactRowBoundsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open UpperHalfPlane AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticRegularObservationRows

theorem integerAction_of_scaled_rational_entries (g : GL (Fin 2) ℚ)
    (hg : 0<(realMatrix g).det.val) (M : IntegerMatrix2) (hdet : M.det≠0)
    (d : ℚ) (hd : d≠0) (hentries : ∀ i j, (M i j:ℚ)=d*g i j) :
    IntegerAction (ofMatrix g hg) M := by
  refine ⟨hdet,?_⟩
  have hr (i j : Fin 2) : (M i j:ℝ)=(d:ℝ)*(g i j:ℝ) := by exact_mod_cast hentries i j
  have hc (i j : Fin 2) : (M i j:ℂ)=(d:ℂ)*((g i j:ℝ):ℂ) := by exact_mod_cast hr i j
  intro z
  rw [ofMatrix_action, coe_smul_of_det_pos hg]
  change (((g 0 0:ℝ):ℂ)*(z:ℂ)+((g 0 1:ℝ):ℂ))/
    (((g 1 0:ℝ):ℂ)*(z:ℂ)+((g 1 1:ℝ):ℂ)) = _
  rw [hc,hc,hc,hc]
  have hd' : (d:ℂ)≠0 := by exact_mod_cast hd
  simp only [mul_assoc, ←mul_add, mul_div_mul_left _ _ hd']

def translationIntegerMatrix (q a : ℕ) : IntegerMatrix2 := !![(q:ℤ),a;0,q]
def reflectedIntegerMatrix (N q a : ℕ) : IntegerMatrix2 :=
  let L : ℤ := Nat.lcm N (q^2)
  !![(a:ℤ)*L,-(q:ℤ);(q:ℤ)*L,0]
def ramifiedIntegerMatrix (p a : ℕ) : IntegerMatrix2 := !![1,(a:ℤ);0,(p:ℤ)]

theorem translation_integer_action (q a : ℕ) (hq : 0<q) :
    IntegerAction (ofMatrix (translation ((a:ℚ)/q)).matrix (translation ((a:ℚ)/q)).positive)
      (translationIntegerMatrix q a) := by
  refine integerAction_of_scaled_rational_entries _ _ _ ?_ (q:ℚ) (by exact_mod_cast hq.ne') ?_
  · simp [translationIntegerMatrix, Matrix.det_fin_two, hq.ne']
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [translationIntegerMatrix, translation, AsymptoticMobiusFold.translation,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, hq.ne', mul_div_cancel₀]

theorem reflected_integer_action (N q a : ℕ) (hN : 0<N) (hq : 0<q) :
    IntegerAction (ofMatrix (reflected N q hN hq a).matrix (reflected N q hN hq a).positive)
      (reflectedIntegerMatrix N q a) := by
  have hL : Nat.lcm N (q^2)≠0 := (Nat.lcm_pos hN (pow_pos hq 2)).ne'
  refine integerAction_of_scaled_rational_entries _ _ _ ?_ (q:ℚ) (by exact_mod_cast hq.ne') ?_
  · simp [reflectedIntegerMatrix, Matrix.det_fin_two, hq.ne', hL]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectedIntegerMatrix, reflected, AsymptoticReconstructionBranch.branch,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]
    all_goals field_simp

theorem ramified_integer_action (p a : ℕ) (hp : 0<p) :
    IntegerAction (ofMatrix (ramified p hp a).matrix (ramified p hp a).positive)
      (ramifiedIntegerMatrix p a) := by
  refine integerAction_of_scaled_rational_entries _ _ _ ?_ 1 one_ne_zero ?_
  · simp [ramifiedIntegerMatrix, Matrix.det_fin_two, hp.ne']
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [ramifiedIntegerMatrix, ramified, AsymptoticRamifiedBranch.branch,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem translation_integer_bound (q a : ℕ) (ha : a≤q) :
    MatrixEntryBound (translationIntegerMatrix q a) q := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [translationIntegerMatrix, Nat.cast_le.mpr ha]

/-- Actual twist-row integer heights grow at most cubically in q, with
an explicit level factor. No choice of rational representatives remains. -/
theorem reflected_integer_bound (N q a : ℕ) (hN : 0<N) (hq : 0<q) (ha : a≤q) :
    MatrixEntryBound (reflectedIntegerMatrix N q a) (N*q^3:ℕ) := by
  have hL : Nat.lcm N (q^2)≤N*q^2 := Nat.lcm_le_mul hN (pow_pos hq 2)
  have hqB : q≤N*q^3 := by
    have hN1 : 1≤N := hN
    have hq1 : 1≤q := hq
    nlinarith [Nat.pow_le_pow_right hq1 (show 1≤3 by omega)]
  have hqL : q*Nat.lcm N (q^2)≤N*q^3 := by
    calc
      _ ≤ q*(N*q^2) := Nat.mul_le_mul_left q hL
      _ = _ := by ring
  have haL := (Nat.mul_le_mul_right (Nat.lcm N (q^2)) ha).trans hqL
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [reflectedIntegerMatrix, Nat.cast_mul] using (Nat.cast_le.mpr haL : (a*Nat.lcm N (q^2):ℕ)≤((N*q^3:ℕ):ℝ))
  · simpa [reflectedIntegerMatrix] using (Nat.cast_le.mpr hqB : (q:ℝ)≤(N*q^3:ℕ))
  · simpa [reflectedIntegerMatrix, Nat.cast_mul] using (Nat.cast_le.mpr hqL : (q*Nat.lcm N (q^2):ℕ)≤((N*q^3:ℕ):ℝ))
  · simp [reflectedIntegerMatrix]
    positivity

theorem ramified_integer_bound (p a : ℕ) (hp : 0<p) (ha : a≤p) :
    MatrixEntryBound (ramifiedIntegerMatrix p a) p := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedIntegerMatrix, Nat.cast_le.mpr ha, Nat.one_le_cast.mpr hp]

#print axioms translation_integer_action
#print axioms reflected_integer_action
#print axioms ramified_integer_action
#print axioms reflected_integer_bound

end QuantitativeHolomorphic
