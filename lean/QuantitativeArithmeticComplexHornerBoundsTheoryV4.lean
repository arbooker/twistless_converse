module

public import QuantitativeArithmeticPolynomialRootCoverTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticComplexHornerBounds. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticComplexHornerBoundsV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexHornerBounds
open Complex Polynomial

/-- Ascending-coefficient Horner evaluation on a finite interval. -/
def hornerValue (a : ℕ → ℂ) (z : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 0
  | n+1, j => a j+z*hornerValue a z n (j+1)

def hornerPolynomial (a : ℕ → ℂ) : ℕ → ℕ → ℂ[X]
  | 0, _ => 0
  | n+1, j => C (a j)+X*hornerPolynomial a n (j+1)

theorem eval_hornerPolynomial (a : ℕ → ℂ) (z : ℂ) (n j : ℕ) :
    (hornerPolynomial a n j).eval z=hornerValue a z n j := by
  induction n generalizing j with
  | zero => simp [hornerPolynomial,hornerValue]
  | succ n ih => simp [hornerPolynomial,hornerValue,ih]

/-- Local rounding-error certificates imply a bound on the complete evaluation.
The approximate states and error budgets may be rational; no exact expansion of
large powers of the evaluation point is needed. -/
theorem horner_error_bound (a : ℕ → ℂ) (z : ℂ)
    (v : ℕ → ℂ) (E : ℕ → ℝ) (n : ℕ) :
    ∀ j : ℕ,
      ‖v (j+n)‖ ≤ E (j+n) →
      (∀ t : ℕ, j≤t → t<j+n →
        ‖a t+z*v (t+1)-v t‖+‖z‖*E (t+1) ≤ E t) →
      ‖hornerValue a z n j-v j‖ ≤ E j := by
  induction n with
  | zero =>
    intro j hend _hstep
    simpa [hornerValue] using hend
  | succ n ih =>
    intro j hend hstep
    have hlast : j+1+n=j+(n+1) := by omega
    have hnext : ‖hornerValue a z n (j+1)-v (j+1)‖ ≤ E (j+1) :=
      ih (j+1) (by simpa only [hlast] using hend) (by
        intro t ht htn
        exact hstep t (by omega) (by omega))
    calc
      ‖hornerValue a z (n+1) j-v j‖ =
          ‖(a j+z*v (j+1)-v j)+z*(hornerValue a z n (j+1)-v (j+1))‖ := by
        congr 1
        simp only [hornerValue]
        ring
      _ ≤ ‖a j+z*v (j+1)-v j‖+‖z*(hornerValue a z n (j+1)-v (j+1))‖ := norm_add_le _ _
      _ = ‖a j+z*v (j+1)-v j‖+‖z‖*‖hornerValue a z n (j+1)-v (j+1)‖ := by rw [norm_mul]
      _ ≤ ‖a j+z*v (j+1)-v j‖+‖z‖*E (j+1) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hnext (norm_nonneg z))
      _ ≤ E j := hstep j (by omega) (by omega)

/-- Coordinate inequalities suffice to certify both the terminal state and each
local rounding residual, avoiding square-root evaluations in exact arithmetic. -/
theorem polynomial_bound_of_horner_certificates (a : ℕ → ℂ) (z : ℂ)
    (v : ℕ → ℂ) (E : ℕ → ℝ) (R B : ℝ) (n : ℕ)
    (hz : ‖z‖ ≤ R)
    (hE : ∀ j≤n, 0≤E j)
    (hend : |(v n).re|+|(v n).im| ≤ E n)
    (hstep : ∀ j<n,
      |(a j+z*v (j+1)-v j).re|+|(a j+z*v (j+1)-v j).im|+
        R*E (j+1) ≤ E j)
    (hfinal : |(v 0).re|+|(v 0).im|+E 0 ≤ B) :
    ‖(hornerPolynomial a n 0).eval z‖ ≤ B := by
  have herr : ‖hornerValue a z n 0-v 0‖ ≤ E 0 :=
    horner_error_bound a z v E n 0 (by
      simpa using (Complex.norm_le_abs_re_add_abs_im (v n)).trans hend) (by
      intro j _hj hjn
      have hj : j<n := by omega
      calc
        ‖a j+z*v (j+1)-v j‖+‖z‖*E (j+1) ≤
            |(a j+z*v (j+1)-v j).re|+|(a j+z*v (j+1)-v j).im|+
              R*E (j+1) := add_le_add (Complex.norm_le_abs_re_add_abs_im _)
                (mul_le_mul_of_nonneg_right hz (hE (j+1) (by omega)))
        _ ≤ E j := hstep j hj)
  rw [eval_hornerPolynomial]
  calc
    ‖hornerValue a z n 0‖ ≤ ‖v 0‖+‖hornerValue a z n 0-v 0‖ := by
      have h := norm_add_le (v 0) (hornerValue a z n 0-v 0)
      simpa only [add_sub_cancel] using h
    _ ≤ |(v 0).re|+|(v 0).im|+E 0 :=
      add_le_add (Complex.norm_le_abs_re_add_abs_im _) herr
    _ ≤ B := hfinal

#print axioms eval_hornerPolynomial
#print axioms horner_error_bound
#print axioms polynomial_bound_of_horner_certificates
end QuantitativeArithmeticComplexHornerBounds
end
end

/-! ## QuantitativeArithmeticComplexHornerDegreeV1 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexHornerBounds
open Polynomial

theorem monic_natDegree_horner (a : ℕ → ℂ) (n j : ℕ) (hlast : a (j+n)=1) :
    (hornerPolynomial a (n+1) j).Monic ∧
      (hornerPolynomial a (n+1) j).natDegree=n := by
  induction n generalizing j with
  | zero =>
    have h : a j=1 := by simpa using hlast
    simp [hornerPolynomial,h]
  | succ n ih =>
    have he : j+1+n=j+(n+1) := by omega
    have ht := ih (j+1) (by simpa only [he] using hlast)
    have hdegree : (X*hornerPolynomial a (n+1) (j+1)).natDegree=n+1 := by
      rw [natDegree_X_mul ht.1.ne_zero,ht.2]
    have hlt : (C (a j)).natDegree < (X*hornerPolynomial a (n+1) (j+1)).natDegree := by
      rw [natDegree_C,hdegree]
      omega
    change (C (a j)+X*hornerPolynomial a (n+1) (j+1)).Monic ∧
      (C (a j)+X*hornerPolynomial a (n+1) (j+1)).natDegree=n+1
    exact ⟨(monic_X.mul ht.1).add_of_right (degree_lt_degree hlt),
      (natDegree_add_eq_right_of_natDegree_lt hlt).trans hdegree⟩

#print axioms monic_natDegree_horner
end QuantitativeArithmeticComplexHornerBounds
end
end

/-! ## QuantitativeArithmeticComplexHornerLipschitzV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexHornerBounds
open Complex Polynomial

/-- Horner envelopes bound values and changes on a disk. The envelope values
can be integers, even when the polynomial coefficients have large denominators. -/
theorem horner_value_and_difference_bound (a : ℕ → ℂ) (z w : ℂ)
    (R : ℝ) (V D : ℕ → ℝ) (hz : ‖z‖≤R) (hw : ‖w‖≤R) (n : ℕ) :
    ∀ j : ℕ, 0≤V (j+n) → 0≤D (j+n) →
      (∀ t : ℕ, j≤t → t<j+n → ‖a t‖+R*V (t+1)≤V t) →
      (∀ t : ℕ, j≤t → t<j+n → V (t+1)+R*D (t+1)≤D t) →
      ‖hornerValue a w n j‖≤V j ∧
        ‖hornerValue a z n j-hornerValue a w n j‖≤‖z-w‖*D j := by
  have hR : 0≤R := (norm_nonneg z).trans hz
  induction n with
  | zero =>
    intro j hv hd _ _
    constructor
    · simpa [hornerValue] using hv
    · simpa [hornerValue] using mul_nonneg (norm_nonneg (z-w)) hd
  | succ n ih =>
    intro j hv hd hV hD
    have hlast : j+1+n=j+(n+1) := by omega
    have hn := ih (j+1) (by simpa only [hlast] using hv)
      (by simpa only [hlast] using hd)
      (fun t ht htn => hV t (by omega) (by omega))
      (fun t ht htn => hD t (by omega) (by omega))
    constructor
    · calc
        ‖hornerValue a w (n+1) j‖ ≤ ‖a j‖+‖w*hornerValue a w n (j+1)‖ :=
          norm_add_le _ _
        _ = ‖a j‖+‖w‖*‖hornerValue a w n (j+1)‖ := by rw [norm_mul]
        _ ≤ ‖a j‖+R*V (j+1) :=
          add_le_add (le_refl _) (mul_le_mul hw hn.1 (norm_nonneg _) hR)
        _ ≤ V j := hV j (by omega) (by omega)
    · calc
        ‖hornerValue a z (n+1) j-hornerValue a w (n+1) j‖ =
            ‖(z-w)*hornerValue a w n (j+1)+
              z*(hornerValue a z n (j+1)-hornerValue a w n (j+1))‖ := by
          congr 1
          simp only [hornerValue]
          ring
        _ ≤ ‖(z-w)*hornerValue a w n (j+1)‖+
              ‖z*(hornerValue a z n (j+1)-hornerValue a w n (j+1))‖ := norm_add_le _ _
        _ = ‖z-w‖*‖hornerValue a w n (j+1)‖+
              ‖z‖*‖hornerValue a z n (j+1)-hornerValue a w n (j+1)‖ := by
          rw [norm_mul,norm_mul]
        _ ≤ ‖z-w‖*V (j+1)+R*(‖z-w‖*D (j+1)) :=
          add_le_add (mul_le_mul_of_nonneg_left hn.1 (norm_nonneg _))
            (mul_le_mul hz hn.2 (norm_nonneg _) hR)
        _ = ‖z-w‖*(V (j+1)+R*D (j+1)) := by ring
        _ ≤ ‖z-w‖*D j :=
          mul_le_mul_of_nonneg_left (hD j (by omega) (by omega)) (norm_nonneg _)

/-- Squared modulus bounds need only a value approximation and an error radius. -/
theorem squared_norm_error_bound (z w : ℂ) (δ B : ℝ)
    (hδ : 0≤δ) (hd : ‖z-w‖≤δ) (hw : ‖w‖≤B) :
    |‖z‖^2-‖w‖^2| ≤ δ*(2*B+δ) := by
  have hz : ‖z‖≤δ+B := by
    have h := norm_add_le (z-w) w
    simp only [sub_add_cancel] at h
    linarith
  calc
    |‖z‖^2-‖w‖^2| = |‖z‖-‖w‖| *(‖z‖+‖w‖) := by
      rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    _ ≤ δ*(2*B+δ) :=
      mul_le_mul ((abs_norm_sub_norm_le z w).trans hd) (by linarith)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) hδ

#print axioms horner_value_and_difference_bound
#print axioms squared_norm_error_bound
end QuantitativeArithmeticComplexHornerBounds
end
end

/-! ## QuantitativeArithmeticRationalHornerCertificatesV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexHornerBounds
open Complex Polynomial

def ratComplex (z : ℚ × ℚ) : ℂ := (z.1:ℂ)+(z.2:ℂ)*I

@[simp] theorem ratComplex_re (z : ℚ × ℚ) : (ratComplex z).re=(z.1:ℝ) := by
  simp [ratComplex]
@[simp] theorem ratComplex_im (z : ℚ × ℚ) : (ratComplex z).im=(z.2:ℝ) := by
  simp [ratComplex]

def ratResidual (a : ℚ) (z u v : ℚ × ℚ) : ℚ × ℚ :=
  (a+z.1*u.1-z.2*u.2-v.1,z.1*u.2+z.2*u.1-v.2)

theorem ratResidual_cast (a : ℚ) (z u v : ℚ × ℚ) :
    ratComplex (ratResidual a z u v)=(a:ℂ)+ratComplex z*ratComplex u-ratComplex v := by
  apply Complex.ext <;>
    simp [ratComplex,ratResidual,Complex.mul_re,Complex.mul_im]
  ring

/-- Entirely rational local inequalities certify a complex polynomial value.
The finite inequalities can be discharged by the Lean kernel independently of
this analytic wrapper. -/
theorem polynomial_bound_of_rational_certificate
    (a : ℕ → ℚ) (z : ℚ × ℚ) (v : ℕ → ℚ × ℚ) (E : ℕ → ℚ)
    (R B : ℚ) (n : ℕ)
    (hz : |z.1|+|z.2|≤R)
    (hE : ∀ j≤n, 0≤E j)
    (hend : |(v n).1|+|(v n).2|≤E n)
    (hstep : ∀ j<n,
      |(ratResidual (a j) z (v (j+1)) (v j)).1|+
        |(ratResidual (a j) z (v (j+1)) (v j)).2|+R*E (j+1)≤E j)
    (hfinal : |(v 0).1|+|(v 0).2|+E 0≤B) :
    ‖(hornerPolynomial (fun j => (a j:ℂ)) n 0).eval (ratComplex z)‖≤(B:ℝ) := by
  apply polynomial_bound_of_horner_certificates (fun j => (a j:ℂ)) (ratComplex z)
    (fun j => ratComplex (v j)) (fun j => (E j:ℝ)) (R:ℝ) (B:ℝ) n
  · have h : |(z.1:ℝ)|+|(z.2:ℝ)|≤(R:ℝ) := by exact_mod_cast hz
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using h)
  · intro j hj
    exact_mod_cast hE j hj
  · have h : |((v n).1:ℝ)|+|((v n).2:ℝ)|≤(E n:ℝ) := by exact_mod_cast hend
    simpa using h
  · intro j hj
    have h : |((ratResidual (a j) z (v (j+1)) (v j)).1:ℝ)|+
        |((ratResidual (a j) z (v (j+1)) (v j)).2:ℝ)|+
          (R:ℝ)*(E (j+1):ℝ)≤(E j:ℝ) := by exact_mod_cast hstep j hj
    simpa only [← ratResidual_cast,ratComplex_re,ratComplex_im] using h
  · have h : |((v 0).1:ℝ)|+|((v 0).2:ℝ)|+(E 0:ℝ)≤(B:ℝ) := by exact_mod_cast hfinal
    simpa using h

#print axioms ratResidual_cast
#print axioms polynomial_bound_of_rational_certificate
end QuantitativeArithmeticComplexHornerBounds
end
end

/-! ## QuantitativeArithmeticRationalHornerErrorV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexHornerBounds
open Complex Polynomial

theorem polynomial_error_of_rational_certificate
    (a : ℕ → ℚ) (z : ℚ × ℚ) (v : ℕ → ℚ × ℚ) (E : ℕ → ℚ)
    (R : ℚ) (n : ℕ)
    (hz : |z.1|+|z.2|≤R)
    (hE : ∀ j≤n, 0≤E j)
    (hend : |(v n).1|+|(v n).2|≤E n)
    (hstep : ∀ j<n,
      |(ratResidual (a j) z (v (j+1)) (v j)).1|+
        |(ratResidual (a j) z (v (j+1)) (v j)).2|+R*E (j+1)≤E j) :
    ‖(hornerPolynomial (fun j => (a j:ℂ)) n 0).eval (ratComplex z)-ratComplex (v 0)‖≤(E 0:ℝ) := by
  have hz' : ‖ratComplex z‖≤(R:ℝ) := by
    have h : |(z.1:ℝ)|+|(z.2:ℝ)|≤(R:ℝ) := by exact_mod_cast hz
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using h)
  rw [eval_hornerPolynomial]
  apply horner_error_bound (fun j => (a j:ℂ)) (ratComplex z)
    (fun j => ratComplex (v j)) (fun j => (E j:ℝ)) n 0
  · have h : |((v n).1:ℝ)|+|((v n).2:ℝ)|≤(E n:ℝ) := by exact_mod_cast hend
    simpa using (Complex.norm_le_abs_re_add_abs_im (ratComplex (v n))).trans (by simpa using h)
  · intro j _hj hjn
    have hj : j<n := by omega
    have he : (0:ℝ)≤(E (j+1):ℝ) := by exact_mod_cast hE (j+1) (by omega)
    have h : |((ratResidual (a j) z (v (j+1)) (v j)).1:ℝ)|+
        |((ratResidual (a j) z (v (j+1)) (v j)).2:ℝ)|+
          (R:ℝ)*(E (j+1):ℝ)≤(E j:ℝ) := by exact_mod_cast hstep j hj
    have hnorm := Complex.norm_le_abs_re_add_abs_im (ratComplex (ratResidual (a j) z (v (j+1)) (v j)))
    have hsum := add_le_add hnorm (mul_le_mul_of_nonneg_right hz' he)
    exact (by simpa only [ratResidual_cast] using hsum.trans (by simpa using h))
#print axioms polynomial_error_of_rational_certificate
end QuantitativeArithmeticComplexHornerBounds
end
end

/-! ## QuantitativeArithmeticRationalHornerDiskV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexHornerBounds
open Complex Polynomial

theorem polynomial_difference_of_rational_envelope
    (a : ℕ → ℚ) (z w : ℂ) (R : ℚ) (V D : ℕ → ℚ) (n : ℕ)
    (hz : ‖z‖≤(R:ℝ)) (hw : ‖w‖≤(R:ℝ))
    (hVend : 0≤V n) (hDend : 0≤D n)
    (hV : ∀ j<n, |a j|+R*V (j+1)≤V j)
    (hD : ∀ j<n, V (j+1)+R*D (j+1)≤D j) :
    ‖(hornerPolynomial (fun j => (a j:ℂ)) n 0).eval z-
      (hornerPolynomial (fun j => (a j:ℂ)) n 0).eval w‖≤‖z-w‖*(D 0:ℝ) := by
  simp only [eval_hornerPolynomial]
  have h := horner_value_and_difference_bound (fun j => (a j:ℂ)) z w (R:ℝ)
    (fun j => (V j:ℝ)) (fun j => (D j:ℝ)) hz hw n 0
    (by simpa only [Nat.zero_add] using (show (0:ℝ)≤(V n:ℝ) by exact_mod_cast hVend)) (by simpa only [Nat.zero_add] using (show (0:ℝ)≤(D n:ℝ) by exact_mod_cast hDend)) (by
      intro j _hj hjn
      have hj : j<n := by omega
      have hc : ‖(a j:ℂ)‖=|(a j:ℝ)| := by simp
      rw [hc]
      exact_mod_cast hV j hj) (by
      intro j _hj hjn
      have hj : j<n := by omega
      exact_mod_cast hD j hj)
  exact h.2

theorem polynomial_disk_error
    (P : ℂ[X]) (z w u : ℂ) (r D E : ℝ)
    (hD : 0≤D) (hd : ‖z-w‖≤r)
    (hlip : ‖P.eval z-P.eval w‖≤‖z-w‖*D)
    (herr : ‖P.eval w-u‖≤E) : ‖P.eval z-u‖≤r*D+E := by
  calc
    ‖P.eval z-u‖≤‖P.eval z-P.eval w‖+‖P.eval w-u‖ := by
      have h := norm_add_le (P.eval z-P.eval w) (P.eval w-u)
      simpa only [sub_add_sub_cancel] using h
    _≤‖z-w‖*D+E := add_le_add hlip herr
    _≤r*D+E := add_le_add (mul_le_mul_of_nonneg_right hd hD) (le_refl E)
#print axioms polynomial_difference_of_rational_envelope
#print axioms polynomial_disk_error
end QuantitativeArithmeticComplexHornerBounds
end
end

/-! ## QuantitativeArithmeticRationalSquaredNormV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticComplexHornerBounds
open Complex

theorem ratComplex_norm_sq (w : ℚ × ℚ) :
    ‖ratComplex w‖^2=((w.1^2+w.2^2:ℚ):ℝ) := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [pow_two]

theorem squared_norm_enclosure_of_rational_error
    (z : ℂ) (w : ℚ × ℚ) (δ lo hi : ℚ)
    (hδ : 0≤δ) (he : ‖z-ratComplex w‖≤(δ:ℝ))
    (hlo : lo≤w.1^2+w.2^2-δ*(2*(|w.1|+|w.2|)+δ))
    (hhi : w.1^2+w.2^2+δ*(2*(|w.1|+|w.2|)+δ)≤hi) :
    (lo:ℝ)≤‖z‖^2 ∧ ‖z‖^2≤(hi:ℝ) := by
  have hB : ‖ratComplex w‖≤((|w.1|+|w.2|:ℚ):ℝ) := by
    simpa using Complex.norm_le_abs_re_add_abs_im (ratComplex w)
  have hh := squared_norm_error_bound z (ratComplex w) (δ:ℝ)
    ((|w.1|+|w.2|:ℚ):ℝ) (by exact_mod_cast hδ) he hB
  rw [ratComplex_norm_sq] at hh
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  have hlo' : (lo:ℝ)≤((w.1^2+w.2^2:ℚ):ℝ)-(δ:ℝ)*(2*((|w.1|+|w.2|:ℚ):ℝ)+(δ:ℝ)) := by exact_mod_cast hlo
  have hhi' : ((w.1^2+w.2^2:ℚ):ℝ)+(δ:ℝ)*(2*((|w.1|+|w.2|:ℚ):ℝ)+(δ:ℝ))≤(hi:ℝ) := by exact_mod_cast hhi
  constructor <;> linarith
#print axioms squared_norm_enclosure_of_rational_error
end QuantitativeArithmeticComplexHornerBounds
end
end
