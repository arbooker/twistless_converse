module

public import AsymptoticRegularFoldedLowV1
public import AsymptoticFoldedTerminalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularFoldedTerminal

open MeasureTheory UpperHalfPlane Set ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticRegularFoldedLow (Space)

variable {L : ℚ} (hL : 0<L) (b d : ℚ)

noncomputable def term (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (n : ℤ) (z : ℍ) :
    Space →L[ℂ] Space :=
  AsymptoticOrbitBranch.operator (AsymptoticRationalBranches.fold hL b d n)
    (AsymptoticFoldedTerminal.coefficient (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) s r ε t n)
    (AsymptoticFoldMajorant.majorant_nonneg zero_le_one (by positivity : 0≤((ε*(L:ℝ))^2)⁻¹) n)
    (AsymptoticFoldedTerminal.coefficient_norm_le (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) hε hd0 hd1 hsource hstrip ht n) z

theorem term_norm_le (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (n : ℤ) (z : ℍ) :
    ‖term hL b d s r hε hd0 hd1 hsource hstrip ht n z‖≤
      AsymptoticFoldMajorant.majorant 1 ((ε*(L:ℝ))^2)⁻¹ n :=
  AsymptoticOrbitBranch.operator_norm_le _ _ _ _ _

theorem term_covariant (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (n : ℤ) :
    Covariant (term hL b d s r hε hd0 hd1 hsource hstrip ht n) :=
  AsymptoticOrbitBranch.operator_covariant _ _ _
    (AsymptoticFoldedTerminal.coefficient_norm_le (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) hε hd0 hd1 hsource hstrip ht n)

theorem term_matrix_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t)
    (n : ℤ) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (term hL b d s r hε hd0 hd1 hsource hstrip ht n z) g h) :=
  AsymptoticOrbitBranch.operator_matrix_measurable
    (fun g => (AsymptoticRationalBranches.action_continuous g).measurable) _ _ _ _
    (AsymptoticFoldedTerminal.coefficient_measurable (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) hs hr ε t n) g h

theorem term_norm_summable (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (z : ℍ) :
    Summable (fun n => ‖term hL b d s r hε hd0 hd1 hsource hstrip ht n z‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => term_norm_le hL b d s r hε hd0 hd1 hsource hstrip ht n z)
    (AsymptoticFoldMajorant.majorant_summable_bound zero_le_one (by positivity)).1

noncomputable def operator (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (z : ℍ) :
    Space →L[ℂ] Space := ∑' n,term hL b d s r hε hd0 hd1 hsource hstrip ht n z

theorem operator_norm_le (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (z : ℍ) :
    ‖operator hL b d s r hε hd0 hd1 hsource hstrip ht z‖≤3+4*((ε*(L:ℝ))^2)⁻¹ := by
  have hn := term_norm_summable hL b d s r hε hd0 hd1 hsource hstrip ht z
  have hb := AsymptoticFoldMajorant.majorant_summable_bound zero_le_one
    (by positivity : 0≤((ε*(L:ℝ))^2)⁻¹)
  apply (norm_tsum_le_tsum_norm hn).trans
  simpa only [mul_one] using (hn.tsum_le_tsum
    (fun n => term_norm_le hL b d s r hε hd0 hd1 hsource hstrip ht n z) hb.1).trans hb.2

theorem operator_covariant (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) :
    Covariant (operator hL b d s r hε hd0 hd1 hsource hstrip ht) :=
  covariant_tsum _ (fun z => Summable.of_norm (term_norm_summable hL b d s r hε hd0 hd1 hsource hstrip ht z))
    (term_covariant hL b d s r hε hd0 hd1 hsource hstrip ht)

theorem operator_matrix_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t)
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (operator hL b d s r hε hd0 hd1 hsource hstrip ht z) g h) :=
  matrix_tsum_measurable _
    (fun z => Summable.of_norm (term_norm_summable hL b d s r hε hd0 hd1 hsource hstrip ht z))
    (term_matrix_measurable hL b d hs hr hε hd0 hd1 hsource hstrip ht) g h

#print axioms operator_norm_le
#print axioms operator_covariant
#print axioms operator_matrix_measurable

end AsymptoticRegularFoldedTerminal
