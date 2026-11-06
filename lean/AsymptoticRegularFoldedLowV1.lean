module

public import AsymptoticRationalBranchesV1
public import AsymptoticRegularAlgebraV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularFoldedLow

open MeasureTheory UpperHalfPlane Set ContinuousLinearMap AsymptoticRegularTrace
open scoped lp

noncomputable abbrev Space := ℓ²(AsymptoticRationalGroup.Group,ℂ)

variable {L : ℚ} (hL : 0<L) (b d : ℚ)

noncomputable def term (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    (t : ℕ) (n : ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitBranch.operator (AsymptoticRationalBranches.fold hL b d n)
    (AsymptoticFoldedLow.coefficient (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) s r cap t n)
    (pow_nonneg (AsymptoticFoldMajorant.majorant_nonneg hcap (by positivity : 0≤4/(L:ℝ)) n) t)
    (AsymptoticFoldedLow.coefficient_norm_le (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) hcap hd0 hd1 hstrip t n) z

theorem term_norm_le (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    (t : ℕ) (n : ℤ) (z : ℍ) :
    ‖term hL b d s r hcap hd0 hd1 hstrip t n z‖≤
      AsymptoticFoldMajorant.majorant cap (4/(L:ℝ)) n^t :=
  AsymptoticOrbitBranch.operator_norm_le _ _ _ _ _

theorem term_covariant (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    (t : ℕ) (n : ℤ) : Covariant (term hL b d s r hcap hd0 hd1 hstrip t n) :=
  AsymptoticOrbitBranch.operator_covariant _ _ _
    (AsymptoticFoldedLow.coefficient_norm_le (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) hcap hd0 hd1 hstrip t n)

theorem term_matrix_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t : ℕ) (n : ℤ)
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (term hL b d s r hcap hd0 hd1 hstrip t n z) g h) :=
  AsymptoticOrbitBranch.operator_matrix_measurable
    (fun g => (AsymptoticRationalBranches.action_continuous g).measurable) _ _ _ _
    (AsymptoticFoldedLow.coefficient_measurable (show (0:ℝ)<L by exact_mod_cast hL)
      (b:ℝ) (d:ℝ) hs hr cap t n) g h

theorem term_norm_summable (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 1≤t) (z : ℍ) :
    Summable (fun n => ‖term hL b d s r hcap hd0 hd1 hstrip t n z‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => term_norm_le hL b d s r hcap hd0 hd1 hstrip t n z)
    (AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/(L:ℝ)) ht).1

/-- The counting-space low branch contains every integer fold, with the
same norm-summable majorant as the hyperbolic realization. -/
noncomputable def operator (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    (t : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  ∑' n,term hL b d s r hcap hd0 hd1 hstrip t n z

theorem operator_norm_le (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 1≤t) (z : ℍ) :
    ‖operator hL b d s r hcap hd0 hd1 hstrip t z‖≤cap^(t-1)*(3*cap+16/(L:ℝ)) := by
  have hn := term_norm_summable hL b d s r hcap hd0 hd1 hstrip ht z
  have hb := AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/(L:ℝ)) ht
  apply (norm_tsum_le_tsum_norm hn).trans
  have he := (hn.tsum_le_tsum (fun n => term_norm_le hL b d s r hcap hd0 hd1 hstrip t n z) hb.1).trans hb.2
  convert he using 1
  ring

theorem operator_covariant (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 1≤t) : Covariant (operator hL b d s r hcap hd0 hd1 hstrip t) :=
  covariant_tsum _ (fun z => Summable.of_norm (term_norm_summable hL b d s r hcap hd0 hd1 hstrip ht z))
    (term_covariant hL b d s r hcap hd0 hd1 hstrip t)

theorem operator_matrix_measurable {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t)
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (operator hL b d s r hcap hd0 hd1 hstrip t z) g h) :=
  matrix_tsum_measurable _
    (fun z => Summable.of_norm (term_norm_summable hL b d s r hcap hd0 hd1 hstrip ht z))
    (term_matrix_measurable hL b d hs hr hcap hd0 hd1 hstrip t) g h

#print axioms operator_norm_le
#print axioms operator_covariant
#print axioms operator_matrix_measurable

end AsymptoticRegularFoldedLow
