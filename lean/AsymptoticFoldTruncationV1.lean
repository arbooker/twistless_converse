module

public import AsymptoticRegularFoldedTerminalV1
public import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFoldedLow

open MeasureTheory UpperHalfPlane Set Filter

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

/-- The same finite set of folds approximates every holomorphic weight.
The measurable cell rule is retained in every summand. -/
theorem finite_folds_tendstoUniformly {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ => ∑ n∈I,term hL b d hs hr hcap hd0 hd1 hstrip t m n)
      (operator hL b d hs hr hcap hd0 hd1 hstrip t) atTop :=
  tendstoUniformly_tsum (AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/L) ht).1
    (fun n m => term_norm_le hL b d hs hr hcap hd0 hd1 hstrip t m n)

theorem finite_folds_norm_le {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (m : ℕ) :
    ‖∑ n∈I,term hL b d hs hr hcap hd0 hd1 hstrip t m n‖≤cap^(t-1)*(3*cap+16/L) := by
  have hb := AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/L) ht
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => term_norm_le hL b d hs hr hcap hd0 hd1 hstrip t m n)).trans
  have he := (Summable.sum_le_tsum I (fun n _ => pow_nonneg
    (AsymptoticFoldMajorant.majorant_nonneg hcap (by positivity : 0≤4/L) n) t) hb.1).trans hb.2
  convert he using 1
  ring

#print axioms finite_folds_tendstoUniformly
#print axioms finite_folds_norm_le

end AsymptoticFoldedLow

namespace AsymptoticFoldedTerminal

open MeasureTheory UpperHalfPlane Set Filter

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

theorem finite_folds_tendstoUniformly {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun m : ℕ => ∑ n∈I,term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n)
      (operator hL b d hs hr hε hd0 hd1 hsource hstrip ht) atTop :=
  tendstoUniformly_tsum (AsymptoticFoldMajorant.majorant_summable_bound zero_le_one
    (by positivity : 0≤((ε*L)^2)⁻¹)).1
    (fun n m => term_norm_le hL b d hs hr hε hd0 hd1 hsource hstrip ht m n)

theorem finite_folds_norm_le {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t)
    (I : Finset ℤ) (m : ℕ) :
    ‖∑ n∈I,term hL b d hs hr hε hd0 hd1 hsource hstrip ht m n‖≤3+4*((ε*L)^2)⁻¹ := by
  have hb := AsymptoticFoldMajorant.majorant_summable_bound zero_le_one (by positivity : 0≤((ε*L)^2)⁻¹)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => term_norm_le hL b d hs hr hε hd0 hd1 hsource hstrip ht m n)).trans
  simpa only [mul_one] using (Summable.sum_le_tsum I (fun n _ => AsymptoticFoldMajorant.majorant_nonneg zero_le_one (by positivity) n) hb.1).trans hb.2

#print axioms finite_folds_tendstoUniformly
#print axioms finite_folds_norm_le

end AsymptoticFoldedTerminal

namespace AsymptoticRegularFoldedLow

open UpperHalfPlane Set Filter

variable {L : ℚ} (hL : 0<L) (b d : ℚ)

theorem finite_folds_tendstoUniformly (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ => ∑ n∈I,term hL b d s r hcap hd0 hd1 hstrip t n z)
      (operator hL b d s r hcap hd0 hd1 hstrip t) atTop :=
  tendstoUniformly_tsum (AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/(L:ℝ)) ht).1
    (fun n z => term_norm_le hL b d s r hcap hd0 hd1 hstrip t n z)

theorem finite_folds_norm_le (s r : Set ℍ) {cap : ℝ} (hcap : 0≤cap)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t)
    (I : Finset ℤ) (z : ℍ) :
    ‖∑ n∈I,term hL b d s r hcap hd0 hd1 hstrip t n z‖≤cap^(t-1)*(3*cap+16/(L:ℝ)) := by
  have hb := AsymptoticFoldMajorant.power_summable_bound hcap (by positivity : 0≤4/(L:ℝ)) ht
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => term_norm_le hL b d s r hcap hd0 hd1 hstrip t n z)).trans
  have he := (Summable.sum_le_tsum I (fun n _ => pow_nonneg
    (AsymptoticFoldMajorant.majorant_nonneg hcap (by positivity : 0≤4/(L:ℝ)) n) t) hb.1).trans hb.2
  convert he using 1
  ring

#print axioms finite_folds_tendstoUniformly
#print axioms finite_folds_norm_le

end AsymptoticRegularFoldedLow

namespace AsymptoticRegularFoldedTerminal

open UpperHalfPlane Set Filter

variable {L : ℚ} (hL : 0<L) (b d : ℚ)

theorem finite_folds_tendstoUniformly (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun z : ℍ => ∑ n∈I,term hL b d s r hε hd0 hd1 hsource hstrip ht n z)
      (operator hL b d s r hε hd0 hd1 hsource hstrip ht) atTop :=
  tendstoUniformly_tsum (AsymptoticFoldMajorant.majorant_summable_bound zero_le_one
    (by positivity : 0≤((ε*(L:ℝ))^2)⁻¹)).1
    (fun n z => term_norm_le hL b d s r hε hd0 hd1 hsource hstrip ht n z)

theorem finite_folds_norm_le (s r : Set ℍ) {ε : ℝ} (hε : 0<ε)
    (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1) (hsource : s⊆{z | z.im≤ε})
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (z : ℍ) :
    ‖∑ n∈I,term hL b d s r hε hd0 hd1 hsource hstrip ht n z‖≤3+4*((ε*(L:ℝ))^2)⁻¹ := by
  have hb := AsymptoticFoldMajorant.majorant_summable_bound zero_le_one (by positivity : 0≤((ε*(L:ℝ))^2)⁻¹)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun n _ => term_norm_le hL b d s r hε hd0 hd1 hsource hstrip ht n z)).trans
  simpa only [mul_one] using (Summable.sum_le_tsum I (fun n _ => AsymptoticFoldMajorant.majorant_nonneg zero_le_one (by positivity) n) hb.1).trans hb.2

#print axioms finite_folds_tendstoUniformly
#print axioms finite_folds_norm_le

end AsymptoticRegularFoldedTerminal
