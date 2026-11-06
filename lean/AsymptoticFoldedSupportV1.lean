module

public import AsymptoticFoldedTerminalV1

set_option autoImplicit false
@[expose] public section

open MeasureTheory UpperHalfPlane Set Filter
open AsymptoticHyperbolicSlash

namespace AsymptoticFoldedLow

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

theorem operator_zero_off_source {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) (m : ℕ) (f : Space) :
    ∀ᵐ z ∂volume, z∉s → operator hL b d hs hr hcap hd0 hd1 hstrip t m f z=0 := by
  filter_upwards [operator_coeFn hL b d hs hr hcap hd0 hd1 hstrip ht m f] with z hz hzs
  rw [hz]
  have hseries : (∑' _n : ℤ, (0 : ℂ))=0 := by simp
  apply Eq.trans ?_ hseries
  apply tsum_congr
  intro n
  have hn : z∉region hL b d s r cap n := fun hh => hzs hh.1.1
  rw [coefficient,Set.indicator_of_notMem hn]
  simp

theorem operator_eq_zero_of_target {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤d) (hd1 : d≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) {t : ℕ} (ht : 1≤t) (m : ℕ) (f : Space)
    (hf : ∀ᵐ z ∂volume, z∈r → f z=0) :
    operator hL b d hs hr hcap hd0 hd1 hstrip t m f=0 := by
  have hp : ∀ᵐ z ∂volume, ∀ n : ℤ, fold hL b d n • z∈r → f (fold hL b d n • z)=0 :=
    ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (fold hL b d n) (volume : Measure ℍ)).quasiMeasurePreserving.ae hf)
  apply Lp.ext
  filter_upwards [operator_coeFn hL b d hs hr hcap hd0 hd1 hstrip ht m f,hp,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz hzp hzero
  rw [hz,hzero]
  have hseries : (∑' _n : ℤ, (0 : ℂ))=0 := by simp
  apply Eq.trans ?_ hseries
  apply tsum_congr
  intro n
  classical
  by_cases hn : z∈region hL b d s r cap n
  · rw [hzp n hn.1.2,mul_zero]
  · rw [coefficient,Set.indicator_of_notMem hn]
    simp

#print axioms operator_zero_off_source
#print axioms operator_eq_zero_of_target

end AsymptoticFoldedLow

namespace AsymptoticFoldedTerminal

open AsymptoticFoldedLow (fold)

variable {L : ℝ} (hL : 0<L) (b d : ℝ)

theorem operator_zero_off_source {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (f : Space) :
    ∀ᵐ z ∂volume, z∉s → operator hL b d hs hr hε hd0 hd1 hsource hstrip ht m f z=0 := by
  filter_upwards [operator_coeFn hL b d hs hr hε hd0 hd1 hsource hstrip ht m f] with z hz hzs
  rw [hz]
  have hseries : (∑' _n : ℤ, (0 : ℂ))=0 := by simp
  apply Eq.trans ?_ hseries
  apply tsum_congr
  intro n
  have hn : z∉region hL b d s r n := fun hh => hzs hh.1
  rw [coefficient,Set.indicator_of_notMem hn]
  simp

theorem operator_eq_zero_of_target {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤d) (hd1 : d≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (f : Space) (hf : ∀ᵐ z ∂volume, z∈r → f z=0) :
    operator hL b d hs hr hε hd0 hd1 hsource hstrip ht m f=0 := by
  have hp : ∀ᵐ z ∂volume, ∀ n : ℤ, fold hL b d n • z∈r → f (fold hL b d n • z)=0 :=
    ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (fold hL b d n) (volume : Measure ℍ)).quasiMeasurePreserving.ae hf)
  apply Lp.ext
  filter_upwards [operator_coeFn hL b d hs hr hε hd0 hd1 hsource hstrip ht m f,hp,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz hzp hzero
  rw [hz,hzero]
  have hseries : (∑' _n : ℤ, (0 : ℂ))=0 := by simp
  apply Eq.trans ?_ hseries
  apply tsum_congr
  intro n
  classical
  by_cases hn : z∈region hL b d s r n
  · rw [hzp n hn.2,mul_zero]
  · rw [coefficient,Set.indicator_of_notMem hn]
    simp

#print axioms operator_zero_off_source
#print axioms operator_eq_zero_of_target

end AsymptoticFoldedTerminal
