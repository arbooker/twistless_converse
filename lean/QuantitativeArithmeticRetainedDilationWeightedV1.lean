module

public import QuantitativeArithmeticRetainedDilationOperatorV1
public import AsymptoticWeightedBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeArithmeticRetainedDilationWeighted

open UpperHalfPlane Set MeasureTheory Filter
open QuantitativeArithmeticRetainedDilationOperator
open AsymptoticWeightedBranches (stripSection)
open AsymptoticCertificateOperators (lowStrip highStrip)

/-- Literal section-valued finite folding, prior to passing to L2. -/
def foldedValue (a b : ℝ) (ha : 0<a) (s r : Set ℍ) (ε : ℝ) (t m : ℕ)
    (F : ℂ → ℂ) (z : ℍ) : ℂ :=
  ∑ n∈folds a b, coefficient a b ha s r n z*
    stripSection ε t m F (AsymptoticMobiusFold.fold (affine a b ha) n • z)

theorem foldedValue_zero (a b : ℝ) (ha : 0<a) (s r : Set ℍ) (ε : ℝ) (t m : ℕ)
    (F : ℂ → ℂ) (z : ℍ) (hz : z∉s) : foldedValue a b ha s r ε t m F z=0 := by
  classical
  apply Finset.sum_eq_zero
  intro n _
  have hn : z∉region a b ha s r n := fun h => hz h.1
  rw [coefficient,Set.indicator_of_notMem hn,zero_mul]

theorem section_selected (a b : ℝ) (ha : 0<a) (ε : ℝ) (t m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (z : ℍ) :
    stripSection ε t m F
      (AsymptoticMobiusFold.fold (affine a b ha) (Int.floor (affine a b ha • z).re) • z)=
        AsymptoticWeightedBranches.weighted ε t m F (affine a b ha • z) := by
  rw [stripSection,Set.indicator_of_mem
    ((AsymptoticMobiusFold.fold_mem_strip_iff _ _ _).mpr rfl)]
  simp only [AsymptoticWeightedBranches.weighted,AsymptoticMobiusFold.fold_im,
    AsymptoticMobiusFold.periodic_fold _ F hp]

/-- The low and terminal affine pieces exactly reproduce the capped
weighted branch. Both target regions, including the boundary, are covered. -/
theorem values_eq (a b : ℝ) (ha : 0<a) {ε : ℝ} (hε : 0<ε)
    (s : Set ℍ) (hs : s⊆lowStrip ε) (β : ℂ) (t m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (z : ℍ) :
    β*((a⁻¹^t:ℝ):ℂ)*foldedValue a b ha s (lowStrip ε) ε t m F z+
      β*capWeight ε t z*foldedValue a b ha s (highStrip ε) ε t m F z=
    s.indicator (fun w : ℍ => capWeight ε t w*β*
      ((affine a b ha • w).im:ℂ)^m*F (affine a b ha • w:ℍ)) z := by
  classical
  by_cases hz : z∈s
  · rw [Set.indicator_of_mem hz]
    have hstrip := (AsymptoticMobiusFold.fold_mem_strip_iff (affine a b ha)
      (Int.floor (affine a b ha • z).re) z).mpr rfl
    have hlo := folded_value a b ha (fun w hw => (hs hw).1) (fun _ hw => hw.1)
      (stripSection ε t m F) z hz (r:=lowStrip ε)
    have hhi := folded_value a b ha (fun w hw => (hs hw).1) (fun _ hw => hw.1)
      (stripSection ε t m F) z hz (r:=highStrip ε)
    change foldedValue a b ha s (lowStrip ε) ε t m F z=_ at hlo
    change foldedValue a b ha s (highStrip ε) ε t m F z=_ at hhi
    rw [hlo,hhi]
    have hzε : z.im≤ε := (show z.im<ε from (hs hz).2).le
    have hcap : capWeight ε t z=((z.im/ε)^t:ℝ) := by
      rw [capWeight,min_eq_left ((div_le_one hε).mpr hzε)]
    by_cases hw : (affine a b ha • z).im<ε
    · have hl : AsymptoticMobiusFold.fold (affine a b ha)
          (Int.floor (affine a b ha • z).re) • z∈lowStrip ε :=
        ⟨hstrip,by simpa only [Set.mem_ofPred_eq,AsymptoticMobiusFold.fold_im] using hw⟩
      have hh : AsymptoticMobiusFold.fold (affine a b ha)
          (Int.floor (affine a b ha • z).re) • z∉highStrip ε := by
        intro hh
        have hh : ε≤(AsymptoticMobiusFold.fold (affine a b ha)
          (Int.floor (affine a b ha • z).re) • z).im := hh.2
        rw [AsymptoticMobiusFold.fold_im] at hh
        exact (not_le_of_gt hw) hh
      rw [Set.indicator_of_mem hl,Set.indicator_of_notMem hh,mul_zero,add_zero,
        section_selected a b ha ε t m F hp z,hcap]
      have hc := AsymptoticWeightedBranches.low_weight_cancel hε t m F z
        (affine a b ha • z) hw.le
      have he : z.im/(affine a b ha • z).im=a⁻¹ := by
        rw [affine_im]
        field_simp
      rw [he] at hc
      linear_combination β*hc
    · have hh : AsymptoticMobiusFold.fold (affine a b ha)
          (Int.floor (affine a b ha • z).re) • z∈highStrip ε :=
        ⟨hstrip,by simpa only [Set.mem_ofPred_eq,AsymptoticMobiusFold.fold_im] using le_of_not_gt hw⟩
      have hl : AsymptoticMobiusFold.fold (affine a b ha)
          (Int.floor (affine a b ha • z).re) • z∉lowStrip ε := by
        intro hl
        exact hw (by simpa only [Set.mem_ofPred_eq,AsymptoticMobiusFold.fold_im] using hl.2)
      rw [Set.indicator_of_notMem hl,Set.indicator_of_mem hh,mul_zero,zero_add,
        section_selected a b ha ε t m F hp z,
        AsymptoticWeightedBranches.weighted_high hε t m F _ (le_of_not_gt hw)]
      ring
  · rw [foldedValue_zero a b ha s (lowStrip ε) ε t m F z hz,
      foldedValue_zero a b ha s (highStrip ε) ε t m F z hz,Set.indicator_of_notMem hz]
    ring

/-- Pulling an almost-everywhere section identity through every affine
fold is justified by preservation of hyperbolic measure. -/
theorem folded_coeFn_section (a b : ℝ) (ha : 0<a) {s r : Set ℍ}
    (hs : MeasurableSet s) (hr : MeasurableSet r) (ε : ℝ) (t m : ℕ)
    (F : ℂ → ℂ) (u : AsymptoticHyperbolicSlash.Space)
    (hu : u =ᵐ[volume] stripSection ε t m F) :
    folded a b ha hs hr (2*m) u =ᵐ[volume] foldedValue a b ha s r ε t m F := by
  have hp : ∀ᵐ z ∂volume,∀ n : ℤ,
      u (AsymptoticMobiusFold.fold (affine a b ha) n • z)=
        stripSection ε t m F (AsymptoticMobiusFold.fold (affine a b ha) n • z) :=
    ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (AsymptoticMobiusFold.fold (affine a b ha) n)
        (volume:Measure ℍ)).quasiMeasurePreserving.ae hu)
  filter_upwards [folded_coeFn a b ha hs hr (2*m) u,hp] with z hz hp
  rw [hz]
  apply Finset.sum_congr rfl
  intro n _
  rw [hp n]


/-- The actual low and terminal L2 operators agree with the capped
pointwise branch on every periodic section represented in L2. -/
theorem operators_coeFn_section (a b : ℝ) (ha : 0<a) {ε : ℝ} (hε : 0<ε)
    {s : Set ℍ} (hs : MeasurableSet s) (hslow : s⊆lowStrip ε)
    (β : ℂ) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (u : AsymptoticHyperbolicSlash.Space) (hu : u =ᵐ[volume] stripSection ε t m F) :
    (weighted a b ha hs (AsymptoticCertificateOperators.lowStrip_measurable ε) β t (2*m) u+
      terminal a b ha hs (AsymptoticCertificateOperators.highStrip_measurable ε)
        ε hε β t (2*m) u:AsymptoticHyperbolicSlash.Space) =ᵐ[volume]
      s.indicator (fun w : ℍ => capWeight ε t w*β*
        ((affine a b ha • w).im:ℂ)^m*F (affine a b ha • w:ℍ)) := by
  let hslo := AsymptoticCertificateOperators.lowStrip_measurable ε
  let hshi := AsymptoticCertificateOperators.highStrip_measurable ε
  have hcap := AsymptoticL2Multiplier.operator_coeFn (capWeight ε t)
    (capWeight_measurable ε t).aestronglyMeasurable
    (Eventually.of_forall (capWeight_norm_le ε hε t)) (folded a b ha hs hshi (2*m) u)
  have hlo := folded_coeFn_section a b ha hs hslo ε t m F u hu
  have hhi := folded_coeFn_section a b ha hs hshi ε t m F u hu
  have hsmlo := Lp.coeFn_smul (β*((a⁻¹^t:ℝ):ℂ)) (folded a b ha hs hslo (2*m) u)
  have hsmhi := Lp.coeFn_smul β (capOperator ε hε t (folded a b ha hs hshi (2*m) u))
  have hadd := Lp.coeFn_add (weighted a b ha hs hslo β t (2*m) u)
    (terminal a b ha hs hshi ε hε β t (2*m) u)
  filter_upwards [hadd,hsmlo,hsmhi,hcap,hlo,hhi] with z hadd hsmlo hsmhi hcap hlo hhi
  rw [hadd]
  change ((β*((a⁻¹^t:ℝ):ℂ)) • folded a b ha hs hslo (2*m) u) z+
    (β • capOperator ε hε t (folded a b ha hs hshi (2*m) u)) z=_
  rw [hsmlo,hsmhi]
  change (β*((a⁻¹^t:ℝ):ℂ))*(folded a b ha hs hslo (2*m) u z)+
    β*(capOperator ε hε t (folded a b ha hs hshi (2*m) u) z)=_
  rw [show capOperator ε hε t (folded a b ha hs hshi (2*m) u) z=_ from hcap,hlo,hhi]
  simpa only [mul_assoc] using values_eq a b ha hε s hslow β t m F hp z

#print axioms operators_coeFn_section
#print axioms section_selected
#print axioms values_eq
#print axioms folded_coeFn_section

end QuantitativeArithmeticRetainedDilationWeighted
