module

public import AsymptoticCompactBranchV1

set_option autoImplicit false
set_option maxHeartbeats 600000
@[expose] public section

namespace AsymptoticCompactBranch

open MeasureTheory UpperHalfPlane Set Filter
open AsymptoticHyperbolicSlash AsymptoticMobiusFold AsymptoticWeightedBranches

theorem selected_section (g : GL (Fin 2) ℝ) (ε : ℝ) (t m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (n : ℤ) (z : ℍ)
    (hn : n=Int.floor (g • z).re) :
    stripSection ε t m F (fold g n • z)=weighted ε t m F (g • z) := by
  rw [stripSection,Set.indicator_of_mem ((fold_mem_strip_iff g n z).mpr hn),
    weighted,weighted,fold_im,periodic_fold g F hp]

theorem folded_formula (g : GL (Fin 2) ℝ) (hg : 0<g.det.val) {s : Set ℍ}
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (z : ℍ) :
    (∑ n∈D.folds,coefficient g s ε t z*phase (fold g n) (2*m) z*
      stripSection ε t m F (fold g n • z))=
    s.indicator (fun w : ℍ => (cap ε t w:ℂ)*phase g (2*m) w*
      ((g • w).im:ℂ)^m*F (g • w:ℍ)) z := by
  classical
  by_cases hz : z∈s
  · rw [Finset.sum_eq_single (Int.floor (g • z).re)]
    · rw [coefficient,Set.indicator_of_mem hz,Set.indicator_of_mem hz,
        selected_section g ε t m F hp _ z rfl,fold_phase g hg]
      have hc : (ratio g ε t z:ℂ)*(cap ε t (g • z):ℂ)=(cap ε t z:ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        exact div_mul_cancel₀ _ (cap_pos hε t (g • z)).ne'
      change (ratio g ε t z:ℂ)*phase g (2*m) z*
        ((cap ε t (g • z):ℂ)*((g • z).im:ℂ)^m*F (g • z:ℍ))=_
      linear_combination phase g (2*m) z*((g • z).im:ℂ)^m*F (g • z:ℍ)*hc
    · intro n _ hn
      rw [stripSection,Set.indicator_of_notMem ((fold_mem_strip_iff g n z).not.mpr hn),mul_zero]
    · exact fun h => False.elim (h (D.fold_mem z hz))
  · simp [coefficient,hz]

/-- Exact formula on a periodic analytic representative, with all folds,
the capped conjugation and the genuine slash phase included. -/
theorem operator_on_section (g : GL (Fin 2) ℝ) (hg : 0<g.det.val) {s : Set ℍ}
    (hs : MeasurableSet s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (D : Data g s ε t) (m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (u : Space)
    (hu : u =ᵐ[volume] stripSection ε t m F) :
    operator g hs hε t D m u =ᵐ[volume] s.indicator (fun z : ℍ =>
      (cap ε t z:ℂ)*phase g (2*m) z*((g • z).im:ℂ)^m*F (g • z:ℍ)) := by
  have hrep : ∀ᵐ z ∂volume,∀ n : ℤ,u (fold g n • z)=stripSection ε t m F (fold g n • z) := by
    apply ae_all_iff.mpr
    intro n
    exact (measurePreserving_smul (fold g n) (volume : Measure ℍ)).quasiMeasurePreserving.ae
      (p:=fun w : ℍ => u w=stripSection ε t m F w) hu
  filter_upwards [operator_coeFn g hs hε t D m u,hrep] with z hz hrepz
  apply hz.trans
  calc
    (∑ n∈D.folds,coefficient g s ε t z*phase (fold g n) (2*m) z*u (fold g n • z))=
        ∑ n∈D.folds,coefficient g s ε t z*phase (fold g n) (2*m) z*stripSection ε t m F (fold g n • z) :=
      Finset.sum_congr rfl (fun n _ => by rw [hrepz n])
    _ = _ := folded_formula g hg hε t D m F hp z

noncomputable def compactOperator (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) : Space →L[ℂ] Space :=
  operator g hs.isClosed.measurableSet hε t (data g hs hε t) m

theorem compactOperator_norm_le (g : GL (Fin 2) ℝ) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    ‖compactOperator g hs hε t m‖≤(data g hs hε t).folds.card*(data g hs hε t).bound :=
  operator_norm_le g hs.isClosed.measurableSet hε t _ m

theorem compactOperator_on_section (g : GL (Fin 2) ℝ) (hg : 0<g.det.val) {s : Set ℍ}
    (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (u : Space)
    (hu : u =ᵐ[volume] stripSection ε t m F) :
    compactOperator g hs hε t m u =ᵐ[volume] s.indicator (fun z : ℍ =>
      (cap ε t z:ℂ)*phase g (2*m) z*((g • z).im:ℂ)^m*F (g • z:ℍ)) :=
  operator_on_section g hg hs.isClosed.measurableSet hε t _ m F hp u hu

#print axioms folded_formula
#print axioms operator_on_section
#print axioms compactOperator_norm_le

end AsymptoticCompactBranch
