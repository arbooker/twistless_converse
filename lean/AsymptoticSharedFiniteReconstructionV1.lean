module

public import AsymptoticFiniteFoldReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticSharedApproximation

open UpperHalfPlane Filter FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCertificateOperators
open scoped Topology

private theorem norm_error_eventually {G E α ι : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {l : Filter ι} (F : ι → α → G →L[ℂ] E) (f : α → G →L[ℂ] E)
    (h : TendstoUniformly F f l) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ i in l,∀ a,‖F i a-f a‖<δ := by
  apply ((Metric.tendstoUniformly_iff.mp h) δ hδ).mono
  intro i hi a
  simpa only [dist_eq_norm,norm_sub_rev] using hi a

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- All admissible phase choices at once, rather than a single sector. -/
def UnitMultipliers (Q : ℕ) := {χ : ℕ → ℂ // ∀ q,q∣Q → ‖χ q‖=1}

/-- First choose finite depth, then a common finite set of integer folds.
Both choices precede variation of weight, orbit root, or sector. -/
theorem finite_reconstruction_approximation (hN : 0<N) (P : Parameters A)
    (hP : P.ρ^(P.s+3-1)*lowConstant A P≤1/2) {δ : ℝ} (hδ : 0<δ) :
    ∃ n : ℕ,∃ I : Finset ℤ,
      (∀ χ : UnitMultipliers Q,∀ m : ℕ,
        ‖AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ.val n I m-
          AsymptoticGeometricReconstruction.extension A hN P χ.val m‖<δ) ∧
      (∀ χ : UnitMultipliers Q,∀ z : ℍ,
        ‖AsymptoticRegularReconstruction.finiteFoldFull A hN P χ.val n I z-
          AsymptoticRegularReconstruction.full A hN P χ.val z‖<δ) := by
  have hd : Tendsto (fun n : ℕ => 2*terminalConstant A P*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).const_mul
        (2*terminalConstant A P)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp hd).2 (δ/2) (half_pos hδ)).exists
  have hP1 : P.ρ^(P.s+3-1)*lowConstant A P≤1 := hP.trans (by norm_num)
  have hh := AsymptoticGeometricReconstruction.finiteFoldExtension_tendstoUniformly A hN P hP1
    (fun a : UnitMultipliers Q × ℕ => a.2) (fun a => a.1.val) (fun a => a.1.property) n
  have hr := AsymptoticRegularReconstruction.finiteFoldFull_tendstoUniformly A hN P hP1
    (fun a : UnitMultipliers Q × ℍ => a.2) (fun a => a.1.val) (fun a => a.1.property) n
  obtain ⟨I,hIh,hIr⟩ := ((norm_error_eventually _ _ hh (half_pos hδ)).and
    (norm_error_eventually _ _ hr (half_pos hδ))).exists
  refine ⟨n,I,?_,?_⟩
  · intro χ m
    have hK : ‖low A hN P χ.val (P.s+3) m‖≤1/2 :=
      (low_norm_le A hN P χ.val χ.property (by omega) m).trans hP
    have hfold : ‖AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ.val n I m-
        AsymptoticGeometricReconstruction.finiteExtension A hN P χ.val m n‖<δ/2 := by
      exact hIh (χ,m)
    have hdepth := (AsymptoticGeometricReconstruction.finiteExtension_error
      A hN P χ.val χ.property m n hK).trans_lt hn
    exact (norm_sub_le_norm_sub_add_norm_sub _ (AsymptoticGeometricReconstruction.finiteExtension A hN P χ.val m n) _).trans_lt
      ((add_lt_add hfold hdepth).trans_eq (add_halves δ))
  · intro χ z
    have hK : ‖AsymptoticRegularCertificate.low A hN P χ.val (P.s+3) z‖≤1/2 :=
      (AsymptoticRegularCertificate.low_norm_le A hN P χ.val χ.property (by omega) z).trans hP
    have hfold : ‖AsymptoticRegularReconstruction.finiteFoldFull A hN P χ.val n I z-
        AsymptoticRegularReconstruction.finiteFull A hN P χ.val n z‖<δ/2 := by
      exact hIr (χ,z)
    have hdepth := (AsymptoticRegularReconstruction.finiteFull_error
      A hN P χ.val χ.property n z hK).trans_lt hn
    exact (norm_sub_le_norm_sub_add_norm_sub _ (AsymptoticRegularReconstruction.finiteFull A hN P χ.val n z) _).trans_lt
      ((add_lt_add hfold hdepth).trans_eq (add_halves δ))

#print axioms finite_reconstruction_approximation

end AsymptoticSharedApproximation
