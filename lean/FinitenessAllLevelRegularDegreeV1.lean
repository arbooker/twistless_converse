module

public import FinitenessAllLevelFiniteSheetsV1
public import FinitenessAllLevelProjectionDichotomyV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter FinitenessAllLevelCoefficientRing
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def regularValues (R : ℂ → X → Prop) : Set ℂ :=
  {w | ∀ x, R w x → AmbientGraphAt R w x}

/-- Exceptional values for actual ambient graphs are isolated in every
polynomial chart, including around exceptional parameters themselves. -/
theorem Presentation.punctured_regularValues {ι : Type*} [Finite ι]
    {R : ℂ → X → Prop} (c : Presentation ι R)
    (hconn : IsPreconnected c.U)
    (hf : ∀ z : ℂ, {t : ℂ × X | R t.1 t.2 ∧ t.1 = z}.Finite)
    {w : ℂ} (hw : w ∈ c.U) :
    ∀ᶠ z in 𝓝[≠] w, z ∈ regularValues R := by
  obtain ⟨D⟩ := c.exists_branchCertificate hconn ⟨w, hw⟩ hf
  have hU : ∀ᶠ z in 𝓝[≠] w, z ∈ c.U := nhdsWithin_le_nhds (c.openU.mem_nhds hw)
  have hn := representative_nonzero_punctured c.coefficientFunctions hconn
    c.coefficientFunctions_analytic D.exceptional_ne_zero hw
  filter_upwards [hU, hn] with z hz he x hx
  apply D.ambient_graph c ⟨z, hz⟩ ?_ hx
  change D.exceptional.val ⟨z, hz⟩ ≠ 0
  rwa [representative_agrees (z := ⟨z, hz⟩)] at he

/-- Removing the closed discrete exceptional values leaves a connected
planar domain, and the actual finite fiber cardinal is constant there. -/
theorem regular_degree (R : ℂ → X → Prop)
    (hp : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (hf : ∀ w, {x | R w x}.Finite)
    (hreg : regularValues R ∈ codiscrete ℂ) :
    ∃ D : ℕ, ∀ w ∈ regularValues R, Nat.card {x | R w x} = D := by
  have hd := (mem_codiscrete'.mp hreg).2
  have hc : (regularValues R)ᶜ.Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd
  have hconn : IsConnected (regularValues R) := by
    simpa only [compl_compl] using hc.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ (by norm_num : (1 : Cardinal) < 2))
  let := Subtype.preconnectedSpace hconn.isPreconnected
  have hlocal : IsLocallyConstant (fun w : regularValues R => Nat.card {x | R w.val x}) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro w
    exact continuous_subtype_val.continuousAt.tendsto.eventually
      (fiber_card_eventually R hp w.val (hf w.val) w.property)
  obtain ⟨w, hw⟩ := hconn.nonempty
  refine ⟨Nat.card {x | R w x}, fun z hz => ?_⟩
  exact hlocal.apply_eq_of_preconnectedSpace ⟨z, hz⟩ ⟨w, hw⟩

#print axioms Presentation.punctured_regularValues
#print axioms regular_degree

end FinitenessAllLevelPolynomialPresentation

namespace FinitenessAllLevelConstraintLocus

open Complex Set Filter FinitenessAllLevelGlobalHeight FinitenessAllLevelPolynomialPresentation
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2)
    (hpQ : p ∣ Q) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a b : ℝ} (hb : 0 < b) (hba : b < a) (hae : a ≤ P.ε)
    {m : ℕ} (hm : 0 < m) (s : Fin (Q + 1) → Bool)

include hp hgood hlarge hpQ hae hm

/-- Actual sector regular values form an open set with closed discrete
complement. No abstract analytic normalization theorem is used. -/
theorem sector_regular_values_codiscrete :
    regularValues (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s) ∈ codiscrete ℂ := by
  apply mem_codiscrete_iff_forall_mem_nhdsNE.mpr
  intro w
  obtain ⟨d, es, c, hw⟩ := sector_polynomial_presentation hN hp A P hb hba hae m s w
  obtain ⟨c', hw', hc'⟩ := c.connected_restriction hw
  exact c'.punctured_regularValues hc'
    (fun z => global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z) hw'

/-- One finite degree works for all regular eigenvalues of the actual
sector, over the entire plane. -/
theorem sector_regular_degree :
    ∃ D : ℕ, ∀ z ∈ regularValues (fun z F => (z, F) ∈ sectorLocus hN A P hb hba m s),
      Nat.card {F | (z, F) ∈ sectorLocus hN A P hb hba m s} = D := by
  apply regular_degree
  · exact global_sector_projection_isProperMap hN hp hgood hlarge hpQ A P hb hba hae hm s
  · intro z
    apply ((global_sector_fiber_finite hN hp hgood hlarge hpQ A P hb hba hae hm s z).image Prod.snd).subset
    intro F hF
    exact ⟨(z, F), ⟨hF, rfl⟩, rfl⟩
  · exact sector_regular_values_codiscrete hN hp hgood hlarge hpQ A P hb hba hae hm s

#print axioms sector_regular_values_codiscrete
#print axioms sector_regular_degree

end FinitenessAllLevelConstraintLocus
