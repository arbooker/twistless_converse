module

public import FinitenessAllLevelGlobalSectorFibersV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelAnalyticAtlas

open Complex Set FinitenessAllLevelAnalyticSubstitution FinitenessAllLevelChartTopology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- An explicit finite-dimensional holomorphic zero-set chart for a locus in
C times a Banach space. These fields give actual equations and coordinate maps;
no dimension, normalization, proper mapping, or curve-selection theorem is a field. -/
structure Chart (I : Type*) (R : ℂ → X → Prop) where
  E : Submodule ℂ X
  Y : Submodule ℂ X
  finiteE : FiniteDimensional ℂ E
  finiteY : FiniteDimensional ℂ Y
  U : Set ℂ
  openU : IsOpen U
  indices : Finset I
  read : X →L[ℂ] E
  lift : ℂ → E →L[ℂ] X
  equations : ℂ × E → Y × (indices → ℂ)
  analytic_lift : AnalyticOnNhd ℂ lift U
  analytic_equations : AnalyticOnNhd ℂ equations (U ×ˢ univ)
  read_lift : ∀ z v, read (lift z v) = v
  exact_locus : ∀ z ∈ U, ∀ x, R z x ↔ ∃ v, equations (z, v) = 0 ∧ x = lift z v

variable {I : Type*} {R : ℂ → X → Prop}

/-- The chart has the subspace topology of the original Banach locus. -/
def Chart.homeomorph (c : Chart I R) :
    locus c.U (fun z v => c.equations (z, v) = 0) ≃ₜ locus c.U R :=
  reconstructionHomeomorph c.U R _ c.read c.lift c.analytic_lift.continuousOn
    c.read_lift c.exact_locus

/-- Transition is the fixed linear projection for the target chart after the
holomorphic reconstruction for the source chart. -/
def Chart.transition (c d : Chart I R) (t : ℂ × c.E) : ℂ × d.E :=
  (t.1, d.read (c.lift t.1 t.2))

theorem Chart.transition_analytic (c d : Chart I R) :
    AnalyticOnNhd ℂ (c.transition d) (c.U ×ˢ univ) := by
  intro t ht
  exact ((ContinuousLinearMap.fst ℂ ℂ c.E).analyticAt t).prod
    ((d.read.analyticAt _).comp (joint_analytic c.analytic_lift t ht))

theorem Chart.transition_exact (c d : Chart I R) {z : ℂ} (hc : z ∈ c.U) (hd : z ∈ d.U)
    (v : c.E) (hv : c.equations (z, v) = 0) :
    d.equations (c.transition d (z, v)) = 0 ∧
      d.lift z (c.transition d (z, v)).2 = c.lift z v := by
  have hr := (c.exact_locus z hc _).mpr ⟨v, hv, rfl⟩
  obtain ⟨w, hw, he⟩ := (d.exact_locus z hd _).mp hr
  have hrw : d.read (c.lift z v) = w := by rw [he, d.read_lift]
  change d.equations (z, d.read (c.lift z v)) = 0 ∧ d.lift z (d.read (c.lift z v)) = c.lift z v
  rw [hrw]
  exact ⟨hw, he.symm⟩

theorem Chart.transition_self (c : Chart I R) (t : ℂ × c.E) : c.transition c t = t := by
  apply Prod.ext
  · rfl
  exact c.read_lift _ _

/-- Transition cocycles hold on the exact zero loci, on every chart overlap. -/
theorem Chart.transition_cocycle (c d e : Chart I R) {z : ℂ} (hc : z ∈ c.U) (hd : z ∈ d.U)
    (v : c.E) (hv : c.equations (z, v) = 0) :
    d.transition e (c.transition d (z, v)) = c.transition e (z, v) := by
  apply Prod.ext
  · rfl
  exact congrArg e.read (c.transition_exact d hc hd v hv).2

theorem Chart.transition_inverse (c d : Chart I R) {z : ℂ} (hc : z ∈ c.U) (hd : z ∈ d.U)
    (v : c.E) (hv : c.equations (z, v) = 0) :
    d.transition c (c.transition d (z, v)) = (z, v) :=
  (c.transition_cocycle d c hc hd v hv).trans (c.transition_self (z, v))

#print axioms Chart.homeomorph
#print axioms Chart.transition_analytic
#print axioms Chart.transition_exact
#print axioms Chart.transition_cocycle
#print axioms Chart.transition_inverse

end FinitenessAllLevelAnalyticAtlas
