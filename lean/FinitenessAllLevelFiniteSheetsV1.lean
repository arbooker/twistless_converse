module

public import FinitenessAllLevelAmbientGraphsV1
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Properness combines the finitely many local graphs into an exhaustive,
disjoint family over one common neighborhood. No sheets can arrive from
outside the chosen neighborhoods of the fiber. -/
theorem finite_sheets (R : ℂ → X → Prop)
    (hp : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (w : ℂ) (hf : {x | R w x}.Finite)
    (hg : ∀ x, R w x → AmbientGraphAt R w x) :
    ∃ F : {x | R w x} → ℂ → X,
      (∀ x, F x w = x.val) ∧ (∀ x, AnalyticAt ℂ (F x) w) ∧
      ∀ᶠ z in 𝓝 w, (∀ x, R z (F x z)) ∧
        Function.Injective (fun x => F x z) ∧ ∀ y, R z y → ∃ x, F x z = y := by
  classical
  let := hf.to_subtype
  have hdata (x : {x | R w x}) := hg x.val x.property
  choose F hFw hFa hFs hFu using hdata
  have hcover : ∀ᶠ z in 𝓝 w, ∀ y, R z y → ∃ x, F x z = y := by
    have he := hp.isClosedMap.eventually_nhds_fiber
      (p := fun t : {t : ℂ × X | R t.1 t.2} => ∃ x, F x t.val.1 = t.val.2) w
    have hh : ∀ᶠ z in 𝓝 w, ∀ t : {t : ℂ × X | R t.1 t.2},
        t ∈ (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1) ⁻¹' {z} →
          ∃ x, F x t.val.1 = t.val.2 := by
      apply he
      intro t ht
      have ht' : t.val.1 = w := ht
      let x : {x | R w x} := ⟨t.val.2, ht' ▸ t.property⟩
      have hu := hFu x
      have hbase : (w, x.val) = t.val := Prod.ext ht'.symm rfl
      rw [hbase] at hu
      have hnear := continuous_subtype_val.continuousAt.tendsto.eventually hu
      filter_upwards [hnear] with u hu'
      exact ⟨x, (hu'.mp u.property).symm⟩
    filter_upwards [hh] with z hz y hy
    exact hz ⟨(z, y), hy⟩ rfl
  have hsep : ∀ᶠ z in 𝓝 w, Function.Injective (fun x => F x z) := by
    have hpair (x y : {x | R w x}) : ∀ᶠ z in 𝓝 w, F x z = F y z → x = y := by
      by_cases hxy : x = y
      · exact Eventually.of_forall (fun _ _ => hxy)
      · have hn : F x w - F y w ≠ 0 := by
          rw [hFw x, hFw y]
          exact sub_ne_zero.mpr (fun h => hxy (Subtype.ext h))
        have he := ((hFa x).continuousAt.sub (hFa y).continuousAt).eventually_ne hn
        filter_upwards [he] with z hz heq
        exact False.elim (hz (sub_eq_zero.mpr heq))
    exact Filter.eventually_all.mpr (fun x => Filter.eventually_all.mpr (hpair x))
  refine ⟨F, hFw, hFa, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hFs, hsep, hcover] with z hs hi hc
  exact ⟨hs, hi, hc⟩

/-- The cardinality of the actual fiber is locally constant at a parameter
where all its points have ambient holomorphic graphs. -/
theorem fiber_card_eventually (R : ℂ → X → Prop)
    (hp : IsProperMap (fun t : {t : ℂ × X | R t.1 t.2} => t.val.1))
    (w : ℂ) (hf : {x | R w x}.Finite)
    (hg : ∀ x, R w x → AmbientGraphAt R w x) :
    ∀ᶠ z in 𝓝 w, Nat.card {x | R z x} = Nat.card {x | R w x} := by
  obtain ⟨F, _, _, he⟩ := finite_sheets R hp w hf hg
  filter_upwards [he] with z hz
  let f : {x | R w x} → {x | R z x} := fun x => ⟨F x z, hz.1 x⟩
  have hi : Function.Injective f := fun x y h => hz.2.1 (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hz.2.2 y.val y.property
    exact ⟨x, Subtype.ext hx⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm

#print axioms finite_sheets
#print axioms fiber_card_eventually

end FinitenessAllLevelPolynomialPresentation
