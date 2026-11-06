module

public import AsymptoticRationalFreenessV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRationalGroup

open MeasureTheory UpperHalfPlane Filter
open scoped MatrixGroups

local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

noncomputable def rationalMap : GL (Fin 2) ℚ →* PGL(2, ℝ) :=
  Matrix.ProjGenLinGroup.mk.comp (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ))

noncomputable def rationalImage : Subgroup PGL(2, ℝ) := rationalMap.range

instance rationalImage_countable : Countable rationalImage :=
  rationalMap.rangeRestrict_surjective.countable

noncomputable def rationalSign : rationalImage →* SignTypeˣ :=
  Matrix.ProjGenLinGroup.signDet.comp rationalImage.subtype

/-- Positive rational projective transformations, realized faithfully
inside real PGL. Taking the image removes scalar representatives. -/
noncomputable abbrev Group := rationalSign.ker

instance group_countable : Countable Group := inferInstanceAs (Countable rationalSign.ker)

theorem pgl_measurePreserving (g : PGL(2, ℝ)) :
    MeasurePreserving (fun z : ℍ => g • z) volume volume := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    simpa only [pglMk_smul] using measurePreserving_smul g (volume : Measure ℍ)

theorem measurePreserving (g : Group) :
    MeasurePreserving (fun z : ℍ => g • z) volume volume :=
  pgl_measurePreserving g.val.val

theorem representative_positive (g : Group) {q : GL (Fin 2) ℚ}
    (hq : rationalMap q=g.val.val) :
    0<(AsymptoticRationalFreeness.realMatrix q).det.val := by
  have he : Matrix.ProjGenLinGroup.signDet (rationalMap q)=1 := by
    rw [hq]
    exact g.property
  have hv := congrArg (fun u : SignTypeˣ => u.val) he
  change SignType.sign (AsymptoticRationalFreeness.realMatrix q).det.val=1 at hv
  exact sign_eq_one_iff.mp hv

/-- The positive rational projective group acts freely outside one
hyperbolic null set. This is the actual group used for the regular orbit
representation, not a family with repeated scalar matrix labels. -/
theorem ae_free : ∀ᵐ z : ℍ ∂volume, ∀ g : Group, g • z=z → g=1 := by
  filter_upwards [AsymptoticRationalFreeness.ae_rational_returns_are_scalar] with z hz g hfix
  obtain ⟨q,hq⟩ := g.val.property
  have hq' : rationalMap q=g.val.val := hq
  have hact : AsymptoticRationalFreeness.realMatrix q • z=z := by
    have hh : rationalMap q • z=z := by rw [hq']; exact hfix
    simpa only [rationalMap,MonoidHom.comp_apply,pglMk_smul,
      AsymptoticRationalFreeness.realMatrix] using hh
  have hc := hz q (representative_positive g hq') hact
  have hone : rationalMap q=1 := Matrix.ProjGenLinGroup.mk_eq_one.mpr hc
  apply Subtype.ext
  apply Subtype.ext
  exact hq'.symm.trans hone

/-- Distinct projective labels give distinct points on every free orbit. -/
theorem ae_orbit_injective :
    ∀ᵐ z : ℍ ∂volume, Function.Injective (fun g : Group => g • z) := by
  filter_upwards [ae_free] with z hz
  intro g h hgh
  change g • z=h • z at hgh
  have he : (h⁻¹*g) • z=z := by rw [mul_smul,hgh,inv_smul_smul]
  exact (inv_mul_eq_one.mp (hz _ he)).symm

#print axioms measurePreserving
#print axioms ae_free
#print axioms ae_orbit_injective

end AsymptoticRationalGroup
