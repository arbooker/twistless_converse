module

public import AsymptoticReturningBranchTraceV1
public import AsymptoticRationalBranchesV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane MeasureTheory Filter Set

/-- Half-open strip representatives cannot differ by a nonzero integer. -/
theorem translate_eq_iff_of_strip (z u : ℍ) (hz : z∈AsymptoticMassTransport.strip)
    (hu : u∈AsymptoticMassTransport.strip) (n : ℤ) :
    translate z n=u ↔ n=0 ∧ z=u := by
  constructor
  · intro h
    have hr := congrArg UpperHalfPlane.re h
    change z.re+(n:ℝ)=u.re at hr
    have hz' : 0≤z.re ∧ z.re<1 := hz
    have hu' : 0≤u.re ∧ u.re<1 := hu
    have hn₁ : (n:ℝ)<1 := by linarith
    have hn₂ : (-1:ℝ)<n := by linarith
    have hn₁' : n<1 := by exact_mod_cast hn₁
    have hn₂' : (-1:ℤ)<n := by exact_mod_cast hn₂
    have hn : n=0 := by omega
    refine ⟨hn,?_⟩
    subst n
    simpa only [translate,Int.cast_zero,add_zero] using h
  · rintro ⟨rfl,rfl⟩
    apply UpperHalfPlane.ext
    simp only [translate,Int.cast_zero,add_zero]

/-- One conull set identifies cylinder returns with identity labels for
all rational words whose input and output both lie in the strip. -/
theorem ae_strip_return_iff_identity :
    ∀ᵐ z : ℍ ∂volume, ∀ g : AsymptoticRationalGroup.Group,
      z∈AsymptoticMassTransport.strip → g • z∈AsymptoticMassTransport.strip →
      ((∃ n : ℤ,translate (g • z) n=z) ↔ g=1) := by
  filter_upwards [AsymptoticRationalGroup.ae_free] with z hz g hs ht
  constructor
  · rintro ⟨n,hn⟩
    exact hz g ((translate_eq_iff_of_strip (g • z) z ht hs n).mp hn).2
  · intro hg
    subst g
    refine ⟨0,?_⟩
    simp only [one_smul,translate,Int.cast_zero,add_zero]

/-- A nonidentity rational label supplies the nonreturn hypothesis in
the proved branch trace estimate, after retaining both strip endpoints. -/
theorem ae_nonidentity_strip_nonreturn (g : AsymptoticRationalGroup.Group) (hg : g≠1)
    (S : Set ℍ) (hstrip : ∀ᵐ z ∂((volume : Measure ℍ).restrict S),
      z∈AsymptoticMassTransport.strip ∧ g • z∈AsymptoticMassTransport.strip) :
    ∀ᵐ z ∂((volume : Measure ℍ).restrict S), ∀ n : ℤ,translate (g • z) n≠z := by
  filter_upwards [ae_restrict_of_ae ae_strip_return_iff_identity,hstrip] with z hz hs n hn
  exact hg ((hz g hs.1 hs.2).mp ⟨n,hn⟩)

#print axioms translate_eq_iff_of_strip
#print axioms ae_strip_return_iff_identity
#print axioms ae_nonidentity_strip_nonreturn

end AsymptoticUnweightedKernel
