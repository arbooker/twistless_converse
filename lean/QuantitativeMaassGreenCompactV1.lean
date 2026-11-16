module

public import QuantitativeMaassGreenRectangleV1
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Every compact set strictly above height zero lies inside a finite open
rectangle whose lower side also has positive height. -/
theorem compact_upper_rectangle {K : Set Point} (hK : IsCompact K)
    (hpos : ∀ Z∈K, 0<Z.2) :
    ∃ l r a b : ℝ, l≤r ∧ 0<a ∧ a≤b ∧ K⊆Ioo l r ×ˢ Ioo a b := by
  obtain ⟨c,hc,hcK⟩ := hK.exists_forall_le' continuous_snd.continuousOn hpos
  obtain ⟨R,hR,hRK⟩ := hK.isBounded.exists_pos_norm_lt
  refine ⟨-R,R,c/2,max R c+1,by linarith,by linarith,?_,?_⟩
  · have := le_max_right R c
    linarith
  · intro Z hZ
    have hnorm := hRK Z hZ
    have hx : |Z.1|<R := lt_of_le_of_lt (norm_fst_le Z) hnorm
    have hy : Z.2<R := lt_of_le_of_lt (le_trans (le_abs_self Z.2) (norm_snd_le Z)) hnorm
    have hz := hcK Z hZ
    have hb := le_max_left R c
    exact ⟨abs_lt.mp hx,by constructor <;> linarith⟩

/-- Removing the rectangle is legitimate because both the test and its
first derivatives vanish outside its topological support. -/
theorem green_compact_of_rectangle (l r a b : ℝ) (hlr : l≤r)
    (ha : 0<a) (hab : a≤b) {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hK : tsupport u⊆Ioo l r ×ˢ Ioo a b) :
    (∫ Z : Point, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2)=
      ∫ Z : Point, star (X u Z)*X v Z+star (Y u Z)*Y v Z := by
  have hz (Z : Point) (hZ : Z∉Ioo l r ×ˢ Ioo a b) : u Z=0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hZ (hK h))
  have hg := green_rectangle l r a b hlr ha hab hu hv
    (fun y => hz (l,y) (by simp)) (fun y => hz (r,y) (by simp))
    (fun x => hz (x,a) (by simp)) (fun x => hz (x,b) (by simp))
  have hn (Z : Point) (hZ : Z∉Ioc l r ×ˢ Ioc a b) : Z∉tsupport u := by
    intro h
    exact hZ ⟨⟨(hK h).1.1,(hK h).1.2.le⟩,⟨(hK h).2.1,(hK h).2.2.le⟩⟩
  have he (Z : Point) (hZ : Z∉Ioc l r ×ˢ Ioc a b) :
      star (X u Z)*X v Z+star (Y u Z)*Y v Z=0 := by
    have hd := fderiv_of_notMem_tsupport ℝ (hn Z hZ)
    simp [X,Y,dir,D,hd]
  have hl (Z : Point) (hZ : Z∉Ioc l r ×ˢ Ioc a b) :
      star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2=0 := by
    simp [image_eq_zero_of_notMem_tsupport (hn Z hZ)]
  unfold greenRectangle at hg
  rw [Measure.prod_restrict] at hg
  change (∫ Z in Ioc l r ×ˢ Ioc a b, _) = ∫ Z in Ioc l r ×ˢ Ioc a b, _ at hg
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hl,
    setIntegral_eq_integral_of_forall_compl_eq_zero he] at hg
  exact hg

/-- Actual ambient Green identity for a compact test supported in the
positive-height chart. No compactness or periodicity of the second function
is required. -/
theorem green_compact {u v : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2})
    (hv : ContDiffOn ℝ ∞ v {Z | 0<Z.2})
    (hc : HasCompactSupport u) (hp : ∀ Z∈tsupport u, 0<Z.2) :
    (∫ Z : Point, star (u Z)*hyperbolic v Z/(Z.2:ℂ)^2)=
      ∫ Z : Point, star (X u Z)*X v Z+star (Y u Z)*Y v Z := by
  obtain ⟨l,r,a,b,hlr,ha,hab,hK⟩ := compact_upper_rectangle hc hp
  exact green_compact_of_rectangle l r a b hlr ha hab hu hv hK

#print axioms green_compact

end QuantitativeMaass
