module

public import QuantitativeArithmeticSmallLevelTwentySevenTheoryV4
public import QuantitativeArithmeticWeightedRecursionRigidityTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticAffineOrbitRigidity. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticAffineOrbitRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticAffineOrbitRigidity
open UpperHalfPlane QuantitativeArithmeticSmallLevelTwentySeven

/-- All descendants lie in this fixed cone of real affine maps. -/
def Orbit := {p : ℝ×ℝ // 1≤p.1 ∧ 0≤p.2 ∧ p.2≤2*(p.1-1)}
def origin : Orbit := ⟨(1,0),by norm_num⟩
instance : Nonempty Orbit := ⟨origin⟩
def height (p : Orbit) : ℝ := p.val.1

theorem height_pos (p : Orbit) : 0<height p := lt_of_lt_of_le zero_lt_one p.property.1

def move (r b : ℝ) (hr : 2≤r) (hb0 : 0≤b) (hb1 : b≤2*(r-1)) (p : Orbit) : Orbit :=
  ⟨(r*p.val.1,r*p.val.2+b),by
    rcases p.property with ⟨hp,hb,hbp⟩
    have hr0 : 0≤r := by linarith
    have hh := mul_le_mul_of_nonneg_left hbp hr0
    constructor
    · nlinarith
    constructor
    · positivity
    · nlinarith⟩

def point (z : ℍ) (p : Orbit) : ℍ := dilate p.val.1 p.val.2 (height_pos p) z

theorem point_origin (z : ℍ) : point z origin=z := by
  apply UpperHalfPlane.ext
  simp [point,origin,dilate_coe]

theorem point_move (r b : ℝ) (hr : 2≤r) (hb0 : 0≤b) (hb1 : b≤2*(r-1))
    (z : ℍ) (p : Orbit) :
    point z (move r b hr hb0 hb1 p)=dilate r b (by linarith) (point z p) := by
  apply UpperHalfPlane.ext
  simp only [point,move,dilate_coe,Complex.ofReal_mul,Complex.ofReal_add]
  ring

/-- Sectorial rapid decay is used only through bounded weighted norms on
these affine descendants. No eigenvalue restriction is needed. -/
theorem dilation_recursion_zero {I : Type*} [Fintype I]
    (D : ℍ → ℂ) (r b : I → ℝ) (c : I → ℂ)
    (hr : ∀ i, 2≤r i) (hb0 : ∀ i, 0≤b i) (hb1 : ∀ i, b i≤2*(r i-1))
    (hrec : ∀ z, D z=∑ i, c i*D (dilate (r i) (b i) (by linarith [hr i]) z))
    (hdecay : ∀ z L, BddAbove (Set.range (fun p : Orbit => ‖D (point z p)‖*height p^L))) :
    D=0 := by
  funext z
  have hh := QuantitativeArithmeticWeightedRecursionRigidity.expanding_recursion_zero
    (fun p : Orbit => D (point z p)) (fun i => move (r i) (b i) (hr i) (hb0 i) (hb1 i))
    c height height_pos (by
      intro i p
      change 2*p.val.1≤r i*p.val.1
      exact mul_le_mul_of_nonneg_right (hr i) (le_of_lt (height_pos p)))
    (by
      intro p
      simpa only [point_move] using hrec (point z p)) (hdecay z)
  have hz := congrFun hh origin
  simpa only [point_origin,Pi.zero_apply] using hz
#print axioms dilation_recursion_zero
end QuantitativeArithmeticAffineOrbitRigidity
end
end

/-! ## QuantitativeArithmeticAffineOrbitConstantV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticAffineOrbitRigidity
open UpperHalfPlane QuantitativeArithmeticSmallLevelTwentySeven

theorem height_unbounded (R : ℝ) : ∃ p : Orbit, R<height p := by
  let p : Orbit := ⟨(max 1 (R+1),0),by
    constructor
    · exact le_max_left _ _
    constructor
    · norm_num
    · have := le_max_left (1:ℝ) (R+1)
      linarith⟩
  refine ⟨p,?_⟩
  change R<max 1 (R+1)
  exact lt_of_lt_of_le (by linarith : R<R+1) (le_max_right _ _)

theorem dilation_recursion_constant {I : Type*} [Fintype I]
    (A : ℍ → ℂ) (r b : I → ℝ) (c : I → ℂ) (a : ℂ)
    (hr : ∀ i, 2≤r i) (hb0 : ∀ i, 0≤b i) (hb1 : ∀ i, b i≤2*(r i-1))
    (hrec : ∀ z, A z=∑ i, c i*A (dilate (r i) (b i) (by linarith [hr i]) z))
    (hdecay : ∀ z L, BddAbove (Set.range (fun p : Orbit => ‖A (point z p)-a‖*height p^L))) :
    A=fun _ => a := by
  funext z
  have hh := QuantitativeArithmeticWeightedRecursionRigidity.expanding_recursion_constant
    (fun p : Orbit => A (point z p)) (fun i => move (r i) (b i) (hr i) (hb0 i) (hb1 i))
    c a height height_pos (by
      intro i p
      change 2*p.val.1≤r i*p.val.1
      exact mul_le_mul_of_nonneg_right (hr i) (le_of_lt (height_pos p)))
    height_unbounded (by
      intro p
      simpa only [point_move] using hrec (point z p)) (hdecay z)
  have hz := congrFun hh origin
  simpa only [point_origin] using hz
#print axioms dilation_recursion_constant
end QuantitativeArithmeticAffineOrbitRigidity
end
end

/-! ## QuantitativeArithmeticAffineSectorDecayV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticAffineOrbitRigidity
open UpperHalfPlane QuantitativeArithmeticSmallLevelTwentySeven

theorem point_im (z : ℍ) (p : Orbit) : (point z p).im=height p*z.im := by
  change (((p.val.1:ℝ):ℂ)*(z:ℂ)+(p.val.2:ℂ)).im=p.val.1*z.im
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,UpperHalfPlane.coe_im]

theorem point_re (z : ℍ) (p : Orbit) : (point z p).re=height p*z.re+p.val.2 := by
  change (((p.val.1:ℝ):ℂ)*(z:ℂ)+(p.val.2:ℂ)).re=p.val.1*z.re+p.val.2
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,UpperHalfPlane.coe_re]

/-- The sector estimate needed by dilation rigidity, stated entirely as
bounds on the ordinary upper half-plane function. -/
def SectorDecay (D : ℍ → ℂ) : Prop :=
  ∀ (C y : ℝ), 0<y → ∀ L : ℕ, ∃ B : ℝ,
    ∀ w : ℍ, y≤w.im → |w.re|≤C*w.im → ‖D w‖*w.im^L≤B

theorem sector_orbit_bound (D : ℍ → ℂ) (h : SectorDecay D) (z : ℍ) (L : ℕ) :
    BddAbove (Set.range (fun p : Orbit => ‖D (point z p)‖*height p^L)) := by
  obtain ⟨B,hB⟩ := h ((|z.re|+2)/z.im) z.im z.im_pos L
  refine ⟨B/z.im^L,?_⟩
  rintro v ⟨p,rfl⟩
  have hp := p.property
  have hy : z.im≤(point z p).im := by
    rw [point_im]
    change z.im≤p.val.1*z.im
    nlinarith [z.im_pos]
  have hx : |(point z p).re|≤((|z.re|+2)/z.im)*(point z p).im := by
    rw [point_re,point_im]
    have hr0 : 0≤height p := le_of_lt (height_pos p)
    calc
      |height p*z.re+p.val.2|≤|height p*z.re|+|p.val.2| := abs_add_le _ _
      _ = height p*|z.re|+p.val.2 := by rw [abs_mul,abs_of_nonneg hr0,abs_of_nonneg hp.2.1]
      _ ≤ height p*(|z.re|+2) := by dsimp [height]; nlinarith [hp.2.2]
      _ = ((|z.re|+2)/z.im)*(height p*z.im) := by field_simp
  have hh := hB (point z p) hy hx
  rw [point_im,mul_pow] at hh
  apply (le_div_iff₀ (pow_pos z.im_pos L)).mpr
  nlinarith [hh]
#print axioms sector_orbit_bound
end QuantitativeArithmeticAffineOrbitRigidity
end
end

/-! ## QuantitativeArithmeticSectorDecayAlgebraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticAffineOrbitRigidity
open Complex UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem SectorDecay.add {F G : ℍ → ℂ} (hF : SectorDecay F) (hG : SectorDecay G) :
    SectorDecay (fun z => F z+G z) := by
  intro C y hy L
  obtain ⟨A,hA⟩ := hF C y hy L
  obtain ⟨B,hB⟩ := hG C y hy L
  refine ⟨A+B,?_⟩
  intro z hz hc
  have h := mul_le_mul_of_nonneg_right (norm_add_le (F z) (G z)) (pow_nonneg z.im_pos.le L)
  nlinarith [hA z hz hc,hB z hz hc]

theorem SectorDecay.bounded_mul {F G : ℍ → ℂ} (hF : SectorDecay F)
    (hG : ∀ y : ℝ,0<y → ∃ B : ℝ,0≤B ∧ ∀ z : ℍ,y≤z.im → ‖G z‖≤B) :
    SectorDecay (fun z => G z*F z) := by
  intro C y hy L
  obtain ⟨A,hA⟩ := hF C y hy L
  obtain ⟨B,hB,hB'⟩ := hG y hy
  refine ⟨B*A,?_⟩
  intro z hz hc
  rw [norm_mul]
  have hnorm : 0≤‖F z‖*z.im^L := by positivity
  calc
    ‖G z‖*‖F z‖*z.im^L = ‖G z‖*(‖F z‖*z.im^L) := by ring
    _ ≤ B*(‖F z‖*z.im^L) := mul_le_mul_of_nonneg_right (hB' z hz) hnorm
    _ ≤ B*A := mul_le_mul_of_nonneg_left (hA z hz hc) hB

theorem SectorDecay.translate {F : ℍ → ℂ} (hF : SectorDecay F) (b : ℝ) :
    SectorDecay (fun z => F (translation b • z)) := by
  intro C y hy L
  obtain ⟨B,hB⟩ := hF (C+|b|/y) y hy L
  refine ⟨B,?_⟩
  intro z hz hc
  have hi : (translation b • z).im=z.im := by
    change (((translation b • z : ℍ):ℂ)).im=z.im
    rw [translation_point]; simp
  have hr : (translation b • z).re=z.re+b := by
    change (((translation b • z : ℍ):ℂ)).re=z.re+b
    rw [translation_point]; simp
  have hbb : |b|≤(|b|/y)*z.im := by
    calc
      |b| = (|b|/y)*y := by field_simp
      _ ≤ (|b|/y)*z.im := mul_le_mul_of_nonneg_left hz (by positivity)
  have hh := abs_add_le z.re b
  have hzC : |(translation b • z).re|≤(C+|b|/y)*(translation b • z).im := by
    rw [hr,hi]; nlinarith
  simpa only [hi] using hB (translation b • z) (by rwa [hi]) hzC

theorem inverse_affine_multiplier (a b : ℝ) (ha : 0<a) (k : ℕ) :
    ∀ y : ℝ,0<y → ∃ B : ℝ,0≤B ∧ ∀ z : ℍ,y≤z.im →
      ‖(((a:ℂ)*(z:ℂ)+(b:ℂ))^k)⁻¹‖≤B := by
  intro y hy
  refine ⟨((a*y)⁻¹)^k,by positivity,?_⟩
  intro z hz
  rw [norm_inv,norm_pow,← inv_pow]
  apply pow_le_pow_left₀ (by positivity)
  apply inv_anti₀ (mul_pos ha hy)
  have hi : ((a:ℂ)*(z:ℂ)+(b:ℂ)).im=a*z.im := by simp [Complex.mul_im]
  calc
    a*y ≤ a*z.im := mul_le_mul_of_nonneg_left hz ha.le
    _ ≤ ‖(a:ℂ)*(z:ℂ)+(b:ℂ)‖ := by rw [← hi]; exact (le_abs_self _).trans (abs_im_le_norm _)
#print axioms SectorDecay.add
#print axioms SectorDecay.bounded_mul
#print axioms SectorDecay.translate
#print axioms inverse_affine_multiplier
end QuantitativeArithmeticAffineOrbitRigidity
end
end
