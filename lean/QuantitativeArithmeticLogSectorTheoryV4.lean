module

public import QuantitativeArithmeticAffineOrbitRigidityTheoryV4
public import QuantitativeArithmeticCuspRemainderTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticLogSector. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSectorExtensionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticLogSector
open Complex

theorem extend_flat_sector (F : ℂ → ℂ)
    (hg : ∀ a b : ℝ,0<a → a<b → b<Real.pi →
      ∃ C B : ℝ,0≤C ∧ 0≤B ∧ ∀ z : ℂ,a≤z.re → z.re≤b → ‖F (logRay z)‖≤C*Real.exp (B*|z.im|))
    (hf : ∀ δ : ℝ,0<δ → δ<Real.pi/2 → ∀ n : ℕ,
      ∃ C : ℝ,0≤C ∧ ∀ w : ℂ,w≠0 → ‖w‖≤1 → δ≤arg w → arg w≤Real.pi-δ → ‖F w‖≤C*‖w‖^n)
    (R δ : ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ w : ℂ,w≠0 → ‖w‖≤R → δ≤arg w → arg w≤Real.pi-δ → ‖F w‖≤C*‖w‖^n := by
  obtain ⟨C,hC,hf⟩ := hf δ hδ hδπ n
  obtain ⟨D,B,hD,hB,hg⟩ := hg δ (Real.pi-δ) hδ (by linarith) (by linarith)
  refine ⟨max C (D*Real.exp (B*|Real.log R|)),hC.trans (le_max_left _ _),?_⟩
  intro w hw hwR hwa hwb
  by_cases hw1 : ‖w‖≤1
  · exact (hf w hw hw1 hwa hwb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg _) n))
  · have hw1' : 1<‖w‖ := lt_of_not_ge hw1
    obtain ⟨he,hre,him⟩ := logarithmic_coordinates w hw
    have hh := hg (-I*log w) (by rwa [hre]) (by rwa [hre])
    rw [he,him,abs_neg,abs_of_nonneg (Real.log_nonneg hw1'.le)] at hh
    have hl : Real.log ‖w‖≤|Real.log R| :=
      (Real.log_le_log (norm_pos_iff.mpr hw) hwR).trans (le_abs_self _)
    have hb := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hB)
    have hn : 1≤‖w‖^n := one_le_pow₀ hw1'.le
    calc
      ‖F w‖ ≤ D*Real.exp (B*|Real.log R|) := hh.trans (mul_le_mul_of_nonneg_left hb hD)
      _ ≤ max C (D*Real.exp (B*|Real.log R|)) := le_max_right _ _
      _ ≤ max C (D*Real.exp (B*|Real.log R|))*‖w‖^n := le_mul_of_one_le_right (hC.trans (le_max_left _ _)) hn

/-- A bound on the slope gives an explicit closed angular sector. -/
theorem cone_angles (C : ℝ) : ∃ δ : ℝ,0<δ ∧ δ<Real.pi/2 ∧
    ∀ w : ℂ,0<w.im → |w.re|≤C*w.im → δ≤arg w ∧ arg w≤Real.pi-δ := by
  let t : ℝ := 1/(|C|+1)
  have ht : 0<t := by dsimp [t]; positivity
  let δ := min (t/2) (Real.pi/4)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  refine ⟨δ,hδ,lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos]),?_⟩
  intro w hw hc
  have hn : 0<‖w‖ := norm_pos_iff.mpr (by intro h; simp [h] at hw)
  have hb : ‖w‖≤(|C|+1)*w.im := by
    have hh := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_pos hw] at hh
    have hcc := mul_le_mul_of_nonneg_right (le_abs_self C) hw.le
    nlinarith
  have hsin : t≤Real.sin (arg w) := by
    rw [sin_arg]
    dsimp [t]
    apply (div_le_div_iff₀ (by positivity : 0 < |C|+1) hn).mpr
    nlinarith
  have ha : 0≤arg w := arg_nonneg_iff.mpr hw.le
  have hp : 0≤Real.pi-arg w := sub_nonneg.mpr (arg_le_pi w)
  have hleft := Real.sin_le ha
  have hright := Real.sin_le hp
  rw [Real.sin_pi_sub] at hright
  have hd : δ≤t/2 := min_le_left _ _
  constructor <;> linarith
#print axioms extend_flat_sector
#print axioms cone_angles
end QuantitativeArithmeticLogSector
end
end

/-! ## QuantitativeArithmeticInverseConeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticLogSector
open Complex UpperHalfPlane QuantitativeArithmeticAffineOrbitRigidity

theorem negative_inverse_geometry (d : ℂ) (hd : 0<d.im) (C : ℝ)
    (hc : |d.re|≤C*d.im) :
    0<(-d⁻¹).im ∧ |(-d⁻¹).re|≤C*(-d⁻¹).im ∧ ‖-d⁻¹‖≤(d.im)⁻¹ := by
  have hn : d≠0 := by intro h; simp [h] at hd
  have hs : 0<normSq d := normSq_pos.mpr hn
  have he : (-d⁻¹).im=d.im/normSq d := by simp only [Complex.neg_im,Complex.inv_im]; ring
  have hr : (-d⁻¹).re= -d.re/normSq d := by simp only [Complex.neg_re,Complex.inv_re]; ring
  refine ⟨by rw [he]; positivity,?_,?_⟩
  · rw [hr,he,abs_div,abs_neg,abs_of_pos hs,← mul_div_assoc]
    exact div_le_div_of_nonneg_right hc hs.le
  · rw [norm_neg,norm_inv]
    apply inv_anti₀ hd
    exact (le_abs_self d.im).trans (abs_im_le_norm d)

theorem affine_cone_geometry (a b C y : ℝ) (ha : 0<a) (hy : 0<y)
    (z : ℍ) (hzy : y≤z.im) (hzC : |z.re|≤C*z.im) :
    let d : ℂ := (a:ℂ)*(z:ℂ)+(b:ℂ)
    0<(-d⁻¹).im ∧ |(-d⁻¹).re|≤(|C|+|b|/(a*y))*(-d⁻¹).im ∧
      ‖-d⁻¹‖≤(a*z.im)⁻¹ ∧ ‖-d⁻¹‖≤(a*y)⁻¹ := by
  let d : ℂ := (a:ℂ)*(z:ℂ)+(b:ℂ)
  have hi : d.im=a*z.im := by simp [d,Complex.mul_im]
  have hr : d.re=a*z.re+b := by simp [d,Complex.mul_re]
  have hdy : 0<d.im := by rw [hi]; positivity
  have hc : |d.re|≤(|C|+|b|/(a*y))*d.im := by
    rw [hr,hi]
    have h1 : |a*z.re+b|≤a*|z.re|+|b| := by simpa [abs_mul,abs_of_pos ha] using abs_add_le (a*z.re) b
    have h2 := mul_le_mul_of_nonneg_left hzC ha.le
    have h3 := mul_le_mul_of_nonneg_right (le_abs_self C) (mul_pos ha z.im_pos).le
    have h4 : |b|≤(|b|/(a*y))*(a*z.im) := by
      calc
        |b| = (|b|/(a*y))*(a*y) := by field_simp
        _ ≤ (|b|/(a*y))*(a*z.im) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hzy ha.le) (by positivity)
    nlinarith
  obtain ⟨hp,hc',hn⟩ := negative_inverse_geometry d hdy _ hc
  rw [hi] at hn
  exact ⟨hp,hc',hn,hn.trans (inv_anti₀ (mul_pos ha hy) (mul_le_mul_of_nonneg_left hzy ha.le))⟩

theorem inverse_affine_decay (F : ℂ → ℂ)
    (hf : ∀ R δ : ℝ,0<δ → δ<Real.pi/2 → ∀ n : ℕ,
      ∃ B : ℝ,0≤B ∧ ∀ w : ℂ,w≠0 → ‖w‖≤R → δ≤arg w → arg w≤Real.pi-δ → ‖F w‖≤B*‖w‖^n)
    (a b : ℝ) (ha : 0<a) :
    SectorDecay (fun z : ℍ => F (-((a:ℂ)*(z:ℂ)+(b:ℂ))⁻¹)) := by
  intro C y hy L
  obtain ⟨δ,hδ,hδπ,hangle⟩ := cone_angles (|C|+|b|/(a*y))
  obtain ⟨B,hB,hB'⟩ := hf ((a*y)⁻¹) δ hδ hδπ L
  refine ⟨B*(a⁻¹)^L,?_⟩
  intro z hzy hzC
  obtain ⟨hp,hc,hn,hnR⟩ := affine_cone_geometry a b C y ha hy z hzy hzC
  obtain ⟨hl,hu⟩ := hangle _ hp hc
  have h := hB' _ (by intro hh; simp [hh] at hp) hnR hl hu
  have hnL := pow_le_pow_left₀ (norm_nonneg _) hn L
  have hb := mul_le_mul_of_nonneg_left hnL hB
  calc
    ‖F (-((a:ℂ)*(z:ℂ)+(b:ℂ))⁻¹)‖*z.im^L ≤ (B*((a*z.im)⁻¹)^L)*z.im^L :=
      mul_le_mul_of_nonneg_right (h.trans hb) (pow_nonneg z.im_pos.le L)
    _ = B*(a⁻¹)^L := by
      rw [mul_inv_rev,mul_pow]
      calc
        B*(z.im⁻¹^L*(a⁻¹)^L)*z.im^L = B*(a⁻¹)^L*(z.im⁻¹*z.im)^L := by rw [mul_pow]; ring
        _ = B*(a⁻¹)^L := by rw [inv_mul_cancel₀ z.im_pos.ne',one_pow,mul_one]
#print axioms negative_inverse_geometry
#print axioms affine_cone_geometry
#print axioms inverse_affine_decay
end QuantitativeArithmeticLogSector
end
end
