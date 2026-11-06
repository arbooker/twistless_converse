module

public import SmallLevelTwentyOneReflectionAlgebraV1
public import SmallLevelTwentyOneChiFiveObstructionTheoryV4
public import SmallLevelTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex
open QuantitativeArithmeticSmallLevelNineteen (heckeScalar oppositeScalar)

/-- The exceptional Hecke2 denominator is the explicit quadratic in
2^(s-1), multiplied by a nowhere-zero exponential. -/
theorem exceptional_denominator {f : ℕ → ℂ}
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) (s : ℂ) :
    2*((2:ℂ)^(s-1))^2*denominator 2 f s=
      2*((2:ℂ)^(s-1))^2-3*(2:ℂ)^(s-1)+2 := by
  have hfirst : heckeScalar 2 f s= -(3/2:ℂ)*(2:ℂ)^(1-s) := by
    have h := SmallLevelTaylor.hecke_first_scalar (by decide : 0<2) 1 (f 2) s
    norm_num only [Nat.cast_ofNat,mul_one,Nat.cast_one] at h
    convert h using 1 <;> norm_num [heckeScalar,ha]
  have hsecond : oppositeScalar 2 s=1+((2:ℂ)^(1-s))^2 := by
    have h := SmallLevelTaylor.hecke_second_scalar (by decide : 0<2) 1 s
    norm_num only [Nat.cast_ofNat,mul_one,Nat.cast_one] at h
    simpa only [oppositeScalar,show (2:ℂ)^2=4 by norm_num] using
      congrArg (fun z : ℂ => 1+z) h
  have ht : (2:ℂ)^(1-s)=((2:ℂ)^(s-1))⁻¹ := by
    rw [← Complex.cpow_neg]
    congr 1
    ring
  have hx : (2:ℂ)^(s-1)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [denominator,hfirst,hsecond,ht]
  field_simp
  ring

theorem quadratic_root_geometry {u : ℂ} (hu : 2*u^2-3*u+2=0) :
    u.re=3/4 ∧ u.im≠0 ∧ ‖u‖=1 := by
  have hr := congrArg Complex.re hu
  have hi := congrArg Complex.im hu
  norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
  have him : u.im≠0 := by
    intro hz
    rw [hz] at hr
    nlinarith [sq_nonneg (u.re-3/4)]
  have hre : u.re=3/4 := by
    have he : (4*u.re-3)*u.im=0 := by nlinarith
    have he' := (mul_eq_zero.mp he).resolve_right him
    linarith
  refine ⟨hre,him,?_⟩
  have hsq : ‖u‖^2=1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    rw [hre] at hr ⊢
    nlinarith
  nlinarith [norm_nonneg u]

theorem exceptional_denominator_root {f : ℕ → ℂ}
    (ha : (Real.sqrt 2:ℂ)*f 2= -(3/2:ℂ)) {s : ℂ}
    (hs : denominator 2 f s=0) :
    let u := (2:ℂ)^(s-1)
    2*u^2-3*u+2=0 ∧ u.re=3/4 ∧ u.im≠0 ∧ ‖u‖=1 := by
  have he := exceptional_denominator ha s
  rw [hs,mul_zero] at he
  exact ⟨he.symm,quadratic_root_geometry he.symm⟩

#print axioms exceptional_denominator
#print axioms quadratic_root_geometry
#print axioms exceptional_denominator_root
end SmallLevelTwentyOneChiFive
