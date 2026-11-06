module

public import QuantitativeArithmeticSmallLevelTwentySixMMPOriginalChartV1
public import SmallLevelTwentySixExceptionalSevenPhysicalTheoryV4
public import SmallLevelTwentySixMMPPariExceptionalIdentitiesV1
public import SmallLevelTwentySixRootTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelTwentySixMMPExceptional. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPExceptionalBranchesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPExceptional
open SmallLevelTwentySixMMPPari SmallLevelTwentySixMMPPariExceptional

/-- The exceptional constant locus of the genuine small MMP rows is
contained in the two already certified exceptional factor loci. -/
theorem exceptional_branches (x y z w a b θ : ℂ) (hx : x≠0)
    (hc : c00 x y z w a b=0)
    (h0 : c00 x y z w a b+c01 x y z w a b*θ=0)
    (h1 : c10 x y z w a b+c11 x y z w a b*θ=0)
    (h3 : c30 x y z w a b+c31 x y z w a b*θ=0) :
    SmallLevelTwentySixPariFinalFactors.factor6 x=0 ∨
      SmallLevelTwentySixExceptionalCurve.extraFactor7 x y=0 := by
  have hx1 : x-1≠0 := by
    intro h
    have he : x=1 := sub_eq_zero.mp h
    subst x
    have he : c00 1 y z w a b=(-19/10:ℂ) := by unfold c00; ring
    rw [he] at hc
    norm_num at hc
  have hx2 : x-2≠0 := by
    intro h
    have he : x=2 := sub_eq_zero.mp h
    subst x
    have he : c00 2 y z w a b=(-52/15:ℂ) := by unfold c00; ring
    rw [he] at hc
    norm_num at hc
  by_cases ht : θ=0
  · subst θ
    simp only [mul_zero,add_zero] at h1 h3
    have e0 := identity0 x y z w a b 0
    rw [binding0_1,binding0_3,h1,h3,mul_zero,mul_zero,zero_add] at e0
    have e1 := identity1 x y z w a b 0
    rw [binding1_1,binding1_3,hc,←e0,mul_zero,mul_zero,zero_add] at e1
    rw [factorization0] at e1
    right
    exact (mul_eq_zero.mp e1.symm).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) hx1) hx)
  · have h01 : c01 x y z w a b=0 := by
      rw [hc,zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right ht
    have e2 := identity2 x y z w a b θ
    rw [binding2_1,binding2_3,h1,h3,mul_zero,mul_zero,zero_add] at e2
    have e3 := identity3 x y z w a b θ
    rw [binding3_1,binding3_3,h01,←e2,mul_zero,mul_zero,zero_add] at e3
    have e4 := identity4 x y z w a b θ
    rw [binding4_1,binding4_3,hc,←e3,mul_zero,mul_zero,zero_add] at e4
    rw [factorization1] at e4
    left
    exact (mul_eq_zero.mp e4.symm).resolve_left
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hx2)) hx1) hx)

#print axioms exceptional_branches
end QuantitativeArithmeticSmallLevelTwentySixMMPExceptional
end
end

/-! ## QuantitativeArithmeticSmallLevelTwentySixMMPOriginalExceptionalV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentySixMMPExceptional
open QuantitativeArithmeticSevenLaurentRows
open SmallLevelTwentySixGermSources SmallLevelPrimeRates
open SmallLevelTwentySixGrid (phase badParameter)
open QuantitativeArithmeticSmallLevelTwentySixMMPPrimitive SmallLevelTwentySixMMPPari
open QuantitativeArithmeticSmallLevelTwentySixMMPOriginalChart

/-- The first-chart exceptional constant cannot vanish at an original MMP
pole. Only the small genuine rows and existing physical root exclusions enter;
the large syzygies are unnecessary for this exceptional case. -/
theorem original_constant_ne_zero {m : ℕ} {f : ℕ → ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (T : SmallLevelTwentySixGrid.PoleSystem m f ε)
    (s u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hshift : ∀ n : ℕ,0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) (hs1 : s≠((2*m:ℕ):ℂ)+1)
    (hη : phase m ε= -u*v) (hs2 : badParameter f 2= -u) (hs13 : badParameter f 13=v)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s<0) :
    SmallLevelTwentySixPariFirstChart.constantTerm
      (u*parameter 2 m s) ((parameter 3 m s)^2)≠0 := by
  intro hc
  obtain ⟨θ,hθ⟩ := original_first_chart S T s u v hu hv hshift hs hs1 hη hs2 hs13
    hpole (fun i : Fin 0 => Fin.elim0 i)
    (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
  have h0 := hθ (Sum.inl 0)
  have h1 := hθ (Sum.inl 1)
  have h3 := hθ (Sum.inl 3)
  change eval _ _ _ _ _ _ 1 _ (primitiveRows 0)=0 at h0
  change eval _ _ _ _ _ _ 1 _ (primitiveRows 1)=0 at h1
  change eval _ _ _ _ _ _ 1 _ (primitiveRows 3)=0 at h3
  rw [small_row_0] at h0
  rw [small_row_1] at h1
  rw [small_row_3] at h3
  norm_num only [ite_true,ite_false,mul_one] at h0 h1 h3
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hun : ‖u‖=1 := by rcases hu with rfl|rfl <;> norm_num
  have hX := mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) s)
  have hcc : c00 (u*parameter 2 m s) ((parameter 3 m s)^2)
      (v*parameter 13 m s) ((parameter 5 m s)^2)
      (badParameter f 3*parameter 3 m s) (badParameter f 5*parameter 5 m s)=0 := by
    rw [SmallLevelTwentySixMMPPariExceptional.constant_binding]
    exact hc
  have hb := exceptional_branches _ _ _ _ _ _ θ hX hcc h0 h1 h3
  apply SmallLevelTwentySixExceptionalSevenPhysical.no_signed_exceptional_branches (s-(m:ℂ)) u hun
  · rw [SmallLevelTwentySixRoot.parameter_three_squared] at hc
    simpa only [parameter,Nat.cast_ofNat] using hc
  · rw [SmallLevelTwentySixRoot.parameter_three_squared] at hb
    simpa only [parameter,Nat.cast_ofNat] using hb

#print axioms original_constant_ne_zero
end QuantitativeArithmeticSmallLevelTwentySixMMPExceptional
end
end
