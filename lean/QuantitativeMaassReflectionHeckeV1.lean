module

public import QuantitativeMaassReflectionCuspV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology MatrixGroups InnerProductSpace BigOperators

namespace QuantitativeMaass

/-- Actual Hecke branches are permuted by reflection, with the negative
residue corrected by the genuine period N. -/
theorem cuspHeckeSum_reflection (N p : ℕ) [Fact p.Prime] (f : ℍ → ℂ)
    (hinv : ∀ γ : gamma N,∀ z : ℍ,f (γ.val•z)=f z) (z : ℍ) :
    cuspHeckeSum N p (fun w => f (J•w)) z=cuspHeckeSum N p f (J•z) := by
  rcases z with ⟨⟨x,y⟩,hy⟩
  change cuspHeckeSum N p (fun w => f (J•w)) (horocyclePoint x y hy)=
    cuspHeckeSum N p f (J•horocyclePoint x y hy)
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hyp : 0<y/(p:ℝ) := div_pos hy hp
  have hperiod : Function.Periodic (fun t => f (horocyclePoint t (y/p) hyp)) (N:ℝ) := by
    simpa only [map_one,one_smul] using cusp_chart_periodic N 1 f hinv (y/p) hyp
  have hpair (u : ZMod p) :
      f (horocyclePoint (-((x+(N:ℝ)*u.val)/p)) (y/p) hyp)=
      f (horocyclePoint ((-x+(N:ℝ)*(-u).val)/p) (y/p) hyp) := by
    by_cases hu : u=0
    · subst u
      simp only [neg_zero,ZMod.val_zero,Nat.cast_zero,mul_zero,add_zero,neg_div]
    · let : NeZero u := ⟨hu⟩
      have hv : ((-u).val:ℝ)=(p:ℝ)-(u.val:ℝ) := by
        rw [ZMod.val_neg_of_ne_zero,Nat.cast_sub (le_of_lt (ZMod.val_lt u))]
      have hx : (-x+(N:ℝ)*(-u).val)/p= -((x+(N:ℝ)*u.val)/p)+N := by
        rw [hv]
        field_simp [hp.ne']
        ring
      rw [hx]
      exact (hperiod _).symm
  simp only [cuspHeckeSum,Fintype.sum_option,reflection_horocyclePoint,
    cuspBranchGL_none_point,cuspBranchGL_some_point,mul_neg]
  congr 1
  simp_rw [hpair]
  exact Equiv.sum_comp (Equiv.neg (ZMod p))
    (fun u => f (horocyclePoint ((-x+(N:ℝ)*u.val)/p) (y/p) hyp))

theorem normalizedCuspHecke_reflection (N p : ℕ) [Fact p.Prime] (f : ℍ → ℂ)
    (hinv : ∀ γ : gamma N,∀ z : ℍ,f (γ.val•z)=f z) (z : ℍ) :
    normalizedCuspHecke N p (fun w => f (J•w)) z=normalizedCuspHecke N p f (J•z) := by
  simp only [normalizedCuspHecke,cuspHeckeSum_reflection N p f hinv z]

/-- The actual finite-cover/adjoint Hecke operator commutes with the actual
reflection on every automorphic representative. -/
theorem reflection_hecke_representative (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    reflectionRepresentative N (HeckeL2.heckeRepresentative N p hN hpN A B hAB f)=
      HeckeL2.heckeRepresentative N p hN hpN A B hAB (reflectionRepresentative N f) := by
  apply Subtype.ext
  funext z
  change (HeckeL2.heckeRepresentative N p hN hpN A B hAB f).val (J•z)=
    (HeckeL2.heckeRepresentative N p hN hpN A B hAB (reflectionRepresentative N f)).val z
  rw [← normalizedCuspHecke_eq_representative N p hN hpN hNp A B hAB f,
    ← normalizedCuspHecke_eq_representative N p hN hpN hNp A B hAB (reflectionRepresentative N f)]
  exact (normalizedCuspHecke_reflection N p f.val f.property.2.1 z).symm

/-- Genuine unramified Hecke/reflection commutation on the full quotient
Hilbert completion; the branch permutation is proved, not assumed. -/
theorem reflectionIsometry_hecke_commute (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) :
    Commute (reflectionIsometry N).toContinuousLinearMap (HeckeL2.operator N p hN hpN A B hAB) := by
  have he : (fun v : AutomorphicSpace N => reflectionIsometry N (HeckeL2.operator N p hN hpN A B hAB v))=
      fun v => HeckeL2.operator N p hN hpN A B hAB (reflectionIsometry N v) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      ((reflectionIsometry N).continuous.comp (HeckeL2.operator N p hN hpN A B hAB).continuous)
      ((HeckeL2.operator N p hN hpN A B hAB).continuous.comp (reflectionIsometry N).continuous)
    funext f
    simp only [Function.comp_apply]
    rw [HeckeL2.operator_on_representatives,reflectionIsometry_apply,reflectionIsometry_apply,
      HeckeL2.operator_on_representatives,reflection_hecke_representative N p hN hpN hNp A B hAB]
  apply ContinuousLinearMap.ext
  exact congrFun he

#print axioms cuspHeckeSum_reflection
#print axioms normalizedCuspHecke_reflection
#print axioms reflection_hecke_representative
#print axioms reflectionIsometry_hecke_commute

end QuantitativeMaass
