module

public import QuantitativeMaassHeckeColumnV1
public import QuantitativeMaassCorrespondenceCosetV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticClassicalCusp AsymptoticClassicalDiscriminant
open scoped Topology InnerProductSpace SchwartzMap

namespace QuantitativeMaass

/-- On an actual invariant function the adapted Hecke branches sum to the
standard upper-triangular branches. No invariance at level one is assumed. -/
theorem cuspHeckeSum_eq_one (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (f : ℍ → ℂ)
    (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z) (x : ℍ) :
    cuspHeckeSum N p f x=cuspHeckeSum 1 p f x := by
  rw [cuspHeckeSum_eq_standard N p hNp f hinv,cuspHeckeSum,
    Fintype.sum_option,cuspBranchGL_none_dilation]
  congr 1
  simp_rw [cuspBranchGL_some_triangular]
  rw [sum_zmod_val p (fun a => f (triangularGL 1 a p (by norm_num)
    (by exact_mod_cast (Fact.out : p.Prime).pos) • x))]
  exact Fin.sum_univ_eq_sum_range (fun a => f (triangularGL 1 a p (by norm_num)
    (by exact_mod_cast (Fact.out : p.Prime).pos) • x)) p

/-- Actual invariant Hilbert columns admit the same standardization, by
pairing against arbitrary vectors. -/
theorem invariantColumn_standard_sum (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (c : ℍ → AutomorphicSpace N)
    (hinv : ∀ γ : gamma N,∀ z,c (γ•z)=c z) (x : ℍ) :
    (∑ j : Option (ZMod p),c (cuspBranchGL N p j • x))=
      ∑ j : Option (ZMod p),c (cuspBranchGL 1 p j • x) := by
  apply ext_inner_right ℂ
  intro v
  rw [sum_inner,sum_inner]
  exact cuspHeckeSum_eq_one N p hNp (fun z => inner ℂ (c z) v)
    (fun γ z => by rw [hinv]) x

/-- The genuine Hecke operator on original time columns has the standard
p+1 branches, with the actual level-N translations and permutation discharged. -/
theorem timeAbelColumn_hecke_standard (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (x : ℍ) :
    HeckeL2.operator N p hN hpN a b hab (timeAbelColumn N f hc he R hR hs x)=
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) • ∑ j : Option (ZMod p),
        timeAbelColumn N f hc he R hR hs (cuspBranchGL 1 p j • x) := by
  rw [timeAbelColumn_hecke N p hN hpN hNp a b hab f hc he hr R hR hs]
  congr 1
  exact invariantColumn_standard_sum N p hNp (timeAbelColumn N f hc he R hR hs)
    (oneSidedAbelColumn_invariant N _ _ _ _ _) x

/-- Every actual Hecke power now has its standard, rather than N-adapted,
finite branch expansion. These are the matrices counted by the Hecke tree. -/
theorem timeSquare_hecke_power_standard (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R) (n : ℕ) (x y : ℍ) :
    inner ℂ (((HeckeL2.operator N p hN hpN a b hab)^n) (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs y)=
      heckeBranchIterate 1 p n
        (fun z => radialPoincareKernel N (abelProfile (evenCoshLift (timeConvolution f f))) y z) x := by
  let T := HeckeL2.operator N p hN hpN a b hab
  let c := timeAbelColumn N f hc he R hR hs
  let α : ℂ := (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)
  have hcol (z : ℍ) : T (c z)=α • ∑ j : Option (ZMod p),c (cuspBranchGL 1 p j • z) :=
    timeAbelColumn_hecke_standard N p hN hpN hNp a b hab f hc he hr R hR hs z
  have hscalar (w : AutomorphicSpace N) : inner ℂ (α • w) (c y)=α*inner ℂ w (c y) := by
    rw [inner_smul_left w (c y) α]
    simp only [α,Complex.conj_ofReal]
  change inner ℂ ((T^n) (c x)) (c y)=_
  induction n generalizing x with
  | zero =>
    simpa only [pow_zero,one_apply_eq_self,heckeBranchIterate] using
      timeSquare_kernel_cross N f hc he hr R hR hs y x
  | succ n ih =>
    rw [pow_succ]
    change inner ℂ ((T^n) (T (c x))) (c y)=_
    rw [hcol,map_smul,map_sum,hscalar,sum_inner]
    simp_rw [ih]
    simp only [heckeBranchIterate,normalizedCuspHecke,cuspHeckeSum,α,Complex.real_smul]

#print axioms cuspHeckeSum_eq_one
#print axioms invariantColumn_standard_sum
#print axioms timeAbelColumn_hecke_standard
#print axioms timeSquare_hecke_power_standard

end QuantitativeMaass
