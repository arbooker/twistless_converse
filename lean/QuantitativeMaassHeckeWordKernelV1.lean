module

public import QuantitativeMaassHeckeWordTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology InnerProductSpace SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- The standard integral branch is literally the level-one branch matrix. -/
theorem standardBranch_matrix (p : ℕ) (j : Option (ZMod p)) :
    HeckeUpper.branchMatrix p j=cuspBranch 1 p j := by
  cases j <;> simp [HeckeUpper.branchMatrix,cuspBranch]

/-- Exact positive determinant of every standard integral Hecke branch. -/
theorem standardBranch_det_pos (p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) :
    0<(HeckeUpper.branchMatrix p j).det := by
  rw [standardBranch_matrix,cuspBranch_det]
  exact_mod_cast (Fact.out : p.Prime).pos

/-- The standard GL branch used by the actual operator is the very same
positive integral matrix used by the correspondence geometry. -/
theorem standardBranch_GL (p : ℕ) [Fact p.Prime] (j : Option (ZMod p)) :
    positiveIntegralGL (HeckeUpper.branchMatrix p j) (standardBranch_det_pos p j)=cuspBranchGL 1 p j := by
  apply Units.ext
  change (HeckeUpper.branchMatrix p j).map (Int.castRingHom ℝ)=(cuspBranch 1 p j).map (Int.castRingHom ℝ)
  rw [standardBranch_matrix]

/-- The literal word recursion and actual branch action have the same order. -/
theorem heckeUpper_left_action (p : ℕ) [Fact p.Prime] (j : Option (ZMod p))
    (M : HeckeUpper) (hM : 0<M.matrix.det) (x : ℍ) :
    positiveIntegralGL (HeckeUpper.left p j M).matrix (heckeUpper_left_det_pos p j M hM) • x=
      cuspBranchGL 1 p j • (positiveIntegralGL M.matrix hM • x) := by
  have hp : 0<(HeckeUpper.branchMatrix p j*M.matrix).det := by
    rw [← HeckeUpper.left_matrix]
    exact heckeUpper_left_det_pos p j M hM
  have hh : positiveIntegralGL (HeckeUpper.left p j M).matrix
      (heckeUpper_left_det_pos p j M hM)=
      positiveIntegralGL (HeckeUpper.branchMatrix p j*M.matrix) hp := by
    congr 1
    exact HeckeUpper.left_matrix p j M
  rw [hh,positiveIntegralGL_mul _ _ (standardBranch_det_pos p j) hM hp,standardBranch_GL,mul_smul]

/-- The finite word kernel is exactly the standard iterated correspondence,
with no formal replacement of the geometric branches. -/
theorem upperWindowKernel_eq_iterate (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0<M.matrix.det) (x : ℍ) :
    upperWindowKernel N p K hc R hR a b n M x=
      heckeBranchIterate 1 p n (fun z => radialPoincareKernel N (abelProfile
        (evenCoshLift (timeConvolution (windowTimeSchwartz K hc R hR a b)
          (windowTimeSchwartz K hc R hR a b)))) x z) (positiveIntegralGL M.matrix hM • x) := by
  induction n generalizing M with
  | zero => simp only [upperWindowKernel,dite_eq_left hM,heckeBranchIterate,windowIntegralKernel]
  | succ n ih =>
    simp only [upperWindowKernel,heckeBranchIterate,normalizedCuspHecke,cuspHeckeSum,Complex.real_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih (HeckeUpper.left p j M) (heckeUpper_left_det_pos p j M hM),heckeUpper_left_action]

/-- The root word acts as the actual identity. -/
theorem heckeUpper_root_action (h : 0<HeckeUpper.root.matrix.det) (x : ℍ) :
    positiveIntegralGL HeckeUpper.root.matrix h • x=x := by
  have hh : positiveIntegralGL HeckeUpper.root.matrix h=1 := by
    apply Units.ext
    change HeckeUpper.root.matrix.map (Int.castRingHom ℝ)=1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [HeckeUpper.root,HeckeUpper.matrix]
  rw [hh,one_smul]

/-- Canonical actual original-window Hilbert column. Its support radius is
chosen from the proved uniform support theorem, not supplied as an assumption. -/
def windowAbelColumn (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : ℍ → AutomorphicSpace N :=
  let B := (symmetricWindowTimeTest_uniform_support K hc).choose
  let hB := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.1
  let hs := (symmetricWindowTimeTest_uniform_support K hc).choose_spec.2
  timeAbelColumn N (windowTimeSchwartz K hc R hR a b)
    (symmetricWindowTimeTest_compact K hc R a b hR) (symmetricWindowTimeTest_even K he R a b)
    (B*R) (mul_nonneg hB.le hR.le) (hs R hR a b)

/-- Every power of the actual Hilbert Hecke operator has precisely the
finite word kernel whose trace and tree coefficient were proved geometrically. -/
theorem windowAbelColumn_hecke_power (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (u v : ℝ) (n : ℕ) (x : ℍ) :
    inner ℂ (((HeckeL2.operator N p hN hpN a b hab)^n) (windowAbelColumn N K he hc R hR u v x))
      (windowAbelColumn N K he hc R hR u v x)=upperWindowKernel N p K hc R hR u v n HeckeUpper.root x := by
  rw [upperWindowKernel_eq_iterate N p K hc R hR u v n HeckeUpper.root
    (by norm_num [HeckeUpper.det_matrix,HeckeUpper.root_det]),heckeUpper_root_action]
  unfold windowAbelColumn
  exact timeSquare_hecke_power_standard N p hN hpN hNp a b hab _ _ _
    (symmetricWindowTimeTest_real K he R u v) _ _ _ n x x

/-- Actual normalized Hecke-power trace asymptotic for the literal original
moving window. All support, branch, scalar-coset and finite-sum inputs are proved.
This remains a full-quotient localized trace, not a cuspidal counting theorem. -/
theorem actualHecke_window_trace_main (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (n : ℕ) :
    Tendsto (fun t =>
      (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (inner ℂ (((HeckeL2.operator N p hN hpN a b hab)^n)
          (windowAbelColumn N K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t) x))
          (windowAbelColumn N K he hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t) t (t+ε t) x)).re
        ∂quotientMeasure N)/(t*ε t))
      atTop (𝓝 ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
        (quotientMeasure N).real univ/(2*Real.pi))) := by
  simp_rw [windowAbelColumn_hecke_power N p hN hpN hNp a b hab]
  exact upperWindowKernel_root_trace_main N p K he hc hK hm o ε hε hproduct n

#print axioms standardBranch_matrix
#print axioms standardBranch_det_pos
#print axioms standardBranch_GL
#print axioms heckeUpper_left_action
#print axioms upperWindowKernel_eq_iterate
#print axioms heckeUpper_root_action
#print axioms windowAbelColumn_hecke_power
#print axioms actualHecke_window_trace_main

end QuantitativeMaass
