module

public import QuantitativeArithmeticRetainedFilterCostV1
public import QuantitativeEulerEndpointCornerAmbientV1
public import QuantitativeEulerEndpointNestedFiniteV1
public import QuantitativeEulerEndpointCornerIterationV1
public import QuantitativeEulerEndpointComparisonIterationV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticRetainedTerminalAlgebra
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight QuantitativeEulerEndpointRegularBase
open AsymptoticFiniteBranch Polynomial
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

def repAt (z : Base) : Algebra A P →ₗ[ℝ] (RegularSpace →L[ℂ] RegularSpace) where
  toFun a := rep A P a z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rep_aeval (a : Algebra A P) (q : ℝ[X]) (z : Base) :
    rep A P (aeval a q) z=aeval (rep A P a z) q*rep A P 1 z :=
  QuantitativeEulerEndpointCornerPolynomial.map_aeval_corner (repAt A P z) (fun _ _ => rfl) a q

theorem rep_update (a g : Algebra A P) (n : ℕ) (z : Base) :
    rep A P (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) n) z=
      QuantitativeEulerEndpointUpdateExpression.cornerUpdate (rep A P 1 z) (rep A P a z) (rep A P g z) n :=
  QuantitativeEulerEndpointUpdateExpression.map_update (repAt A P z) (fun _ _ => rfl) a g n

#print axioms rep_aeval
#print axioms rep_update
end QuantitativeArithmeticRetainedTerminalAlgebra

namespace QuantitativeArithmeticRetainedExpressionIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic
open QuantitativeArithmeticRetainedTerminalAlgebra Polynomial MeasureTheory

variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

/-- The finite branch identity on the ENTIRE terminal source. -/
def unit : Expression := [AsymptoticFiniteBranch.corner (terminalRegion A P) (terminal_measurable A P)]

theorem unit_mass : expressionBound (unit A P)=1 := by
  simp [unit,expressionBound,AsymptoticFiniteBranch.corner]

theorem unit_matrix : ExpressionMatrixBound (unit A P) 1 := by
  intro b hb
  have hb' : b=AsymptoticFiniteBranch.corner (terminalRegion A P) (terminal_measurable A P) := by
    simpa only [unit,List.mem_singleton] using hb
  subst b
  refine ⟨1,integerAction_one,?_⟩
  intro i j
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem unit_regular (x : UpperHalfPlane) : regularSum (unit A P) x=rep A P 1 x := by
  simp only [unit,regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,regular_corner]
  rfl

theorem unit_physical (m : ℕ) : holomorphicSum (unit A P) m=
    AsymptoticRegionL2.projection (volume : Measure UpperHalfPlane) (terminalRegion A P) (terminal_measurable A P) := by
  simp only [unit,holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,holomorphic_corner]

theorem unit_regular_projection (x : UpperHalfPlane) : IsStarProjection (regularSum (unit A P) x) := by
  rw [unit_regular,rep_one]
  exact isStarProjection_starProjection

theorem unit_physical_projection (m : ℕ) : IsStarProjection (holomorphicSum (unit A P) m) := by
  constructor
  · change holomorphicSum (unit A P) m*holomorphicSum (unit A P) m=holomorphicSum (unit A P) m
    rw [unit_physical]
    apply ContinuousLinearMap.ext
    exact AsymptoticRegionL2.projection_idempotent _ _ _
  · change star (holomorphicSum (unit A P) m)=holomorphicSum (unit A P) m
    rw [unit_physical]
    exact AsymptoticRegionL2.projection_adjoint _ _ _

theorem unit_regular_order (x : UpperHalfPlane) :
    0≤regularSum (unit A P) x ∧ regularSum (unit A P) x≤1 := by
  have hp := unit_regular_projection A P x
  have hn : ‖regularSum (unit A P) x‖≤1 := (regularSum_norm_le _ _).trans (unit_mass A P).le
  have hz := star_mul_self_nonneg (regularSum (unit A P) x)
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hz
  exact ⟨hz,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hz).mp hn⟩

theorem unit_physical_order (m : ℕ) :
    0≤holomorphicSum (unit A P) m ∧ holomorphicSum (unit A P) m≤1 := by
  have hp := unit_physical_projection A P m
  have hn : ‖holomorphicSum (unit A P) m‖≤1 := (holomorphicSum_norm_le _ _).trans (unit_mass A P).le
  have hz := star_mul_self_nonneg (holomorphicSum (unit A P) m)
  rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hz
  exact ⟨hz,(CStarAlgebra.norm_le_one_iff_of_nonneg _ hz).mp hn⟩

theorem rep_support (a : Algebra A P) (x : UpperHalfPlane) :
    rep A P 1 x*rep A P a x=rep A P a x ∧ rep A P a x*rep A P 1 x=rep A P a x := by
  change rep A P (1*a) x=rep A P a x ∧ rep A P (a*1) x=rep A P a x
  simp only [one_mul,mul_one,and_self]

theorem rep_order (a : Algebra A P) (ha : 0≤a ∧ a≤1) (x : UpperHalfPlane) :
    0≤rep A P a x ∧ rep A P a x≤1 := by
  have h0 := (QuantitativeSpectralRegularOrder.pointwise_le_iff _ _ _ 0 a).mpr ha.1 x
  have h1 := (QuantitativeSpectralRegularOrder.pointwise_le_iff _ _ _ a 1).mpr ha.2 x
  change 0≤rep A P a x at h0
  change rep A P a x≤rep A P 1 x at h1
  have hu := (unit_regular_order A P x).2
  rw [unit_regular] at hu
  exact ⟨h0,h1.trans hu⟩

theorem rep_sharpened_ambient (a g : Algebra A P) (d : ℕ) (q : ℝ[X]) (hq : q.eval 0=0)
    (x : UpperHalfPlane) :
    rep A P (aeval (QuantitativeEulerEndpointSoftUpdate.update a (a*g*a) d) q) x=
      aeval (QuantitativeEulerEndpointSoftUpdate.update (rep A P a x)
        (rep A P a x*rep A P g x*rep A P a x) d) q := by
  rw [rep_aeval,rep_update]
  have hp : IsStarProjection (rep A P 1 x) := by simpa only [unit_regular] using unit_regular_projection A P x
  exact QuantitativeEulerEndpointCornerAmbient.corner_sharpened_eq _ _ _ hp.isIdempotentElem.eq
    (rep_support A P a x).1 (rep_support A P a x).2 d q hq

#print axioms unit_matrix
#print axioms unit_regular_projection
#print axioms unit_physical_projection
#print axioms rep_order
#print axioms rep_sharpened_ambient
end QuantitativeArithmeticRetainedExpressionIteration

namespace QuantitativeArithmeticRetainedExpressionIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeEulerEndpointNestedExpression QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointUpdateExpression QuantitativeEulerEndpointBandExpression
open QuantitativeEulerEndpointPolynomialExpression
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

def iterate (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) : Expression :=
  expression (unit A P) (unit A P) g L q n

theorem regular_step (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (j : ℕ)
    (x : UpperHalfPlane) :
    regularSum (iterate A P g L q (j+1)) x=
      aeval (cornerUpdate (regularSum (unit A P) x)
        (regularSum (iterate A P g L q j) x) (regularSum (g j) x) (L j)) (q j)*
          regularSum (unit A P) x := by
  unfold iterate
  rw [expression,sharpenedExpression,regular_cornerPolynomial,regular_update]

theorem physical_step (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (j m : ℕ) :
    holomorphicSum (iterate A P g L q (j+1)) m=
      aeval (cornerUpdate (holomorphicSum (unit A P) m)
        (holomorphicSum (iterate A P g L q j) m) (holomorphicSum (g j) m) (L j)) (q j)*
          holomorphicSum (unit A P) m := by
  unfold iterate
  rw [expression,holomorphic_sharpened]

/-- Positivity, contraction and support on the whole regular terminal strip. -/
theorem regular_order (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ)
    (x : UpperHalfPlane)
    (hg : ∀ j<n,let U := regularSum (unit A P) x
      let G := regularSum (g j) x
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let U := regularSum (unit A P) x
    let F := regularSum (iterate A P g L q n) x
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  have hp := unit_regular_projection A P x
  have hu := unit_regular_order A P x
  have hi : let F := regularSum (iterate A P g L q 0) x
      let U := regularSum (unit A P) x
      0≤F ∧ F≤U ∧ U*F=F ∧ F*U=F :=
    ⟨hu.1,le_rfl,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
  have h := QuantitativeEulerEndpointCornerIteration.order _ hp hu.2
    (fun j => regularSum (iterate A P g L q j) x) (fun j => regularSum (g j) x)
    L q n hi hg hq (fun j _ => regular_step A P g L q j x)
  exact ⟨h.1,h.2.2.1.trans hu.2,h.2.2⟩

/-- The identical finite expression is positive and contracting in the
physical representation; no truncation of the terminal source is used. -/
theorem physical_order (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n m : ℕ)
    (hg : ∀ j<n,let U := holomorphicSum (unit A P) m
      let G := holomorphicSum (g j) m
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ j<n,ScalarSharpening (q j)) :
    let U := holomorphicSum (unit A P) m
    let F := holomorphicSum (iterate A P g L q n) m
    0≤F ∧ F≤1 ∧ F≤U ∧ U*F=F ∧ F*U=F := by
  have hp := unit_physical_projection A P m
  have hu := unit_physical_order A P m
  have hi : let F := holomorphicSum (iterate A P g L q 0) m
      let U := holomorphicSum (unit A P) m
      0≤F ∧ F≤U ∧ U*F=F ∧ F*U=F :=
    ⟨hu.1,le_rfl,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
  have h := QuantitativeEulerEndpointCornerIteration.order _ hp hu.2
    (fun j => holomorphicSum (iterate A P g L q j) m) (fun j => holomorphicSum (g j) m)
    L q n hi hg hq (fun j _ => physical_step A P g L q j m)
  exact ⟨h.1,h.2.2.1.trans hu.2,h.2.2⟩

theorem regular_ambient_step (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    (j : ℕ) (x : UpperHalfPlane)
    (hg : ∀ i<j,let U := regularSum (unit A P) x
      let G := regularSum (g i) x
      0≤G ∧ G≤1 ∧ U*G=G ∧ G*U=G)
    (hq : ∀ i<j+1,ScalarSharpening (q i)) :
    let F := regularSum (iterate A P g L q j) x
    regularSum (iterate A P g L q (j+1)) x=
      aeval (QuantitativeEulerEndpointSoftUpdate.update F (F*regularSum (g j) x*F) (L j)) (q j) := by
  have ho := regular_order A P g L q j x hg (fun i hi => hq i (by omega))
  rw [regular_step]
  exact QuantitativeEulerEndpointCornerIteration.ambient_step _ (unit_regular_projection A P x)
    _ _ ho.2.2.2.1 ho.2.2.2.2 (L j) (q j) (hq j (by omega)).1

#print axioms regular_order
#print axioms physical_order
#print axioms regular_ambient_step
end QuantitativeArithmeticRetainedExpressionIteration

namespace QuantitativeArithmeticRetainedExpressionIteration
open QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedGlobalHeight AsymptoticFiniteBranch QuantitativeHolomorphic Polynomial
open QuantitativeArithmeticRetainedTerminalAlgebra QuantitativeEulerEndpointBernstein
open QuantitativeEulerEndpointNestedPerturbation
variable {N Q : ℕ} {R₀ : Finset ℕ} {hQ : 0<Q} (A : Certificate N R₀ Q hQ) (P : Parameters A)

/-- Compare a finite expression on the entire terminal source with an
intrinsic terminal-algebra iteration. Only the Gram approximations incur
error; the terminal identity is represented exactly. -/
theorem regular_comparison (F G : ℕ → Algebra A P) (g : ℕ → Expression)
    (L : ℕ → ℕ) (q : ℕ → ℝ[X]) (n : ℕ) (x : UpperHalfPlane)
    (hinit : F 0=1) (hF : ∀ j<n,0≤F j ∧ F j≤1) (hG : ∀ j<n,0≤G j ∧ G j≤1)
    (hrec : ∀ j<n,F (j+1)=aeval
      (QuantitativeEulerEndpointSoftUpdate.update (F j) (F j*G j*F j) (L j)) (q j))
    (hg : ∀ j<n,let U := regularSum (unit A P) x
      let T := regularSum (g j) x
      0≤T ∧ T≤1 ∧ U*T=T ∧ T*U=T)
    (hq : ∀ j<n,ScalarSharpening (q j))
    {δ : ℝ} (hδ : 0≤δ) (herror : ∀ j<n,‖rep A P (G j) x-regularSum (g j) x‖≤δ) :
    ‖rep A P (F n) x-regularSum (iterate A P g L q n) x‖≤comparisonBudget L q n*δ := by
  apply iteration_difference (fun j => rep A P (F j) x)
    (fun j => regularSum (iterate A P g L q j) x)
    (fun j => rep A P (G j) x) (fun j => regularSum (g j) x) L q n hδ
  · change ‖rep A P (F 0) x-regularSum (unit A P) x‖≤δ
    rw [hinit,unit_regular,sub_self,norm_zero]
    exact hδ
  · intro j hj
    exact rep_order A P (F j) (hF j hj) x
  · intro j hj
    have h := regular_order A P g L q j x (fun i hi => hg i (by omega))
      (fun i hi => hq i (by omega))
    exact ⟨h.1,h.2.1⟩
  · intro j hj
    exact rep_order A P (G j) (hG j hj) x
  · intro j hj
    exact ⟨(hg j hj).1,(hg j hj).2.1⟩
  · intro j hj
    rw [hrec j hj]
    exact rep_sharpened_ambient A P (F j) (G j) (L j) (q j) (hq j hj).1 x
  · intro j hj
    exact regular_ambient_step A P g L q j x (fun i hi => hg i (by omega))
      (fun i hi => hq i (by omega))
  · exact herror

/-- Exact complexity bound for the same full-terminal expression, retaining
all actual Gram and polynomial coefficient costs as finite-horizon inputs. -/
theorem bounds (g : ℕ → Expression) (L : ℕ → ℕ) (q : ℕ → ℝ[X])
    {B a b : ℝ} (hB : 16≤B) (n : ℕ)
    (hg : ∀ j<n,expressionBound (g j)≤B) (hgM : ∀ j<n,ExpressionMatrixBound (g j) B)
    (hq : ∀ j<n,(∑ i∈(q j).support,|(q j).coeff i|)≤B)
    (ha : (∑ j∈Finset.range n,QuantitativeEulerEndpointNestedExpression.logarithmicCost L q j)≤a)
    (hb : Real.log B≤Real.exp b) :
    expressionBound (iterate A P g L q n)≤Real.exp (Real.exp (a+b)) ∧
    ExpressionMatrixBound (iterate A P g L q n) (Real.exp (Real.exp (a+b))) := by
  have h1 : (1:ℝ)≤B := by linarith
  exact QuantitativeEulerEndpointNestedExpression.bounds_double_exp_upto
    (unit A P) (unit A P) g L q hB (unit_mass A P).le (unit_matrix A P)
    ((unit_mass A P).le.trans h1) ((unit_matrix A P).mono h1) n hg hgM hq ha hb

#print axioms regular_comparison
#print axioms bounds
end QuantitativeArithmeticRetainedExpressionIteration
