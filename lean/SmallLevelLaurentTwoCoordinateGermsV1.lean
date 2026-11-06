module
public import SmallLevelLaurentVariableGermV1
public import SmallLevelPoleGridTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelLaurentTwoCoordinateGerms
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticAnalyticGerm
open Filter
open scoped Topology

def coefficient (X Y Z W A B C : ℂ) (p : Poly) (i : ℕ) : ℂ :=
  eval X Y Z W A B C (fun j => if j=i then 1 else 0) p

theorem eval_two_coordinates (X Y Z W A B C : ℂ) (p : Poly) (v : ℕ→ℂ)
    (hp : ∀ t∈p,t.2.1=0 ∨ t.2.1=1) :
    eval X Y Z W A B C v p=
      coefficient X Y Z W A B C p 0*v 0+coefficient X Y Z W A B C p 1*v 1 := by
  unfold coefficient
  induction p with
  | nil => simp
  | cons t p ih =>
    have ht := hp t (by simp)
    have htail : ∀ t∈p,t.2.1=0 ∨ t.2.1=1 := fun t ht => hp t (by simp [ht])
    rw [eval_cons,eval_cons,eval_cons,ih htail]
    rcases ht with ht|ht
    · simp only [ht,ite_true,ite_eq_right (by decide : (0:ℕ)≠1)]
      ring
    · simp only [ht,ite_true,ite_eq_right (by decide : (1:ℕ)≠0)]
      ring

theorem eval_top_two (X Y Z W A B C : ℂ) (p : Poly) (v : Fin 2→ℂ)
    (hp : ∀ t∈p,t.2.1=0 ∨ t.2.1=1) :
    eval X Y Z W A B C (fun j => if j=0 then v 0 else v 1) p=
      ∑ i : Fin 2,coefficient X Y Z W A B C p i*v i := by
  rw [eval_two_coordinates X Y Z W A B C p _ hp]
  simp [Fin.sum_univ_two]

theorem coefficient_analytic (X Y Z W A B C : ℂ→ℂ) (s : ℂ) (p : Poly) (i : ℕ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0) :
    AnalyticAt ℂ (fun t => coefficient (X t) (Y t) (Z t) (W t) (A t) (B t) (C t) p i) s := by
  unfold coefficient
  induction p with
  | nil => exact analyticAt_const
  | cons t p ih =>
    simp only [eval_cons]
    exact ((analyticAt_const.mul
      (SmallLevelLaurentVariableGerm.monomial_analytic X Y Z W A B C s t.2.2
        hX hY hZ hW hA hB hC hx hy hz hw)).mul analyticAt_const).add ih

/-- After polynomial syzygies remove the lower layers, a pole of either
top coordinate supplies a nonzero two-coordinate kernel vector. No bound
on the pole orders of the removed lower layers is used here. -/
theorem leading_kernel {ρ : Type*} (X Y Z W A B C : ℂ→ℂ)
    (F : Fin 2→ℂ→ℂ) (p : ρ→Poly) (s : ℂ)
    (hX : AnalyticAt ℂ X s) (hY : AnalyticAt ℂ Y s)
    (hZ : AnalyticAt ℂ Z s) (hW : AnalyticAt ℂ W s)
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s) (hC : AnalyticAt ℂ C s)
    (hx : X s≠0) (hy : Y s≠0) (hz : Z s≠0) (hw : W s≠0)
    (hF : ∀ i,MeromorphicAt (F i) s) (hpole : ∃ i,meromorphicOrderAt (F i) s<0)
    (hsupport : ∀ r t,t∈p r → t.2.1=0 ∨ t.2.1=1)
    (hrows : ∀ r,HasAnalyticGerm (fun z => eval (X z) (Y z) (Z z) (W z)
      (A z) (B z) (C z) (fun j => if j=0 then F 0 z else F 1 z) (p r)) s) :
    ∃ v : Fin 2→ℂ,v≠0 ∧ ∀ r,
      eval (X s) (Y s) (Z s) (W s) (A s) (B s) (C s)
        (fun j => if j=0 then v 0 else v 1) (p r)=0 := by
  classical
  choose H hH he using hrows
  obtain ⟨v,hv,hvrows⟩ := SmallLevelPoleGrid.leading_kernel hF hpole
    (fun z r i => coefficient (X z) (Y z) (Z z) (W z) (A z) (B z) (C z) (p r) i) H
    (fun r i => coefficient_analytic X Y Z W A B C s (p r) i
      hX hY hZ hW hA hB hC hx hy hz hw) hH (fun r => by
        filter_upwards [he r] with z hz
        rw [←eval_top_two (X z) (Y z) (Z z) (W z) (A z) (B z) (C z)
          (p r) (fun i => F i z) (hsupport r)]
        exact hz)
  refine ⟨v,hv,?_⟩
  intro r
  rw [eval_top_two (X s) (Y s) (Z s) (W s) (A s) (B s) (C s) (p r) v (hsupport r)]
  exact hvrows r

#print axioms eval_two_coordinates
#print axioms coefficient_analytic
#print axioms leading_kernel
end SmallLevelLaurentTwoCoordinateGerms
