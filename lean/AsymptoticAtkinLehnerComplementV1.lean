module

public import AsymptoticRamifiedTwistedLawV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticAtkinLehner

open Matrix AsymptoticRationalGroup AsymptoticRationalFreeness AsymptoticRationalBranches
open AsymptoticFreshMatrices AsymptoticCongruenceLabels
open scoped MatrixGroups

theorem bezout_relation (M p : ℕ) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) :
    (p:ℤ)*A=(M:ℤ)*1*(-B)+1 := by linear_combination hAB

/-- A fixed determinant-M representative for the complementary
Atkin--Lehner coset at level p*M. -/
def complementGL (M p : ℕ) (hM : 0<M) (A B : ℤ) (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : GL (Fin 2) ℚ :=
  representative M p hM.ne' 1 (-B) A (bezout_relation M p A B hAB)

theorem complement_positive (M p : ℕ) (hM : 0<M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : 0<(realMatrix (complementGL M p hM A B hAB)).det.val := by
  change 0<((entries M p 1 (-B) A).map (fun z : ℚ => (z:ℝ))).det
  rw [← Rat.cast_det,entries_det M p 1 (-B) A (bezout_relation M p A B hAB)]
  exact_mod_cast hM

noncomputable def complement (M p : ℕ) (hM : 0<M) (A B : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) : AsymptoticRationalGroup.Group :=
  ofMatrix (complementGL M p hM A B hAB) (complement_positive M p hM A B hAB)

/-- The left Γ₀(pM) factor comparing every ramified reflected matrix
with the fixed complementary Atkin--Lehner representative. -/
def comparison (M p : ℕ) (A B a b c : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (h : (p:ℤ)*c=(M:ℤ)*a*b+1) : SL(2,ℤ) :=
  ⟨!![(M:ℤ)*a*B+(p:ℤ)*c,a*A-c;(p:ℤ)*(M:ℤ)*(B+b),(p:ℤ)*A-(M:ℤ)*b],by
    rw [Matrix.det_fin_two]
    change ((M:ℤ)*a*B+(p:ℤ)*c)*((p:ℤ)*A-(M:ℤ)*b)-
      (a*A-c)*((p:ℤ)*(M:ℤ)*(B+b))=1
    linear_combination ((p:ℤ)*A+(M:ℤ)*B)*h+hAB⟩

theorem comparison_mem (M p : ℕ) (A B a b c : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (h : (p:ℤ)*c=(M:ℤ)*a*b+1) :
    comparison M p A B a b c hAB h∈CongruenceSubgroup.Gamma0 (p*M) := by
  rw [gamma0_mem_dvd]
  refine ⟨B+b,?_⟩
  change (p:ℤ)*(M:ℤ)*(B+b)=((p*M:ℕ):ℤ)*(B+b)
  rw [Nat.cast_mul]

theorem comparison_mul (M p : ℕ) (hM : 0<M) (A B a b c : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (h : (p:ℤ)*c=(M:ℤ)*a*b+1) :
    rationalGL (comparison M p A B a b c hAB h)*complementGL M p hM A B hAB=
      representative M p hM.ne' a b c h := by
  have hb : (p:ℚ)*(A:ℚ)+(M:ℚ)*(B:ℚ)=1 := by exact_mod_cast hAB
  apply Units.ext
  change (comparison M p A B a b c hAB h).val.map (fun z : ℤ => (z:ℚ))*
    (complementGL M p hM A B hAB).val=(representative M p hM.ne' a b c h).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comparison,complementGL,representative,entries,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]
  · linear_combination (M:ℚ)*(a:ℚ)*hb
  · linear_combination -(c:ℚ)*hb
  · linear_combination (p:ℚ)*(M:ℚ)*hb
  · linear_combination -(M:ℚ)*(b:ℚ)*hb

theorem label_eq_comparison_complement (M p : ℕ) (hM : 0<M) (hp : 0<p) (A B a b c : ℤ)
    (hAB : (p:ℤ)*A+(M:ℤ)*B=1) (h : (p:ℤ)*c=(M:ℤ)*a*b+1) :
    label M p hM hp a b=integralLabel (comparison M p A B a b c hAB h)*complement M p hM A B hAB := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (branchMatrix M p hM.ne' hp.ne' a b)=
    rationalMap (rationalGL (comparison M p A B a b c hAB h))*rationalMap (complementGL M p hM A B hAB)
  rw [← branchMatrix_projective M p hM.ne' hp.ne' a b c h,← map_mul,comparison_mul]

#print axioms bezout_relation
#print axioms complement_positive
#print axioms comparison_mem
#print axioms comparison_mul
#print axioms label_eq_comparison_complement

end AsymptoticAtkinLehner
