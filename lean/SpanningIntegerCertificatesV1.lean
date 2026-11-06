module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SpanningIntegerCertificates

open Matrix

theorem scaled_rat_integer {D : ℕ} (x : ℚ) (hx : x.den∣D) :
    ∃z:ℤ,(D:ℚ)*x=z := by
  refine ⟨x.num*(D/x.den:ℕ),?_⟩
  have hD : x.den*(D/x.den)=D := Nat.mul_div_cancel' hx
  have hd : (x.den:ℚ)≠0 := by exact_mod_cast x.den_ne_zero
  calc
    (D:ℚ)*x=(D:ℚ)*((x.num:ℚ)/(x.den:ℚ)) := by rw [x.num_div_den]
    _=(x.num*(D/x.den:ℕ):ℤ) := by
      have hD' : (x.den:ℚ)*((D/x.den:ℕ):ℚ)=D := by exact_mod_cast hD
      simp only [Int.cast_mul,Int.cast_natCast]
      field_simp
      simpa only [mul_assoc,mul_comm,mul_left_comm] using
        congrArg (fun z:ℚ => (x.num:ℚ)*z) hD'.symm

theorem common_denominators {I : Type*} [Fintype I] (f : I → ℚ) :
    ∃D:ℕ,0<D ∧ ∀i,∃z:ℤ,(D:ℚ)*f i=z := by
  classical
  let D := ∏i:I,(f i).den
  refine ⟨D,Finset.prod_pos (fun i _ => (f i).den_pos),?_⟩
  intro i
  exact scaled_rat_integer (f i) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

theorem integer_certificate_injective {I J K : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] [Field K] (A : Matrix I J ℤ) (C : Matrix J I ℤ) (D : ℤ)
    (hcert : C*A=diagonal (fun _:J => D)) (hD : (D:K)≠0) :
    Function.Injective (A.map (Int.castRingHom K)).mulVec := by
  change Function.Injective (A.map (Int.castRingHom K)).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hc : (C.map (Int.castRingHom K))*(A.map (Int.castRingHom K))=
      diagonal (fun _:J => (D:K)) := by
    rw [←Matrix.map_mul,hcert]
    exact diagonal_map (map_zero (Int.castRingHom K))
  change (A.map (Int.castRingHom K)).mulVec v = 0 at hv
  have hh := congrArg (fun w:I → K => (C.map (Int.castRingHom K)).mulVec w) hv
  rw [mulVec_mulVec, hc] at hh
  funext j
  have hj := congrFun hh j
  simp only [mulVec_diagonal,mulVec_zero,Pi.zero_apply] at hj
  exact (mul_eq_zero.mp hj).resolve_left hD

theorem rational_injective_certificate {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (A : Matrix I J ℤ)
    (hA : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec) :
    ∃D:ℕ,0<D ∧ ∃C:Matrix J I ℤ,C*A=diagonal (fun _:J => (D:ℤ)) := by
  classical
  let AQ := A.map (Int.castRingHom ℚ)
  obtain ⟨g,hg⟩ := LinearMap.exists_leftInverse_of_injective AQ.mulVecLin
    (LinearMap.ker_eq_bot.mpr hA)
  let CQ : Matrix J I ℚ := LinearMap.toMatrix' g
  have hCQ : CQ*AQ=1 := by
    apply Matrix.toLin'.injective
    change (CQ*AQ).mulVecLin=(1:Matrix J J ℚ).mulVecLin
    rw [Matrix.mulVecLin_mul,Matrix.mulVecLin_one]
    have he : CQ.mulVecLin=g := Matrix.toLin'_toMatrix' g
    rw [he]
    exact hg
  obtain ⟨D,hD,hden⟩ := common_denominators (fun ji:J×I => CQ ji.1 ji.2)
  choose C hC using hden
  let CI : Matrix J I ℤ := fun j i => C (j,i)
  have hCI : CI.map (Int.castRingHom ℚ)=(D:ℚ) • CQ := by
    ext j i
    exact (hC (j,i)).symm
  refine ⟨D,hD,CI,?_⟩
  have he : (CI*A).map (Int.castRingHom ℚ)=
      (diagonal (fun _:J => (D:ℤ))).map (Int.castRingHom ℚ) := by
    rw [Matrix.map_mul,hCI]
    change ((D:ℚ) • CQ)*AQ=_
    rw [Matrix.smul_mul,hCQ,smul_one_eq_diagonal]
    simp
  ext j k
  exact Int.cast_injective (congrFun (congrFun he j) k)

#print axioms rational_injective_certificate
#print axioms common_denominators
#print axioms integer_certificate_injective

end SpanningIntegerCertificates
