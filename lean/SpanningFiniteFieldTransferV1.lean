module

public import SpanningIntegerCertificatesV1
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

namespace SpanningFiniteFieldTransfer

open Matrix SpanningIntegerCertificates

theorem rational_injective_mod_large_prime {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (A : Matrix I J ℤ)
    (hA : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec) :
    ∃D:ℕ,0<D ∧ ∀p:ℕ,∀_hp:p.Prime,D<p →
      Function.Injective (A.map (Int.castRingHom (ZMod p))).mulVec := by
  obtain ⟨D,hD,C,hC⟩ := rational_injective_certificate A hA
  refine ⟨D,hD,?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  apply integer_certificate_injective A C (D:ℤ) hC
  simpa only [Int.cast_natCast,ne_eq,ZMod.natCast_eq_zero_iff] using
    (fun hdiv:p∣D => (not_le.mpr hlarge) (Nat.le_of_dvd hD hdiv))

theorem matrix_left_inverse {I J K : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] [Field K] (A : Matrix I J K)
    (hA : Function.Injective A.mulVec) : ∃C:Matrix J I K,C*A=1 := by
  classical
  obtain ⟨g,hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin
    (LinearMap.ker_eq_bot.mpr hA)
  refine ⟨LinearMap.toMatrix' g,?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  exact hg

theorem finite_field_injective_certificate {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (A : Matrix I J ℤ) (p:ℕ) [Fact p.Prime]
    (hA : Function.Injective (A.map (Int.castRingHom (ZMod p))).mulVec) :
    ∃C:Matrix J I ℤ,∃D:ℤ,D≠0 ∧ C*A=diagonal (fun _:J => D) := by
  classical
  obtain ⟨C,hC⟩ := matrix_left_inverse (A.map (Int.castRingHom (ZMod p))) hA
  let CI : Matrix J I ℤ := fun j i => (C j i).val
  have hCI : CI.map (Int.castRingHom (ZMod p))=C := by
    ext j i
    change (((C j i).val:ℤ):ZMod p)=C j i
    rw [Int.cast_natCast,ZMod.natCast_zmod_val]
  have hprod : (CI*A).map (Int.castRingHom (ZMod p))=1 := by
    rw [Matrix.map_mul,hCI,hC]
  have hdet : ((CI*A).det:ZMod p)=1 := by
    have he := RingHom.map_det (Int.castRingHom (ZMod p)) (CI*A)
    change (Int.castRingHom (ZMod p)) (CI*A).det=1
    rw [he]
    change ((CI*A).map (Int.castRingHom (ZMod p))).det=1
    rw [hprod,det_one]
  have hn : (CI*A).det≠0 := by
    intro hzero
    simp [hzero] at hdet
  refine ⟨(CI*A).adjugate*CI,(CI*A).det,hn,?_⟩
  rw [Matrix.mul_assoc,adjugate_mul,smul_one_eq_diagonal]

theorem finite_field_injective_rational {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (A : Matrix I J ℤ) (p:ℕ) [Fact p.Prime]
    (hA : Function.Injective (A.map (Int.castRingHom (ZMod p))).mulVec) :
    Function.Injective (A.map (Int.castRingHom ℚ)).mulVec := by
  obtain ⟨C,D,hD,hC⟩ := finite_field_injective_certificate A p hA
  exact integer_certificate_injective A C D hC (by exact_mod_cast hD)

theorem two_rational_injections_one_prime {I J I' J' : Type*}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    [DecidableEq J] [DecidableEq J'] (A : Matrix I J ℤ) (B : Matrix I' J' ℤ)
    (hA : Function.Injective (A.map (Int.castRingHom ℚ)).mulVec)
    (hB : Function.Injective (B.map (Int.castRingHom ℚ)).mulVec) (bound:ℕ) :
    ∃p:ℕ,p.Prime ∧ bound<p ∧
      Function.Injective (A.map (Int.castRingHom (ZMod p))).mulVec ∧
      Function.Injective (B.map (Int.castRingHom (ZMod p))).mulVec := by
  obtain ⟨DA,_,ha⟩ := rational_injective_mod_large_prime A hA
  obtain ⟨DB,_,hb⟩ := rational_injective_mod_large_prime B hB
  obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (DA+DB+bound+1)
  exact ⟨p,hprime,by omega,ha p hprime (by omega),hb p hprime (by omega)⟩

#print axioms finite_field_injective_rational
#print axioms two_rational_injections_one_prime

end SpanningFiniteFieldTransfer
