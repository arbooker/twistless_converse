module

public import AsymptoticQuotientCoordinatesV1
public import AsymptoticDecodedRamifiedKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticQuotientIncidence

open UpperHalfPlane ContinuousLinearMap AsymptoticCongruenceQuotient
open AsymptoticSectorSigns AsymptoticOrbitDecode AsymptoticFreshMatrices
open scoped lp

abbrev BadPrime (N : ℕ) := {p : ℕ // p.Prime ∧ p∣N}

noncomputable def fricke (N : ℕ) (hN : 0<N) (ε : ℝ) (t : ℕ) (e : Sector N)
    (x : ℍ) (g : AsymptoticRationalGroup.Group) : ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℂ :=
  sign e.1 • coordinate N ε t x (frickeLabel N hN*g)-coordinate N ε t x g

noncomputable def ramified (N : ℕ) (ε : ℝ) (t : ℕ) (e : Sector N) (p : BadPrime N)
    (x : ℍ) (g : AsymptoticRationalGroup.Group) : ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℂ :=
  (∑ a : Fin p.val,coordinate N ε t x (ramifiedLabel p.val p.property.1.pos a*g))-
    AsymptoticCylinderRamified.eigenvalue e p.val • coordinate N ε t x g

theorem fricke_apply (N : ℕ) (hN : 0<N) (ε : ℝ) (t : ℕ) (e : Sector N)
    (x : ℍ) (g : AsymptoticRationalGroup.Group) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    fricke N hN ε t e x g v=
      sign e.1*coordinate N ε t x (frickeLabel N hN*g) v-coordinate N ε t x g v := rfl

theorem ramified_apply (N : ℕ) (ε : ℝ) (t : ℕ) (e : Sector N) (p : BadPrime N)
    (x : ℍ) (g : AsymptoticRationalGroup.Group) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    ramified N ε t e p x g v=
      (∑ a : Fin p.val,coordinate N ε t x (ramifiedLabel p.val p.property.1.pos a*g) v)-
        AsymptoticCylinderRamified.eigenvalue e p.val*coordinate N ε t x g v := by
  simp only [ramified,sub_apply,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]

/-- The closed quotient realization of the unweighted Fricke and
ramified incidence equations. Individual rows are bounded coordinate
functionals; no global boundedness of the coordinate weight is assumed. -/
noncomputable def space (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e : Sector N) (x : ℍ) : Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  quotientSpace N hε ht x ⊓
    ((⨅ g,(fricke N hN ε t e x g).ker) ⊓
      (⨅ p : BadPrime N,⨅ g,(ramified N ε t e p x g).ker))

theorem space_closed (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e : Sector N) (x : ℍ) :
    IsClosed (space N hN hε ht e x : Set ℓ²(AsymptoticRationalGroup.Group,ℂ)) := by
  have hq : IsClosed (quotientSpace N hε ht x : Set ℓ²(AsymptoticRationalGroup.Group,ℂ)) :=
    (completeSpace_coe_iff_isComplete.mp
      (inferInstance : CompleteSpace (quotientSpace N hε ht x))).isClosed
  simp only [space,Submodule.coe_inf,Submodule.coe_iInf]
  exact hq.inter ((isClosed_iInter (fun g => (fricke N hN ε t e x g).isClosed_ker)).inter
    (isClosed_iInter (fun p => isClosed_iInter (fun g => (ramified N ε t e p x g).isClosed_ker))))

noncomputable instance space_complete (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e : Sector N) (x : ℍ) : CompleteSpace (space N hN hε ht e x) :=
  (space_closed N hN hε ht e x).completeSpace_coe

theorem space_mem (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e : Sector N) (x : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    v∈space N hN hε ht e x ↔ v∈quotientSpace N hε ht x ∧
      (∀ g,sign e.1*coordinate N ε t x (frickeLabel N hN*g) v=coordinate N ε t x g v) ∧
      (∀ p : BadPrime N,∀ g,
        (∑ a : Fin p.val,coordinate N ε t x (ramifiedLabel p.val p.property.1.pos a*g) v)=
          AsymptoticCylinderRamified.eigenvalue e p.val*coordinate N ε t x g v) := by
  simp only [space,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker]
  change (v∈quotientSpace N hε ht x ∧ (∀ g,fricke N hN ε t e x g v=0) ∧
      (∀ p : BadPrime N,∀ g,ramified N ε t e p x g v=0)) ↔ _
  simp only [fricke_apply,ramified_apply,sub_eq_zero]

theorem induction_mem_space (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e : Sector N) (x : ℍ) (f : ℓ²(Classes N,ℂ)) :
    induction N hε ht x f∈space N hN hε ht e x ↔
      (∀ g,sign e.1*f (classOf N (frickeLabel N hN*g))=f (classOf N g)) ∧
      (∀ p : BadPrime N,∀ g,
        (∑ a : Fin p.val,f (classOf N (ramifiedLabel p.val p.property.1.pos a*g)))=
          AsymptoticCylinderRamified.eigenvalue e p.val*f (classOf N g)) := by
  have hf : induction N hε ht x f∈quotientSpace N hε ht x := ⟨f,rfl⟩
  rw [space_mem]
  simp only [hf,true_and,coordinate_induction]

#print axioms fricke_apply
#print axioms ramified_apply
#print axioms space_closed
#print axioms space_mem
#print axioms induction_mem_space

end AsymptoticQuotientIncidence
