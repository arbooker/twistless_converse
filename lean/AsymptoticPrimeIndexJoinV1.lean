module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs

set_option autoImplicit false
@[expose] public section

namespace AsymptoticPrimeIndexJoin

variable {G : Type*} [Group G]

/-- An overgroup of prime relative index has no proper intermediate
subgroup; a second subgroup outside the first generates the overgroup. -/
theorem sup_eq_of_prime_relIndex (H J K : Subgroup G) (hH : H≤K) (hJ : J≤K)
    (hp : (H.relIndex K).Prime) (hne : ¬J≤H) : H⊔J=K := by
  have hle : H⊔J≤K := sup_le hH hJ
  have hm := Subgroup.relIndex_mul_relIndex H (H⊔J) K le_sup_left hle
  have hd : H.relIndex (H⊔J)∣H.relIndex K := dvd_of_mul_right_eq _ hm
  rcases (Nat.dvd_prime hp).mp hd with hone | heq
  · have hi : H⊔J≤H := Subgroup.relIndex_eq_one.mp hone
    exact (hne (le_sup_right.trans hi)).elim
  · have hi : (H⊔J).relIndex K=1 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      simpa only [heq,mul_one] using hm
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hi)

#print axioms sup_eq_of_prime_relIndex

end AsymptoticPrimeIndexJoin
