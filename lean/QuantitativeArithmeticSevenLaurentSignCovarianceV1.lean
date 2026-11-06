module
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSevenLaurentRows

def SignCompatible (e : Exponent) : Prop :=
  (e.2.1+e.2.2.2.1)%2=(e.2.2.2.2.2.1:ℤ)%2 ∧
  (e.2.2.1+e.2.2.2.1)%2=(e.2.2.2.2.2.2:ℤ)%2

instance (e : Exponent) : Decidable (SignCompatible e) := by unfold SignCompatible; infer_instance

private theorem sign_zpow_eq (u : ℂ) (hu : u=1 ∨ u= -1)
    (r s : ℤ) (h : r%2=s%2) : u^r=u^s := by
  rcases hu with rfl|rfl
  · simp
  · have he : Even (r-s) := Int.even_iff.mpr (by omega)
    have hh := he.neg_one_zpow (α := ℂ)
    rw [zpow_sub₀ (by norm_num : (-1:ℂ)≠0)] at hh
    exact (div_eq_one_iff_eq (zpow_ne_zero _ (by norm_num : (-1:ℂ)≠0))).mp hh

theorem monomial_sign_covariance (x y z η a u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (e : Exponent) (he : SignCompatible e) :
    monomial x y z η a u v e=monomial x (u*y) (v*z) (η*u*v) a 1 1 e := by
  have hu0 : u≠0 := by rcases hu with h|h <;> simp [h]
  have hv0 : v≠0 := by rcases hv with h|h <;> simp [h]
  have huPow : u^e.2.1*u^e.2.2.2.1=u^e.2.2.2.2.2.1 := by
    rw [← zpow_add₀ hu0,sign_zpow_eq u hu _ _ he.1,zpow_natCast]
  have hvPow : v^e.2.2.1*v^e.2.2.2.1=v^e.2.2.2.2.2.2 := by
    rw [← zpow_add₀ hv0,sign_zpow_eq v hv _ _ he.2,zpow_natCast]
  calc
    monomial x y z η a u v e=
        (x^e.1*y^e.2.1*z^e.2.2.1*η^e.2.2.2.1*a^e.2.2.2.2.1)*
          (u^e.2.1*u^e.2.2.2.1)*(v^e.2.2.1*v^e.2.2.2.1) := by
      rw [huPow,hvPow]
      rfl
    _=monomial x (u*y) (v*z) (η*u*v) a 1 1 e := by
      simp only [monomial,mul_zpow,one_pow,mul_one]
      ring

theorem eval_sign_covariance (x y z η a u v : ℂ) (w : ℕ→ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (p : Poly) (hp : ∀ t∈p,SignCompatible t.2.2) :
    eval x y z η a u v w p=eval x (u*y) (v*z) (η*u*v) a 1 1 w p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    simp only [eval_cons]
    rw [monomial_sign_covariance x y z η a u v hu hv t.2.2 (hp t (by simp)),
      ih (fun t ht => hp t (by simp [ht]))]

#print axioms monomial_sign_covariance
#print axioms eval_sign_covariance
end QuantitativeArithmeticSevenLaurentRows
