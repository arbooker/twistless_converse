module

public import SmallLevelThirtySixOrbitV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane ModularGroup
open scoped ModularForm MatrixGroups

abbrev Coefficients := ℤ × ℤ × ℤ

def combo (m : ℕ) (g : ℍ → ℂ) (v : Coefficients) : ℍ → ℂ :=
  (v.1 : ℂ) • g + (v.2.1 : ℂ) • (g ∣[((2*m:ℕ):ℤ)] T) +
    (v.2.2 : ℂ) • obstruction m g

def stepT (v : Coefficients) : Coefficients := (-v.2.1, v.1+v.2.1, v.2.2)
def stepTi (v : Coefficients) : Coefficients := (v.1+v.2.1, -v.1, v.2.2)
def stepS (v : Coefficients) : Coefficients := (-v.1, -v.2.1, v.2.1+v.2.2)

variable (m : ℕ) (g : ℍ → ℂ)
  (hT : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=(g ∣[((2*m:ℕ):ℤ)] T)-g)
  (hS : g ∣[((2*m:ℕ):ℤ)] S = -g)

include hT hS

theorem combo_T (v : Coefficients) :
    combo m g v ∣[((2*m:ℕ):ℤ)] T=combo m g (stepT v) := by
  have hH := (obstruction_invariant m g hT hS).2
  simp only [combo, SlashAction.add_slash, ModularForm.SL_smul_slash, hT, hH, stepT]
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg, Int.cast_add]
  ring

theorem combo_S (v : Coefficients) :
    combo m g v ∣[((2*m:ℕ):ℤ)] S=combo m g (stepS v) := by
  have hH := (obstruction_invariant m g hT hS).1
  have hTS : (g ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] S =
      obstruction m g-(g ∣[((2*m:ℕ):ℤ)] T) := by
    unfold obstruction
    abel
  simp only [combo, SlashAction.add_slash, ModularForm.SL_smul_slash, hS, hTS, hH, stepS]
  ext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_neg, Int.cast_add]
  ring

theorem combo_Tinv (v : Coefficients) :
    combo m g v ∣[((2*m:ℕ):ℤ)] T⁻¹=combo m g (stepTi v) := by
  have hi : stepT (stepTi v)=v := by
    rcases v with ⟨a,b,c⟩
    simp [stepT, stepTi]
  have hh := congrArg (fun f : ℍ → ℂ => f ∣[((2*m:ℕ):ℤ)] T⁻¹)
    (combo_T m g hT hS (stepTi v))
  simpa only [hi, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using hh.symm

theorem combo_Tpow (n : ℕ) (v : Coefficients) :
    combo m g v ∣[((2*m:ℕ):ℤ)] (T^n)=combo m g ((stepT^[n]) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', SlashAction.slash_mul, combo_T m g hT hS, ih,
      Function.iterate_succ_apply]

theorem combo_Tinv_pow (n : ℕ) (v : Coefficients) :
    combo m g v ∣[((2*m:ℕ):ℤ)] ((T⁻¹)^n)=combo m g ((stepTi^[n]) v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', SlashAction.slash_mul, combo_Tinv m g hT hS, ih,
      Function.iterate_succ_apply]

def translate : ℤ → Coefficients → Coefficients
  | .ofNat n => stepT^[n]
  | .negSucc n => stepTi^[n+1]

theorem combo_translate (q : ℤ) (v : Coefficients) :
    combo m g v ∣[((2*m:ℕ):ℤ)] (T^q)=combo m g (translate q v) := by
  cases q with
  | ofNat n => simpa only [translate, Int.ofNat_eq_natCast, zpow_natCast] using combo_Tpow m g hT hS n v
  | negSucc n =>
    simpa only [translate, zpow_negSucc, inv_pow] using combo_Tinv_pow m g hT hS (n+1) v

def wordMatrix : List ℤ → ℤ → SL(2,ℤ)
  | [], q => T^q
  | q::qs, t => (T^q*S)*wordMatrix qs t

def wordCoefficients : List ℤ → ℤ → Coefficients → Coefficients
  | [], q, v => translate q v
  | q::qs, t, v => wordCoefficients qs t (stepS (translate q v))

/-- Exact action of any certified S,T word on the actual three-function
orbit; this remains valid when those functions are linearly dependent. -/
theorem combo_word (qs : List ℤ) (t : ℤ) (v : Coefficients) :
    combo m g v ∣[((2*m:ℕ):ℤ)] wordMatrix qs t=combo m g (wordCoefficients qs t v) := by
  induction qs generalizing v with
  | nil => exact combo_translate m g hT hS t v
  | cons q qs ih =>
    simp only [wordMatrix, SlashAction.slash_mul, combo_translate m g hT hS,
      combo_S m g hT hS, ih, wordCoefficients]

theorem original_word (qs : List ℤ) (t : ℤ) :
    g ∣[((2*m:ℕ):ℤ)] wordMatrix qs t=combo m g (wordCoefficients qs t (1,0,0)) := by
  simpa only [combo, Int.cast_one, Int.cast_zero, one_smul, zero_smul, add_zero]
    using combo_word m g hT hS qs t (1,0,0)

#print axioms combo_T
#print axioms combo_S
#print axioms combo_Tinv
#print axioms original_word

end SmallLevelThirtySix
