module
public import QuantitativeArithmeticIntegerSevenLaurentRowsTheoryV4
set_option autoImplicit false
set_option maxHeartbeats 0
@[expose] public noncomputable section

namespace QuantitativeArithmeticExponentEncoding
open QuantitativeArithmeticIntegerSevenLaurentRows

def coordinates (e : Exponent) : List ℕ :=
  [e.1.toNat,e.2.1.toNat,e.2.2.1.toNat,e.2.2.2.1.toNat,
   e.2.2.2.2.1,e.2.2.2.2.2.1,e.2.2.2.2.2.2]

def encodeDigits : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 64 * encodeDigits ds

def decodeDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n+1, code => code % 64 :: decodeDigits n (code / 64)

def encode (e : Exponent) : ℕ := encodeDigits (coordinates e)

def fromDigits (ds : List ℕ) : Exponent :=
  ((ds[0]! : ℤ),(ds[1]! : ℤ),(ds[2]! : ℤ),(ds[3]! : ℤ),ds[4]!,ds[5]!,ds[6]!)

def decode (code : ℕ) : Exponent := fromDigits (decodeDigits 7 code)

def Nonnegative (e : Exponent) : Prop :=
  0 ≤ e.1 ∧ 0 ≤ e.2.1 ∧ 0 ≤ e.2.2.1 ∧ 0 ≤ e.2.2.2.1

def Small (e : Exponent) : Prop :=
  Nonnegative e ∧ e.1 < 32 ∧ e.2.1 < 32 ∧ e.2.2.1 < 32 ∧ e.2.2.2.1 < 32 ∧
    e.2.2.2.2.1 < 32 ∧ e.2.2.2.2.2.1 < 32 ∧ e.2.2.2.2.2.2 < 32

instance (e : Exponent) : Decidable (Small e) := by
  unfold Small Nonnegative
  infer_instance

theorem decodeDigits_encode (ds : List ℕ) (h : ∀ d ∈ ds, d < 64) :
    decodeDigits ds.length (encodeDigits ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      have hd : d < 64 := h d (by simp)
      have ht : ∀ a ∈ ds, a < 64 := fun a ha => h a (by simp [ha])
      have hm : (d + 64 * encodeDigits ds) % 64 = d := by omega
      have hq : (d + 64 * encodeDigits ds) / 64 = encodeDigits ds := by omega
      simp only [List.length_cons,encodeDigits,decodeDigits,hm,hq,ih ht]

theorem fromDigits_coordinates (e : Exponent) (h : Nonnegative e) :
    fromDigits (coordinates e) = e := by
  rcases e with ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆⟩
  simp only [Nonnegative] at h
  have h₀ : (e₀.toNat : ℤ) = e₀ := by omega
  have h₁ : (e₁.toNat : ℤ) = e₁ := by omega
  have h₂ : (e₂.toNat : ℤ) = e₂ := by omega
  have h₃ : (e₃.toNat : ℤ) = e₃ := by omega
  simp [fromDigits,coordinates,h₀,h₁,h₂,h₃]

theorem decode_encode (e : Exponent) (h : Nonnegative e)
    (hb : ∀ d ∈ coordinates e, d < 64) : decode (encode e) = e := by
  have hd := decodeDigits_encode (coordinates e) hb
  change decodeDigits 7 (encode e) = coordinates e at hd
  exact congrArg fromDigits hd |>.trans (fromDigits_coordinates e h)

theorem encode_add (e f : Exponent) (he : Nonnegative e) (hf : Nonnegative f) :
    encode (exponentAdd e f) = encode e + encode f := by
  rcases e with ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆⟩
  rcases f with ⟨f₀,f₁,f₂,f₃,f₄,f₅,f₆⟩
  simp only [Nonnegative] at he hf
  have h₀ : (e₀+f₀).toNat = e₀.toNat+f₀.toNat := by omega
  have h₁ : (e₁+f₁).toNat = e₁.toNat+f₁.toNat := by omega
  have h₂ : (e₂+f₂).toNat = e₂.toNat+f₂.toNat := by omega
  have h₃ : (e₃+f₃).toNat = e₃.toNat+f₃.toNat := by omega
  simp only [encode,coordinates,exponentAdd,encodeDigits,h₀,h₁,h₂,h₃]
  omega

theorem decode_add (e f : Exponent) (he : Small e) (hf : Small f) :
    decode (encode e + encode f) = exponentAdd e f := by
  rw [← encode_add e f he.1 hf.1]
  apply decode_encode
  · simp only [Nonnegative,exponentAdd]
    rcases he.1 with ⟨h₀,h₁,h₂,h₃⟩
    rcases hf.1 with ⟨g₀,g₁,g₂,g₃⟩
    omega
  · rcases e with ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆⟩
    rcases f with ⟨f₀,f₁,f₂,f₃,f₄,f₅,f₆⟩
    simp only [Small,Nonnegative] at he hf
    simp only [coordinates,exponentAdd,List.mem_cons,List.not_mem_nil,or_false,
      forall_eq_or_imp,forall_eq]
    omega

#print axioms decode_encode
#print axioms encode_add
#print axioms decode_add
end QuantitativeArithmeticExponentEncoding
