module

public import AsymptoticFreshCRTResiduesV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFreshCRT

open Matrix AsymptoticFreshMatrices

/-- Select a nonzero residue by an integer translation, retaining the
exact quotient needed for the row and column operations. -/
theorem negative_residue (q : ℕ) (hq : 1<q) (z : ℤ) (hz : ¬(q:ℤ)∣z) :
    ∃ a u : ℤ,0<a ∧ a<(q:ℤ) ∧ z+(q:ℤ)*u= -a := by
  have hp : (0:ℤ)<q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hn : ¬(q:ℤ)∣-z := by simpa using hz
  refine ⟨(-z)%(q:ℤ),(-z)/(q:ℤ),
    (Int.emod_pos_of_not_dvd hn).resolve_left hp.ne',Int.emod_lt_of_pos _ hp,?_⟩
  have he := Int.mul_ediv_add_emod (-z) (q:ℤ)
  linarith

theorem first_column_nonzero_mod (N q : ℕ) (hq : 1<q) (b c d : ℤ)
    (hdet : (q:ℤ)*d-(N:ℤ)*c*b=1) : ¬(q:ℤ)∣c := by
  intro hc
  have hh : (q:ℤ)∣(q:ℤ)*d-(N:ℤ)*c*b := dvd_sub (dvd_mul_right _ _)
    ((hc.trans (dvd_mul_left c (N:ℤ))).trans (dvd_mul_right _ b))
  rw [hdet] at hh
  have hn : q∣1 := by exact_mod_cast hh
  exact (Nat.ne_of_gt hq) (Nat.dvd_one.mp hn)

theorem first_row_nonzero_mod (N q : ℕ) (hq : 1<q) (b c d : ℤ)
    (hdet : (q:ℤ)*d-(N:ℤ)*c*b=1) : ¬(q:ℤ)∣b := by
  intro hb
  have hh : (q:ℤ)∣(q:ℤ)*d-(N:ℤ)*c*b := dvd_sub (dvd_mul_right _ _)
    (hb.trans (dvd_mul_left b ((N:ℤ)*c)))
  rw [hdet] at hh
  have hn : q∣1 := by exact_mod_cast hh
  exact (Nat.ne_of_gt hq) (Nat.dvd_one.mp hn)

def upper (u : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1,u;0,1]
def lower (N : ℕ) (u : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1,0;(N:ℤ)*u,1]

/-- The manuscript's canonical reduction, with explicit left and
right transvections. Once the first entry is q, determinant one forces
both selected residues to be nonzero. No prime-distribution statement
is used in this algebraic step. -/
theorem canonical_reduction (N q : ℕ) (hq : 1<q) (a₀ b₀ c₀ d₀ t : ℤ)
    (hdet : a₀*d₀-(N:ℤ)*c₀*b₀=1) (hqeq : a₀+(N:ℤ)*c₀*t=(q:ℤ)) :
    ∃ a b c u v : ℤ,0<a ∧ a<(q:ℤ) ∧ 0<b ∧ b<(q:ℤ) ∧
      (q:ℤ)*c=(N:ℤ)*a*b+1 ∧
      lower N v * upper t * !![a₀,b₀;(N:ℤ)*c₀,d₀] * upper u=canonicalEntries N q a b c := by
  let b₁ := b₀+t*d₀
  have hdet' : (q:ℤ)*d₀-(N:ℤ)*c₀*b₁=1 := by
    dsimp only [b₁]
    linear_combination hdet-d₀*hqeq
  obtain ⟨a,v,ha0,haq,hav⟩ := negative_residue q hq c₀
    (first_column_nonzero_mod N q hq b₁ c₀ d₀ hdet')
  obtain ⟨b,u,hb0,hbq,hbu⟩ := negative_residue q hq b₁
    (first_row_nonzero_mod N q hq b₁ c₀ d₀ hdet')
  let c := (N:ℤ)*v*b₁+d₀-(N:ℤ)*a*u
  have hc : (q:ℤ)*c=(N:ℤ)*a*b+1 := by
    dsimp only [c]
    linear_combination hdet'+(N:ℤ)*b₁*hav-(N:ℤ)*a*hbu
  refine ⟨a,b,c,u,v,ha0,haq,hb0,hbq,hc,?_⟩
  have he : upper t * !![a₀,b₀;(N:ℤ)*c₀,d₀]=!![(q:ℤ),b₁;(N:ℤ)*c₀,d₀] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upper,Matrix.mul_apply,Fin.sum_univ_two,b₁]
    nlinarith [hqeq]
  rw [mul_assoc (lower N v) (upper t),he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower,upper,canonicalEntries,Matrix.mul_apply,Fin.sum_univ_two,c]
  · linear_combination hbu
  · linear_combination (N:ℤ)*hav
  · linear_combination (N:ℤ)*u*hav

#print axioms negative_residue
#print axioms first_column_nonzero_mod
#print axioms first_row_nonzero_mod
#print axioms canonical_reduction

end AsymptoticFreshCRT
