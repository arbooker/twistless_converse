module

public import SpanningClassicalZonesV1

set_option autoImplicit false

@[expose] public section

namespace SpanningClassicalZones

open Set SpanningProjectedWords SpanningExceptionalSet

/-- A point outside the exceptional set has a neighborhood on which all
sufficiently large diagonal trace words are periodic. -/
theorem local_periodicity {A : Type*} {Q p r P i₀ : ℕ}
    (hQ : 0<Q) (hp : 2≤p) (hr : 2≤r) (W : ℕ → ℤ → A)
    (hperiod : ∀ m n, Tower p r m → Tower p r n → ∀ (l : ℤ) (i : ℕ),
      i₀ ≤ i → i+P<n → W (m*((p*r)*n)) (((p*r)*n:ℕ)*l+(i+P:ℕ)) =
        W (m*((p*r)*n)) (((p*r)*n:ℕ)*l+i))
    {x : ℝ} (hx : (x:Circle) ∉ exceptional Q p r (periodicArc (p*r))) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ ∃ a₀ : ℕ, ∀ a≥a₀, ∀ j : ℕ,
      (j:ℝ)/(Q*(p*r)^a:ℕ) ∈ U → W ((p*r)^a) (j+P:ℕ)=W ((p*r)^a) j := by
  obtain ⟨b,c,l,η,hη,hlo,hup⟩ := entry_interval hx
  let m := p^b*r^c
  let D := p*r
  let U : Set ℝ := {y | η < (Q*p^b*r^c:ℕ)*(y:ℝ)-(l:ℝ) ∧
    (Q*p^b*r^c:ℕ)*(y:ℝ)-(l:ℝ)<1/(D:ℝ)-η}
  have hU : IsOpen U := (isOpen_lt continuous_const
    ((continuous_const.mul continuous_id).sub continuous_const)).inter
    (isOpen_lt ((continuous_const.mul continuous_id).sub continuous_const) continuous_const)
  obtain ⟨L,hL⟩ := exists_nat_gt (((i₀:ℝ)+P+1)/η)
  obtain ⟨a₀,ha₀⟩ := diagonal_factor hp hr b c L
  refine ⟨U,hU,⟨hlo,hup⟩,a₀,?_⟩
  intro a ha j hj
  obtain ⟨n,hn,hLn,hfac⟩ := ha₀ a ha
  have hnpos : 0<n := by omega
  have hDpos : 0<D := Nat.mul_pos (by omega) (by omega)
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hmr : (0:ℝ)<m := by dsimp [m]; positivity
  have hDr : (0:ℝ)<D := by exact_mod_cast hDpos
  have hnr : (0:ℝ)<n := by exact_mod_cast hnpos
  have hMpos : (0:ℝ)<(D*n:ℕ) := by positivity
  have hsmall : (i₀:ℝ)+P+1 < η*(n:ℝ) := by
    have hLn' : (L:ℝ)<n := by exact_mod_cast hLn
    have he := (div_lt_iff₀ hη).mp (hL.trans hLn')
    nlinarith
  have hD1 : (1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hscale : η*(n:ℝ) ≤ η*(D*n:ℕ) := by
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hD1) (mul_nonneg hη.le hnr.le)]
  have hratio : (Q*p^b*r^c:ℕ)*((j:ℝ)/(Q*(p*r)^a:ℕ))=(j:ℝ)/(D*n:ℕ) := by
    have hfac' : (p*r)^a=m*(D*n) := hfac
    rw [hfac']
    have he : Q*p^b*r^c=Q*m := by dsimp [m]; ring
    rw [he]
    push_cast
    field_simp
  change η < (Q*p^b*r^c:ℕ)*((j:ℝ)/(Q*(p*r)^a:ℕ))-(l:ℝ) ∧
    (Q*p^b*r^c:ℕ)*((j:ℝ)/(Q*(p*r)^a:ℕ))-(l:ℝ)<1/(D:ℝ)-η at hj
  rw [hratio] at hj
  have hlow := (lt_div_iff₀ hMpos).mp (show η+(l:ℝ)<(j:ℝ)/(D*n:ℕ) by linarith [hj.1])
  have hupp := (div_lt_iff₀ hMpos).mp
    (show (j:ℝ)/(D*n:ℕ)<1/(D:ℝ)-η+(l:ℝ) by linarith [hj.2])
  have hid : (1/(D:ℝ))*(D*n:ℕ)=(n:ℝ) := by push_cast; field_simp
  obtain ⟨i,hi,hend,hji⟩ := digit_of_ratio hDpos hnpos l
    (show (i₀:ℝ)≤(j:ℝ)-(D*n:ℕ)*(l:ℝ) by nlinarith)
    (show (j:ℝ)-(D*n:ℕ)*(l:ℝ)+(P:ℝ)<n by nlinarith)
  have hh := hperiod m n ⟨b,c,rfl⟩ hn l i hi hend
  rw [← hfac] at hh
  have hj0 : (((p*r)*n:ℕ):ℤ)*l+i=(j:ℤ) := by simpa [D] using hji.symm
  have hjP : (((p*r)*n:ℕ):ℤ)*l+(i+P:ℕ)=(j+P:ℕ) := by
    push_cast
    push_cast at hj0
    linarith
  rw [hjP,hj0] at hh
  exact hh

#print axioms local_periodicity

end SpanningClassicalZones
