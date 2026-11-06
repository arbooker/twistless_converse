module

public import SpanningFineDefectsV1
public import GridRationalDenominatorsV1

@[expose] public section

namespace SpanningConcentrationClosure

open SpanningActualKernel SpanningTraceAlgebra SpanningKernelDefects SpanningKernelDifferences
  SpanningFineDefects GridAdmissibleGap GridSupportGeometry GridRationalDenominators
  SpanningLevelArithmetic

variable {K : Type} [Field K]

/-- Arbitrarily large common rational concentration scales already force
one vanishing augmented kernel. No cardinality bound is needed here. -/
theorem concentration_forces_zero {N B P : ℕ} {L : Set ℕ} (hN : Admissible N)
    (hP : 0<P) (hdiv : ∀ell∈L,ell∣B) (E : Finset ℚ)
    (hconc : ∀ε:ℝ,0<ε → ∀T:ℝ,∃Q:ℕ,0<Q ∧ B∣Q ∧ T<(Q:ℝ) ∧
      ∀j∈coordinateDefects (K:=K) N L Q P,∃x∈E,|(j:ℝ)/(Q:ℝ)-(x:ℝ)|<ε) :
    ∃Q:ℕ,0<Q ∧ B∣Q ∧ ∀f:ℤ → K,Augmented N L Q f → f=0 := by
  obtain ⟨G,hG,hNG,hE⟩ := common_grid N hN.1 E
  obtain ⟨H,R,hH,hR,hdet⟩ := exists_grid_difference_detector (K:=K) hN hG hNG
  let r := G*H
  have hr : 0<r := Nat.mul_pos hG hH
  have hG' : (0:ℝ)<G := by exact_mod_cast hG
  have hH' : (0:ℝ)<H := by exact_mod_cast hH
  have hR' : (0:ℝ)<R := by exact_mod_cast hR
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  let ε : ℝ := 1/(64*R*G)
  have hε : 0<ε := by dsimp [ε]; positivity
  let T : ℝ := max (1/ε) (max (40*R*((r*P:ℕ)+1)/(3*H))
    (max (((r*P:ℕ):ℝ)*Real.sqrt N/((G:ℝ)*H)) (16*R)))
  obtain ⟨Q,hQ,hBQ,hQT,hnear⟩ := hconc ε hε T
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hQT1 : 1/ε<(Q:ℝ) := (le_max_left _ _).trans_lt hQT
  have hQT2 : 40*(R:ℝ)*((r*P:ℕ)+1)/(3*H)<Q :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hQT
  have hQT3 : (((r*P:ℕ):ℝ)*Real.sqrt N)/((G:ℝ)*H)<Q :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans_lt hQT
  have hQT4 : (16:ℝ)*R<Q :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans_lt hQT
  have hrecip : (1:ℝ)/Q<ε := by
    apply (div_lt_iff₀ hQ').mpr
    have hh := (div_lt_iff₀ hε).mp hQT1
    nlinarith
  let v := H*Q
  have hv : 0<v := Nat.mul_pos hH hQ
  have hvR : 16*R≤v := by
    have hqR : 16*R<Q := by exact_mod_cast hQT4
    dsimp [v]
    nlinarith
  have hscale : r*Q=G*v := by dsimp [r,v]; ring
  have hbuffer : ((r*P:ℕ):ℝ)<3*(v:ℝ)/(40*R)-1 := by
    apply (lt_sub_iff_add_lt).mpr
    apply (lt_div_iff₀ (by positivity : (0:ℝ)<40*R)).mpr
    have hh := (div_lt_iff₀ (by positivity : (0:ℝ)<3*H)).mp hQT2
    dsimp [v]
    push_cast
    push_cast at hh
    nlinarith
  have hroot : (0:ℝ)<Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN.1)
  have hsize : ((r*P:ℕ):ℝ)<radius N (G*v) 1 := by
    simp only [radius,level,one_pow,Nat.lcm_one_right,Nat.cast_mul]
    apply (lt_div_iff₀ hroot).mpr
    have hh := (div_lt_iff₀ (mul_pos hG' hH')).mp hQT3
    push_cast at hh
    dsimp [v]
    push_cast
    nlinarith
  refine ⟨G*v,Nat.mul_pos hG hv,hBQ.trans ?_,?_⟩
  · exact ⟨G*H,by dsimp [v]; ring⟩
  · intro f hf
    have hf' : Augmented N L (r*Q) f := by simpa only [hscale] using hf
    apply hdet v hv (dvd_mul_right H Q) hvR (r*P) f (Nat.mul_pos hr hP) hf.1 hbuffer hsize
    intro j hj
    by_contra hd
    let n : Fin (r*Q) := ⟨j.val,by simpa only [hscale] using j.isLt⟩
    obtain ⟨x,hx,hxnear⟩ := fine_defects_near hr hQ (fun ell hell => (hdiv ell hell).trans hBQ)
      hnear hf' n hd
    obtain ⟨k,hkx⟩ := hE x hx
    apply hj
    apply normalized_near_grid hG hv hR hvR j (x:ℝ) k hkx
    have hnorm : (r:ℝ)*Q=(G:ℝ)*v := by exact_mod_cast hscale
    change |(j.val:ℝ)/((r:ℝ)*Q)-(x:ℝ)|<ε+1/(Q:ℝ) at hxnear
    rw [hnorm] at hxnear
    have htwice : ε+1/(Q:ℝ)<1/(16*(R:ℝ)*G) := by
      have hi : 4*ε=1/(16*(R:ℝ)*G) := by dsimp [ε]; field_simp; norm_num
      rw [←hi]
      linarith
    exact hxnear.trans htwice

#print axioms concentration_forces_zero

end SpanningConcentrationClosure
