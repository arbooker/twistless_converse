module

public import QuantitativeMaassNewRamifiedEquationV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticFreshMatrices QuantitativeNinaMaass AsymptoticOrbitDecode AsymptoticIntegralSubgroup

namespace QuantitativeMaass

/-- At a repeated divisor, the second actual trace-new equation is
exactly the vanishing ramified sum on continuous representatives. -/
theorem repeated_fricke_trace_ramified_zero (M q : ℕ) (hM : 0<M) (hq : 0<q)
    (hqM : q∣M) [NeZero (q*M)]
    (f : AutomorphicL2.representatives (gamma (q*M)) (quotientMeasure (q*M)))
    (hf : Continuous f.val)
    (ht : levelTrace (Nat.dvd_mul_left M q)
      (frickeIsometry (q*M) (Nat.mul_pos hq hM) (AutomorphicL2.denseEmbedding _ _ f))=0)
    (z : ℍ) : ∑ a : Fin q,f.val (ramifiedLabel q hq a • z)=0 := by
  let W := frickeLabel (q*M) (Nat.mul_pos hq hM)
  have ht' : levelTrace (Nat.dvd_mul_left M q)
      (AutomorphicL2.denseEmbedding _ _ (frickeRepresentative (q*M) (Nat.mul_pos hq hM) f))=0 := by
    rwa [←frickeIsometry_apply]
  have he := congrFun ((continuous_trace_zero_iff (Nat.dvd_mul_left M q)
    (frickeRepresentative (q*M) (Nat.mul_pos hq hM) f)
    (frickeRepresentative_continuous (q*M) (Nat.mul_pos hq hM) f hf)).mp ht')
      (W • ((dilationLabel q hq)⁻¹ • z))
  rw [ramified_levelTrace_formula M q hM hq hqM] at he
  have hw (j : Fin q) : W*(integralLabel (lowerSL M (j.val:ℤ)))⁻¹=
      translationLabel ((j.val:ℚ)/q)*W := by
    rw [←map_inv,lowerSL_inv]
    simpa only [Int.cast_neg,Int.cast_natCast,neg_neg] using
      fricke_lower_div M q hM hq (-(j.val:ℤ))
  have hb (j : Fin q) :
      (frickeRepresentative (q*M) (Nat.mul_pos hq hM) f).val
        ((integralLabel (lowerSL M (j.val:ℤ)))⁻¹ • (W • ((dilationLabel q hq)⁻¹ • z)))=
      f.val (ramifiedLabel q hq j • z) := by
    change f.val (W • ((integralLabel (lowerSL M (j.val:ℤ)))⁻¹ •
      (W • ((dilationLabel q hq)⁻¹ • z))))=_
    rw [←mul_smul,hw,mul_smul]
    have hWW : W*W=1 := frickeLabel_mul_self (q*M) (Nat.mul_pos hq hM)
    rw [←mul_smul W W,hWW,one_smul,←mul_smul,←ramifiedLabel_mul_dilation q hq j,mul_inv_cancel_right]
  simpa only [hb,Pi.zero_apply] using he

/-- Every genuine new vector at a square-divisible prime has zero U_p
on its continuous representative, without any Laplace equation. -/
theorem newSpace_repeated_ramified_zero (N p : ℕ) (hN : 0<N) (hp : p.Prime)
    (hp2 : p^2∣N) [NeZero N]
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hx : AutomorphicL2.denseEmbedding _ _ f ∈ newSpace N hN)
    (z : ℍ) : ∑ a : Fin p,f.val (ramifiedLabel p hp.pos a • z)=0 := by
  have hpN : p∣N := (dvd_pow_self p (by decide : 2≠0)).trans hp2
  simp only [newSpace,Submodule.mem_iInf] at hx
  have ht := hx ⟨p,hp,hpN⟩
  obtain ⟨M,rfl⟩ := hpN
  have hM : 0<M := Nat.pos_of_mul_pos_left hN
  have hpM : p∣M := by
    rw [pow_two] at hp2
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos hp2
  have hd : p*M/p=M := Nat.mul_div_cancel_left M hp.pos
  have ht' : levelTrace (Nat.dvd_mul_left M p)
      (frickeIsometry (p*M) (Nat.mul_pos hp.pos hM) (AutomorphicL2.denseEmbedding _ _ f))=0 := by
    have hk : AutomorphicL2.denseEmbedding _ _ f ∈
        newTraceKernel (Nat.mul_pos hp.pos hM) (Nat.dvd_mul_left M p) := by
      simpa only [hd] using ht
    exact hk.2
  exact repeated_fricke_trace_ramified_zero M p hM hp.pos hpM f hf ht' z

#print axioms repeated_fricke_trace_ramified_zero
#print axioms newSpace_repeated_ramified_zero

end QuantitativeMaass
