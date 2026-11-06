module

public import QuantitativeArithmeticSmallLevelThirtyFiveSixRowAnalyticV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

theorem coordinate_zero_of_germ {G : ℂ → Fin 210 → ℂ} {x : ℂ}
    {v : Fin 210 → ℂ} (hv : IsLeadingVector G x v) (i : Fin 210)
    (hi : HasAnalyticGerm (fun z => G z i) x) : v i=0 := by
  obtain ⟨H,hH,he⟩ := hi
  let A : ℂ → Fin 210 → ℂ := fun _ j => if j=i then 1 else 0
  have hs (z : ℂ) (u : Fin 210 → ℂ) : (∑ j, A z j*u j)=u i := by simp [A]
  have he' : (fun z => ∑ j, A z j*G z j)=ᶠ[𝓝[≠] x] H := by simpa only [hs] using he
  simpa only [hs] using hv.2 A H (fun _ => analyticAt_const) hH he'

theorem heckeTwo_explicit (m : ℕ) (f : ℕ → ℂ) (t : ℤ) (s : ℂ)
    (v : Fin 210 → ℂ) : fullHeckeRow m f 2 t s v=
      v (gridIndex t)+v (gridIndex (t+105))-
      ((Real.sqrt 2:ℂ)*f 2)/(primeParameter 2 m s)*v (gridIndex (2*t))+
      (primeParameter 2 m s)⁻¹^2*v (gridIndex (4*t)) := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,hp,div_eq_mul_inv]

theorem pole_hecke_two {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G x v) (t : ℤ) :
    v (gridIndex t)+v (gridIndex (t+105))-
      ((Real.sqrt 2:ℂ)*f 2)/(primeParameter 2 m x)*v (gridIndex (2*t))+
      (primeParameter 2 m x)⁻¹^2*v (gridIndex (4*t))=0 := by
  let A : ℂ → Fin 210 → ℂ := fun z j =>
    (if j=gridIndex t then 1 else 0)+(if j=gridIndex (t+105) then 1 else 0)-
    ((Real.sqrt 2:ℂ)*f 2)/(primeParameter 2 m z)*(if j=gridIndex (2*t) then 1 else 0)+
    (primeParameter 2 m z)⁻¹^2*(if j=gridIndex (4*t) then 1 else 0)
  have hA (j : Fin 210) : AnalyticAt ℂ (fun z => A z j) x := by
    have hp := (primeParameter_analytic 2 m (by decide) x).inv
      (primeParameter_ne_zero 2 m (by decide) x)
    dsimp only [A]
    simp only [div_eq_mul_inv]
    exact (analyticAt_const.sub ((analyticAt_const.mul hp).mul analyticAt_const)).add
      ((hp.pow 2).mul analyticAt_const)
  have hs (z : ℂ) (u : Fin 210 → ℂ) : (∑ j, A z j*u j)=fullHeckeRow m f 2 t z u := by
    rw [heckeTwo_explicit]
    simp [A,add_mul,sub_mul,mul_assoc,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have he := original_full_hecke_germs hm hf BG G hG hGF
    (p:=2) (by decide) (by decide) t x
  have he' : (fun z => ∑ j, A z j*G z j)=ᶠ[𝓝[≠] x] (fun _ => 0) := by
    simpa only [hs] using he
  have hh := hv.2 A (fun _ => 0) hA analyticAt_const he'
  simpa only [hs,heckeTwo_explicit] using hh

#print axioms coordinate_zero_of_germ
#print axioms pole_hecke_two
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
