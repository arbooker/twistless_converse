module

public import QuantitativeArithmeticUniversalPoleVectorV1
public import SmallLevelTwentyOneTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open SmallLevelTwentyOne
open FinitenessRamanujanSum
open scoped Topology

/-- The coefficient row of a finite sum of grid coordinates. -/
def samplingRow (S : Finset ℕ) (q : ℕ) (t : ℤ) (i : Fin 42) : ℂ :=
  ∑ a ∈ S, if i=gridIndex (t+(a:ℤ)*(42/q:ℕ)) then 1 else 0

theorem samplingRow_apply (S : Finset ℕ) (q : ℕ) (t : ℤ) (v : Fin 42 → ℂ) :
    (∑ i, samplingRow S q t i*v i)=∑ a ∈ S, v (gridIndex (t+(a:ℤ)*(42/q:ℕ))) := by
  simp only [samplingRow,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

def ramanujanLeadingRow (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t u : ℤ) (z : ℂ) (i : Fin 42) : ℂ :=
  samplingRow (residues q) q t i-
    fullTaylorCoefficient (2*m) f ε q t 0 z*samplingRow (residues q) q u i

def ramanujanShiftRow (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t u : ℤ) (n : ℕ) (z : ℂ) (i : Fin 42) : ℂ :=
  fullTaylorCoefficient (2*m) f ε q t (n+1) z*samplingRow (residues q) q u i

theorem ramanujanLeadingRow_apply (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t u : ℤ) (z : ℂ) (v : Fin 42 → ℂ) :
    (∑ i, ramanujanLeadingRow m f ε q t u z i*v i)=
      sampleSum q t v-fullTaylorCoefficient (2*m) f ε q t 0 z*sampleSum q u v := by
  simp only [ramanujanLeadingRow,sub_mul,mul_assoc,Finset.sum_sub_distrib,
    ← Finset.mul_sum,samplingRow_apply,sampleSum]

theorem ramanujanShiftRow_apply (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (q : ℕ) (t u : ℤ) (n : ℕ) (z : ℂ) (v : Fin 42 → ℂ) :
    (∑ i, ramanujanShiftRow m f ε q t u n z i*v i)=
      fullTaylorCoefficient (2*m) f ε q t (n+1) z*sampleSum q u v := by
  simp only [ramanujanShiftRow,mul_assoc,← Finset.mul_sum,samplingRow_apply,sampleSum]

/-- Every closed Ramanujan Taylor row acts on the SAME principal-part vector. -/
theorem pole_full_taylor {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (q : ℕ) (hq : 0<q) (hqQ : q∣42) (t d : ℤ) (ht : t≠0)
    (hd : (Nat.lcm 21 (q^2):ℤ)*d=(42:ℤ)^2) (htd : t∣d) :
    sampleSum q t v-fullTaylorCoefficient (2*m) f ε q t 0 x*sampleSum q (-(d/t)) v=0 := by
  obtain ⟨B,hrow⟩ := full_taylor_germs_of_law hf ε hlaw BG G hG hGF q hq hqQ t d ht hd htd
  have hA (i : Fin 42) : AnalyticAt ℂ (fun z => ramanujanLeadingRow m f ε q t (-(d/t)) z i) x :=
    analyticAt_const.sub ((fullTaylorCoefficient_analytic (2*m) f ε hq ht 0 x).mul analyticAt_const)
  have hC (n : ℕ) (i : Fin 42) : AnalyticAt ℂ (fun z => ramanujanShiftRow m f ε q t (-(d/t)) n z i) x :=
    (fullTaylorCoefficient_analytic (2*m) f ε hq ht (n+1) x).mul analyticAt_const
  have hh := hv.taylor hG hshift B (ramanujanLeadingRow m f ε q t (-(d/t)))
    (ramanujanShiftRow m f ε q t (-(d/t))) (fullTaylorError (2*m) f ε q t)
    hA hC (fun n z hz => (hrow n).1 z hz)
    (fun n hn => by simpa only [ramanujanLeadingRow_apply,ramanujanShiftRow_apply] using (hrow n).2 x hn)
  simpa only [ramanujanLeadingRow_apply] using hh

theorem pole_full_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (q : ℕ) (hq : 0<q) (hqQ : q∣42) : sampleSum q 0 v=0 := by
  obtain ⟨hH,he⟩ := original_full_entire_germs hm hf BG G hG hGF hq hqQ
  let A : ℂ → Fin 42 → ℂ := fun _ => samplingRow (residues q) q 0
  have hh := hv.2 A _ (fun _ => analyticAt_const) (hH x)
    (by simpa only [A,samplingRow_apply,sampleSum] using he x)
  simpa only [A,samplingRow_apply,sampleSum] using hh

def heckeCoefficientRow (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (t : ℤ)
    (z : ℂ) (i : Fin 42) : ℂ :=
  samplingRow (Finset.range p) p t i-
    ((Real.sqrt p:ℂ)*f p)*(p:ℂ)^((m:ℂ)-z)*(if i=gridIndex ((p:ℤ)*t) then 1 else 0)+
    if p∣21 then 0 else ((p:ℂ)^((m:ℂ)-z))^(2:ℕ)*(if i=gridIndex ((p:ℤ)^2*t) then 1 else 0)

theorem heckeCoefficientRow_apply (m : ℕ) (f : ℕ → ℂ) (p : ℕ) (t : ℤ)
    (z : ℂ) (v : Fin 42 → ℂ) :
    (∑ i, heckeCoefficientRow m f p t z i*v i)=fullHeckeRow m f p t z v := by
  by_cases hb : p∣21
  · simp [heckeCoefficientRow,fullHeckeRow,hb,add_mul,sub_mul,mul_assoc,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,samplingRow_apply,completeSum]
  · simp [heckeCoefficientRow,fullHeckeRow,hb,add_mul,sub_mul,mul_assoc,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,samplingRow_apply,completeSum]

theorem heckeCoefficientRow_analytic (m : ℕ) (f : ℕ → ℂ) {p : ℕ} (hp : 0<p)
    (t : ℤ) (x : ℂ) (i : Fin 42) : AnalyticAt ℂ (fun z => heckeCoefficientRow m f p t z i) x := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  have hP : AnalyticAt ℂ (fun z : ℂ => (p:ℂ)^((m:ℂ)-z)) x := by
    simp_rw [Complex.cpow_def_of_ne_zero hp0]
    fun_prop
  unfold heckeCoefficientRow
  apply (analyticAt_const.sub ((analyticAt_const.mul hP).mul analyticAt_const)).add
  by_cases hb : p∣21
  · simpa only [ite_eq_left hb] using (analyticAt_const (v := (0:ℂ)))
  · simpa only [ite_eq_right hb] using (hP.fun_pow 2).fun_mul
      (analyticAt_const (v := (if i=gridIndex ((p:ℤ)^2*t) then (1:ℂ) else 0)))

/-- All good and bad Hecke rows retain their original eigenvalues. -/
theorem pole_full_hecke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 42 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 42 → ℂ) (hv : IsLeadingVector G x v)
    (p : ℕ) (hp : p.Prime) (hpQ : p∣42) (t : ℤ) : fullHeckeRow m f p t x v=0 := by
  have he := original_full_hecke_germs hm hf BG G hG hGF hp hpQ t x
  have hh := hv.2 (heckeCoefficientRow m f p t) (fun _ => 0)
    (heckeCoefficientRow_analytic m f hp.pos t x) analyticAt_const
    (by simpa only [heckeCoefficientRow_apply] using he)
  simpa only [heckeCoefficientRow_apply] using hh

#print axioms pole_full_taylor
#print axioms pole_full_entire
#print axioms pole_full_hecke
end SmallLevelTwentyOneKnownWords
