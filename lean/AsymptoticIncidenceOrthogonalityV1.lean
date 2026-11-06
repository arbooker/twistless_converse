module

public import AsymptoticCosetSectorOrthogonalityV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public section

namespace AsymptoticQuotientIncidence

open UpperHalfPlane AsymptoticCongruenceQuotient AsymptoticCongruenceStrip
open AsymptoticSectorSigns AsymptoticOrbitDecode InnerProductSpace
open scoped lp InnerProduct

/-- Distinct actual incidence sectors are orthogonal. The proof uses the
normalizing Fricke and simple-prime Atkin--Lehner permutations after the
normalized counting-coset isometry, and assumes no sector dimension formula. -/
theorem inner_eq_zero_of_ne (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e d : Sector N) (hed : e≠d) (x : ℍ)
    (v w : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hv : v∈space N hN hε ht e x) (hw : w∈space N hN hε ht d x) : ⟪v,w⟫_ℂ=0 := by
  have hqv := ((space_mem N hN hε ht e x v).mp hv).1
  have hqw := ((space_mem N hN hε ht d x w).mp hw).1
  obtain ⟨f,rfl⟩ := hqv
  obtain ⟨g,rfl⟩ := hqw
  change ⟪induction N hε ht x f,induction N hε ht x g⟫_ℂ=0
  rw [(induction N hε ht x).inner_map_map]
  have hf := (induction_mem_space N hN hε ht e x f).mp hv
  have hg := (induction_mem_space N hN hε ht d x g).mp hw
  by_cases hfr : e.1=d.1
  · have hs : e.2≠d.2 := by
      intro h
      exact hed (Prod.ext hfr h)
    obtain ⟨p,hpdiff⟩ := Function.ne_iff.mp hs
    rcases p with ⟨p,hps⟩
    obtain ⟨hp,hpN,hpsq⟩ := mem_simplePrimes.mp hps
    obtain ⟨M,rfl⟩ := hpN
    have hM : 0<M := by
      by_contra hm
      have hm0 : M=0 := by omega
      simp only [hm0,mul_zero] at hN
      omega
    have hpM : ¬p∣M := by
      intro hm
      apply hpsq
      rw [pow_two]
      exact Nat.mul_dvd_mul_left p hm
    let : Fact p.Prime := ⟨hp⟩
    have hfU (u : AsymptoticRationalGroup.Group) :
        (∑ j : Fin p,f (classOf (p*M) (ramifiedLabel p hp.pos j*u)))=
          sign (e.2 ⟨p,hps⟩)*f (classOf (p*M) u) := by
      have hh := hf.2 ⟨p,hp,Nat.dvd_mul_right p M⟩ u
      simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_right hpsq,
        AsymptoticSectorSigns.delta,dite_eq_left hps] using hh
    have hgU (u : AsymptoticRationalGroup.Group) :
        (∑ j : Fin p,g (classOf (p*M) (ramifiedLabel p hp.pos j*u)))=
          sign (d.2 ⟨p,hps⟩)*g (classOf (p*M) u) := by
      have hh := hg.2 ⟨p,hp,Nat.dvd_mul_right p M⟩ u
      simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_right hpsq,
        AsymptoticSectorSigns.delta,dite_eq_left hps] using hh
    exact AsymptoticCosetSectorOrthogonality.simple_inner_eq_zero M p hM hpM f g
      (sign e.1) (sign d.1) (e.2 ⟨p,hps⟩) (d.2 ⟨p,hps⟩) hpdiff hf.1 hg.1 hfU hgU
  · exact AsymptoticCosetSectorOrthogonality.fricke_inner_eq_zero N hN f g e.1 d.1 hfr hf.1 hg.1

theorem space_le_orthogonal (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (e d : Sector N) (hed : e≠d) (x : ℍ) :
    space N hN hε ht e x≤(space N hN hε ht d x)ᗮ := by
  intro v hv w hw
  exact inner_eq_zero_of_ne N hN hε ht d e hed.symm x w v hw hv

#print axioms inner_eq_zero_of_ne
#print axioms space_le_orthogonal

end AsymptoticQuotientIncidence
