module

public import AsymptoticSectorSignsV1
public import AsymptoticCylinderSectorsV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRamifiedSectors

open AsymptoticSectorSigns AsymptoticCylinder
open FinitenessCertificate FinitenessGlobalHeight FinitenessOriginalInput

/-- The two kinds of ramified Fourier rows in the manuscript. No
good-prime Euler relation is imposed on this linear space. -/
def ramifiedRows (N h : ℕ) (e : Sector N) : Submodule ℂ (ℕ → ℂ) where
  carrier := {a |
    (∀ p : ℕ, p∈simplePrimes N → ∀ n : ℕ, a (p*n)=delta e p*(p:ℂ)^h*a n) ∧
    (∀ p : ℕ, p.Prime → p^2∣N → ∀ n : ℕ, a (p*n)=0)}
  zero_mem' := ⟨fun _ _ _ => by simp,fun _ _ _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨has,haq⟩ ⟨hbs,hbq⟩
    constructor
    · intro p hp n
      simp only [Pi.add_apply,has p hp n,hbs p hp n,mul_add]
    · intro p hp hpsq n
      simp only [Pi.add_apply,haq p hp hpsq n,hbq p hp hpsq n,add_zero]
  smul_mem' := by
    rintro c a ⟨has,haq⟩
    constructor
    · intro p hp n
      simp only [Pi.smul_apply,smul_eq_mul,has p hp n]
      ring
    · intro p hp hpsq n
      simp only [Pi.smul_apply,smul_eq_mul,haq p hp hpsq n,mul_zero]

/-- Coefficient realization of a fixed geometric sector: all positive
Ramanujan laws with their coherent signs and all ramified rows. The
degree d will be furnished uniformly by the direct-height certificate. -/
noncomputable def sector (N h d : ℕ) (e : Sector N) :
    Submodule ℂ (coefficientSpace d) where
  carrier := {a |
    (∀ Q : ℕ, 0<Q → a∈coefficientSector N Q (multiplier e) (h+1) d) ∧
    a.val∈ramifiedRows N h e}
  zero_mem' := ⟨fun Q _ => (coefficientSector N Q (multiplier e) (h+1) d).zero_mem,
    (ramifiedRows N h e).zero_mem⟩
  add_mem' := by
    rintro a b ⟨has,har⟩ ⟨hbs,hbr⟩
    exact ⟨fun Q hQ => (coefficientSector N Q (multiplier e) (h+1) d).add_mem
      (has Q hQ) (hbs Q hQ),(ramifiedRows N h e).add_mem har hbr⟩
  smul_mem' := by
    rintro c a ⟨has,har⟩
    exact ⟨fun Q hQ => (coefficientSector N Q (multiplier e) (h+1) d).smul_mem c (has Q hQ),
      (ramifiedRows N h e).smul_mem c har⟩

theorem sector_le_finiteLaw (N h d : ℕ) (e : Sector N) {Q : ℕ} (hQ : 0<Q) :
    sector N h d e≤coefficientSector N Q (multiplier e) (h+1) d := fun _ ha => ha.1 Q hQ

theorem sector_finiteDimensional {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h d : ℕ) (e : Sector N) :
    FiniteDimensional ℂ (sector N h d e) := by
  let _ : FiniteDimensional ℂ (coefficientSector N Q (multiplier e) (h+1) d) :=
    coefficientSector_finiteDimensional hN A P (multiplier e) (h+1) d (by omega)
      (fun q _ => multiplier_norm e q)
  let j := Submodule.inclusion (sector_le_finiteLaw N h d e hQ)
  apply FiniteDimensional.of_injective (V₂:=coefficientSector N Q (multiplier e) (h+1) d) j
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun x : coefficientSector N Q (multiplier e) (h+1) d => x.val) hab

noncomputable def cylinderMap (N h d t : ℕ) (e : Sector N) {ε : ℝ}
    (hε : 0<ε) (hd : 2*d+4≤2*h+2*t+1) :
    sector N h d e →ₗ[ℂ] holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) hε :=
  (fourierMap (2*h) t d (by positivity) hε hd).comp (sector N h d e).subtype

theorem cylinderMap_injective (N h d t : ℕ) (e : Sector N) {ε : ℝ}
    (hε : 0<ε) (hd : 2*d+4≤2*h+2*t+1) :
    Function.Injective (cylinderMap N h d t e hε hd) :=
  (fourierMap_injective (2*h) t d (by positivity) hε hd).comp Subtype.val_injective

theorem cylinderMap_finrank (N h d t : ℕ) (e : Sector N) {ε : ℝ}
    (hε : 0<ε) (hd : 2*d+4≤2*h+2*t+1) :
    Module.finrank ℂ (LinearMap.range (cylinderMap N h d t e hε hd))=
      Module.finrank ℂ (sector N h d e) :=
  LinearMap.finrank_range_of_inj (cylinderMap_injective N h d t e hε hd)

/-- Every original complex Euler solution belongs to one of the actual
Fricke-and-ramified-sign sectors, with all positive twist equations and
all ramified rows. The index set is independent of the chosen certificate. -/
theorem euler_cover {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
    (A : Certificate N Q hQ) (P : Parameters A) (h : ℕ) (f : S N (2*(h+1))) :
    ∃ e : Sector N, eulerCoefficients hN A P (h+1) f∈sector N h (h+1+P.s) e := by
  obtain ⟨e,hd,hFE⟩ := AsymptoticSectorSigns.euler_sector hN f.property
  obtain ⟨τ,_,hg⟩ := f.property.growth
  refine ⟨e,?_,?_,?_⟩
  · intro Q' hQ'
    exact FinitenessTwistedAnalyticBridge.disk_mem_space hN hQ' f.property.zero hg
      (fun q hq => hFE q (Nat.pos_of_dvd_of_pos hq hQ'))
  · intro p hp n
    change FinitenessOriginalFourier.fullCoefficients f.val (2*(h+1)) (p*n)=
      delta e p*(p:ℂ)^h*FinitenessOriginalFourier.fullCoefficients f.val (2*(h+1)) n
    rw [hd p hp]
    obtain ⟨hp',hpN,_⟩ := mem_simplePrimes.mp hp
    exact AsymptoticRamifiedCoefficients.simple_relation f.property.toEulerData hp' hpN h n
  · intro p hp hpsq n
    exact AsymptoticRamifiedCoefficients.square_relation f.property.toEulerData hp hpsq (2*(h+1)) n

#print axioms sector_finiteDimensional
#print axioms cylinderMap_finrank
#print axioms euler_cover

end AsymptoticRamifiedSectors
