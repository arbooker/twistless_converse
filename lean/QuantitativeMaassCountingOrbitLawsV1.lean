module

public import QuantitativeMaassCountingOrbitRepresentativeV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceLabels AsymptoticFreshMatrices
open AsymptoticOrbitDecode AsymptoticNestedQuotients AsymptoticSectorSigns QuantitativeNewGap
open scoped lp
namespace QuantitativeMaass.CountingMetric

theorem orbitLift_mul (z : ℍ) (f : AsymptoticRationalGroup.Group→ℂ) (c : ℂ) (w : ℍ) :
    orbitLift z (fun a => c*f a) w=c*orbitLift z f w := by
  classical
  unfold orbitLift
  split_ifs <;> simp

theorem orbitLift_sum {ι : Type*} (s : Finset ι) (z : ℍ)
    (f : ι→AsymptoticRationalGroup.Group→ℂ) (w : ℍ) :
    orbitLift z (fun a => ∑ i∈s,f i a) w=∑ i∈s,orbitLift z (f i) w := by
  classical
  unfold orbitLift
  split_ifs <;> simp

theorem countingSector_ramified (N : ℕ) (hN : 0<N) (e : Sector N)
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e)
    (p : ℕ) (hp : p.Prime) (hpN : p∣N) (a : AsymptoticRationalGroup.Group) :
    (∑ j : Fin p,f (classOf (gamma N) (ramifiedLabel p hp.pos j*a)))=
      AsymptoticCylinderRamified.eigenvalue e p*f (classOf (gamma N) a) := by
  let z : ℍ := ⟨Complex.I,by simp⟩
  have hi := (AsymptoticQuotientIncidence.induction_mem_space N hN
    (by norm_num : (0:ℝ)<1) (by omega : 1≤(1:ℕ)) e z f).mp
    (countingSector_induction_mem_incidence N hN e
      (by norm_num : (0:ℝ)<1) (by omega : 1≤(1:ℕ)) z f hf)
  exact hi.2 ⟨p,hp,hpN⟩ a

/-- Every original all-modulus law holds on the counting-sector orbit
representative. This reuses only the pointwise algebraic theorem, not a
continuity assertion or an equality of L2 representatives. -/
theorem countingSector_orbit_all_laws (N : ℕ) (hN : 0<N) (e : Sector N)
    (f : ℓ²(Classes (gamma N),ℂ)) (hf : f∈countingSectorSpace N hN e)
    (z : ℍ) (hz : Function.Injective (fun a : AsymptoticRationalGroup.Group => a • z)) :
    ∀ q : ℕ,0<q → ∀ w : ℂ,
      FinitenessAnalyticReconstruction.twist (upperZeroExtension (orbitRepresentative N z hz f).val) q w=
        multiplier e q*FinitenessAnalyticReconstruction.twist
          (upperZeroExtension (orbitRepresentative N z hz f).val) q
          (-1/((Nat.lcm N (q^2):ℂ)*w)) := by
  let F := fun a : AsymptoticRationalGroup.Group => f (classOf (gamma N) a)
  apply modular_ramified_all_analytic_laws N hN (orbitRepresentative N z hz f) e
  · intro w
    change sign e.1*orbitLift z F (frickeLabel N hN • w)=orbitLift z F w
    rw [orbitLift_transport z hz,←orbitLift_mul]
    apply congrArg (fun h => orbitLift z h w)
    funext a
    exact countingSector_fricke N hN e f hf a
  · intro p hp hpN hp2 w
    change (∑ j : Fin p,orbitLift z F (ramifiedLabel p hp.pos j • w))=delta e p*orbitLift z F w
    simp_rw [orbitLift_transport z hz]
    rw [←orbitLift_sum,←orbitLift_mul]
    apply congrArg (fun h => orbitLift z h w)
    funext a
    simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_right hp2] using
      countingSector_ramified N hN e f hf p hp hpN a
  · intro p hp hp2 w
    have hpN : p∣N := (dvd_pow_self p (by decide : 2≠0)).trans hp2
    change (∑ j : Fin p,orbitLift z F (ramifiedLabel p hp.pos j • w))=0
    simp_rw [orbitLift_transport z hz]
    rw [←orbitLift_sum]
    have he : (fun a => ∑ j : Fin p,F (ramifiedLabel p hp.pos j*a))=fun _ => (0:ℂ) := by
      funext a
      simpa only [AsymptoticCylinderRamified.eigenvalue,ite_eq_left hp2,zero_mul] using
        countingSector_ramified N hN e f hf p hp hpN a
    rw [he]
    unfold orbitLift
    split_ifs <;> rfl

#print axioms orbitLift_mul
#print axioms orbitLift_sum
#print axioms countingSector_ramified
#print axioms countingSector_orbit_all_laws
end QuantitativeMaass.CountingMetric
