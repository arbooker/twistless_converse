module

public import AsymptoticWeightedBranchesV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticWeightedFE

open UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight
open FinitenessAnalyticReconstruction AsymptoticCertificateBranches
open AsymptoticCertificateOperators AsymptoticWeightedBranches

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The pointwise kernel of the actual low and terminal operators. -/
noncomputable def reconstructionValue (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (t m : ℕ) (F : ℂ → ℂ) (z : ℍ) : ℂ :=
  ∑ v : Index A, amplitude A χ v*
    (lowValue (level_pos A hN v) (inputShift A v) (outputShift A v)
      P.ε P.ρ (lowCell A P.ε v) t m F z+
    terminalValue (level_pos A hN v) (inputShift A v) (outputShift A v)
      P.ε (lowCell A P.ε v) t m F z)

theorem reconstructionValue_eq (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z) (z : ℍ) :
    reconstructionValue A hN P χ t m F z=
      ∑ v : Index A, amplitude A χ v*(lowCell A P.ε v).indicator
        (fun w : ℍ => ((w.im/P.ε)^t:ℝ)*
          AsymptoticHyperbolicSlash.phase (matrix A hN v) (2*m) w*
            ((matrix A hN v • w).im:ℂ)^m*F (matrix A hN v • w:ℍ)) z := by
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact values_eq (level_pos A hN v) (inputShift A v) (outputShift A v)
    P.epsilon_pos (lowCell A P.ε v) t m F hp z
    (fun hz => ascending A hN P v z hz.1 (show z.im<P.ε from hz.2).le)

theorem reconstruct_low (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (z : ℍ) (hz : z∈lowStrip P.ε) :
    stripSection P.ε t m F z=reconstructionValue A hN P χ t m F z := by
  classical
  rw [stripSection,Set.indicator_of_mem hz.1,
    weighted_low P.epsilon_pos t m F z (show z.im<P.ε from hz.2).le]
  rw [mul_assoc,reconstruct_strip A hN F hp χ m hFE z hz.1,Finset.mul_sum,
    reconstructionValue_eq A hN P χ t m F hp z]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : z∈cell A v
  · rw [Set.indicator_of_mem hv,Set.indicator_of_mem (show z∈lowCell A P.ε v from ⟨hv,hz.2⟩)]
    unfold amplitude
    ring
  · have hl : z∉lowCell A P.ε v := fun h => hv h.1
    rw [Set.indicator_of_notMem hv,Set.indicator_of_notMem hl,mul_zero,mul_zero]

theorem reconstructionValue_zero (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (z : ℍ) (hz : z∉lowStrip P.ε) : reconstructionValue A hN P χ t m F z=0 := by
  classical
  rw [reconstructionValue_eq A hN P χ t m F hp z]
  apply Finset.sum_eq_zero
  intro v _
  have hv : z∉lowCell A P.ε v := fun h => hz ⟨cell_subset_strip A v h.1,h.2⟩
  rw [Set.indicator_of_notMem hv,mul_zero]

/-- The original functional equations imply the literal weighted
reconstruction equation everywhere, before passing to L² equivalence
classes. Only the prescribed periodicity and twist laws are assumed. -/
theorem reconstruct (hN : 0<N) (P : Parameters A)
    (χ : ℕ → ℂ) (t m : ℕ) (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z))) (z : ℍ) :
    stripSection P.ε t m F z=(highStrip P.ε).indicator (stripSection P.ε t m F) z+
      reconstructionValue A hN P χ t m F z := by
  classical
  by_cases hz : z∈lowStrip P.ε
  · have hh : z∉highStrip P.ε := fun h =>
      (not_lt_of_ge (show P.ε≤z.im from h.2)) (show z.im<P.ε from hz.2)
    rw [Set.indicator_of_notMem hh,zero_add]
    exact reconstruct_low A hN P χ t m F hp hFE z hz
  · rw [reconstructionValue_zero A hN P χ t m F hp z hz,add_zero]
    by_cases hs : z∈AsymptoticMassTransport.strip
    · have hh : z∈highStrip P.ε := ⟨hs,show P.ε≤z.im from le_of_not_gt (fun h => hz ⟨hs,h⟩)⟩
      rw [Set.indicator_of_mem hh]
    · have hh : z∉highStrip P.ε := fun h => hs h.1
      rw [Set.indicator_of_notMem hh,stripSection,Set.indicator_of_notMem hs]

#print axioms reconstructionValue_eq
#print axioms reconstruct_low
#print axioms reconstruct

end AsymptoticWeightedFE
