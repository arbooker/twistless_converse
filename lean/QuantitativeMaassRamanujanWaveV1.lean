module

public import QuantitativeMaassRamanujanPhaseV1
public import QuantitativeMaassTwistedFrickeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace QuantitativeMaass

/-- Literal primitive translation sum of the actual principal Maass wave. -/
def principalRamanujanWave (b : ℕ → ℂ) (r : ℝ) (σ q : ℕ) (z : ℝ × ℝ) : ℂ :=
  ∑ a ∈ FinitenessRamanujanSum.residues q,principalEulerWave b r σ (z.1+(a:ℝ)/q,z.2)

/-- Absolute convergence permits the finite primitive translation sum to pass
through the actual Fourier--Bessel series. -/
theorem principalEulerWave_twisted {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ q : ℕ) (z : ℝ × ℝ) (hz : 0<z.2) :
    principalEulerWave (FinitenessRamanujanFourier.twisted b q) r σ z=
      principalRamanujanWave b r σ q z := by
  have hs : ∀ a∈FinitenessRamanujanSum.residues q,
      Summable (fun n => principalEulerTerm b r σ n (z.1+(a:ℝ)/q,z.2)) :=
    fun a _ => principalEulerTerm_summable hb r σ (z.1+(a:ℝ)/q,z.2) hz
  unfold principalRamanujanWave principalEulerWave
  dsimp only
  rw [←Finset.mul_sum]
  apply congrArg (fun w : ℂ => (Real.sqrt z.2:ℂ)*w)
  unfold principalEulerCore
  change (∑' n,principalEulerTerm (FinitenessRamanujanFourier.twisted b q) r σ n (z.1,z.2))=_
  simp_rw [principalEulerTerm_twisted]
  exact Summable.tsum_finsetSum hs

/-- Original Euler solutions satisfy every literal primitive translation law,
with the coherent local root and exact lcm conductor. No twisted functional
equations, modularity, smoothness or reconstruction hypotheses are supplied. -/
theorem principal_original_ramanujan_reflections {N : ℕ} {b : ℕ → ℂ} (hN : 0<N)
    (r : ℝ) (σ : ℕ) (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧ ∀ q : ℕ,0<q → ∀ x y : ℝ,0<y →
      principalRamanujanWave b r σ q (x,y)=
        ((-1:ℂ)^σ*(FinitenessNormalizedTwistProduct.root N b q*ε))*
          principalRamanujanWave b r σ q (MaassDifferential.F (Nat.lcm N (q^2):ℝ) x y) := by
  obtain ⟨ε,hε,he⟩ := principal_original_coherent_twist_reflections hN r σ hb
  refine ⟨ε,hε,?_⟩
  intro q hq x y hy
  have hL : (0:ℝ)<(Nat.lcm N (q^2):ℝ) := by exact_mod_cast Nat.lcm_pos hN (pow_pos hq 2)
  have hh := he q hq x y hy
  rw [principalEulerWave_twisted hb.polynomialGrowth r σ q (x,y) hy,
    principalEulerWave_twisted hb.polynomialGrowth r σ q _ (MaassDifferential.F_height_pos hL hy)] at hh
  exact hh

#print axioms principalEulerWave_twisted
#print axioms principal_original_ramanujan_reflections

end QuantitativeMaass
