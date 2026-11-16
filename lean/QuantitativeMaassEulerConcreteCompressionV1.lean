module

public import QuantitativeMaassPhysicalEulerSpectralV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticSectorSigns
open scoped ContDiff BigOperators

namespace QuantitativeMaass

theorem cosinePacket_real (φ : ℝ → ℂ) (hr : ∀ t,star (φ t)=φ t) (r : ℝ) :
    ((cosinePacket φ r).re:ℂ)=cosinePacket φ r := by
  have he : star (cosinePacket φ r)=cosinePacket φ r := by
    unfold cosinePacket
    rw [Complex.star_def,←integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    rw [map_mul,Complex.conj_ofReal]
    exact congrArg (fun z : ℂ => z*(Real.cos (t*r):ℂ)) (hr t)
  apply Complex.ext
  · rfl
  · have hh := congrArg Complex.im he
    simp only [Complex.star_def,Complex.conj_im] at hh
    change 0=(cosinePacket φ r).im
    linarith

namespace EulerHilbert

/-- The exact original-window count for the constructed physical Abel
operator. Spectral action is discharged; the residual Hilbert--Schmidt
summability and the scalar window lower bound remain explicit inputs. -/
theorem originalWindow_count_concrete_abel {N Q : ℕ} {hQ : 0<Q}
    (A : FinitenessCertificate.Certificate N Q hQ) (hN : 0<N)
    (P : FinitenessGlobalHeight.Parameters A) {ι : Type*}
    (σ : ℕ) (t ε : ℝ)
    (basis : HilbertBasis ι ℂ
      (AsymptoticCylinderTerminal.Space (AsymptoticReconstructedCount.parameters A P).ε))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hsF : Function.support F⊆Iic (Real.cosh R))
    (s : Set UpperHalfPlane) (hs : IsCompact s) (qs : Finset ℕ+) (d : ℕ)
    (hlower : ∀ r∈Icc t (t+ε),1≤(cosinePacket (coshTimeTest F) r).re)
    (hB : ∀ e : Sector N,Summable (fun i =>
      ‖filteredCompression (physicalIsometry A hN P e)
        (physicalCappedAbelOperator F hF hc R hR hsF
          (AsymptoticReconstructedCount.parameters A P).ε
          (AsymptoticReconstructedCount.parameters A P).epsilon_pos
          ((AsymptoticReconstructedCount.parameters A P).s+3))
        (residualFilter A hN P e hs qs d) (basis i)‖^2)) :
    (QuantitativeConcreteGoals.maassWindow N σ t ε).Finite ∧
      ((QuantitativeConcreteGoals.maassWindow N σ t ε).ncard : ℝ)≤
        ∑ e : Sector N,hilbertSchmidtEnergy basis
          (filteredCompression (physicalIsometry A hN P e)
            (physicalCappedAbelOperator F hF hc R hR hsF
              (AsymptoticReconstructedCount.parameters A P).ε
              (AsymptoticReconstructedCount.parameters A P).epsilon_pos
              ((AsymptoticReconstructedCount.parameters A P).s+3))
            (residualFilter A hN P e hs qs d)) := by
  apply originalWindow_count_of_residual_compressions A hN P σ t ε basis _ s hs qs d
    (fun r => (cosinePacket (coshTimeTest F) r).re) _ hlower hB
  intro p
  rw [cosinePacket_real (coshTimeTest F) (fun t => hr (Real.cosh t)) p.val.1]
  exact physicalCappedAbelOperator_original hN A (AsymptoticReconstructedCount.parameters A P)
    p.val.1 σ p.property.2.2 F hF hc hr R hR hsF

#print axioms originalWindow_count_concrete_abel

end EulerHilbert
#print axioms cosinePacket_real
end QuantitativeMaass
