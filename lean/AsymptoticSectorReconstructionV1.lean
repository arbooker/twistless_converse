module

public import AsymptoticCylinderReconstructionV1
public import AsymptoticCylinderCountV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticSectorReconstruction

open MeasureTheory FinitenessCertificate FinitenessGlobalHeight
open FinitenessAnalyticReconstruction FinitenessFourierConstruction
open AsymptoticCylinder AsymptoticSectorSigns

/-- The coefficient-sector definition supplies the literal Fourier
functional equations; the canonical disk extension agrees at every
positive-height argument appearing in a twist law. -/
theorem coefficientSector_laws {N Q : ℕ} (hN : 0<N) (hQ : 0<Q)
    (χ : ℕ → ℂ) (m d : ℕ) (a : coefficientSpace d)
    (ha : a∈coefficientSector N Q χ m d) :
    FinitenessHolomorphicSpace.Laws N Q χ m (fourier a.val) := by
  have hL : FinitenessHolomorphicSpace.Laws N Q χ m
      (FinitenessHolomorphicSpace.lift (disk a.val)) := ha.2.2.2
  have ht (q : ℕ) (z : ℂ) (hz : 0<z.im) :
      twist (FinitenessHolomorphicSpace.lift (disk a.val)) q z=twist (fourier a.val) q z := by
    unfold twist
    apply Finset.sum_congr rfl
    intro u _
    apply disk_eq_fourier
    simpa using hz
  intro q hq z hz
  have hq0 := Nat.pos_of_dvd_of_pos hq hQ
  have hℓ : (0:ℝ)<Nat.lcm N (q^2) := by exact_mod_cast Nat.lcm_pos hN (pow_pos hq0 2)
  have hi : 0<(-1/((Nat.lcm N (q^2):ℕ)*z):ℂ).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos hℓ hz
  have he := hL q hq z hz
  rw [ht q z hz,ht q _ hi] at he
  exact he

theorem fourierMap_inclusion (h t d : ℕ) {ε : ℝ} (hε : 0<ε)
    (hd : 2*d+4≤2*h+2*t+1) (hd' : 2*d+4≤2*h+2*(t+1)+1) (a : coefficientSpace d) :
    inclusion hε ((fourierMap (2*h) t d (by positivity) hε hd a :
      holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) hε):Space)=
      ((fourierMap (2*h) (t+1) d (by positivity) hε hd' a :
        holomorphicSpace (2*h) (t+1) (by positivity : 0<4*Real.pi) hε):Space) := by
  apply Lp.ext
  filter_upwards [inclusion_coeFn hε ((fourierMap (2*h) t d (by positivity) hε hd a :
      holomorphicSpace (2*h) t (by positivity : 0<4*Real.pi) hε):Space),
    fourierMap_eq_disk_ae h t d hε hd a,fourierMap_eq_disk_ae h (t+1) d hε hd' a]
    with z hi ht ht'
  rw [hi,ht,ht']
  simp only [weight,pow_succ,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem sector_reconstructed (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (hK : ‖AsymptoticCertificateOperators.low A hN P (multiplier e) (P.s+3) (h+1)‖<1)
    (w : holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈eulerCylinderSector P h e) :
    ∃ g : AsymptoticCylinderTerminal.Space P.ε,
      (inclusion P.epsilon_pos).comp
        (AsymptoticCylinderReconstruction.extension A hN P (multiplier e) (h+1)) g=(w:Space) := by
  obtain ⟨a,rfl⟩ := hw
  let f : Space := (fourierMap (2*h) (P.s+3) (h+1+P.s) (by positivity) P.epsilon_pos
    (by omega) a.val : holomorphicSpace (2*h) (P.s+3) (by positivity : 0<4*Real.pi) P.epsilon_pos)
  let g := AsymptoticRegionL2.restrict measure (AsymptoticCylinderTerminal.region P.ε)
    (AsymptoticCylinderTerminal.region_measurable P.ε) f
  have hFE := coefficientSector_laws hN hQ (multiplier e) (h+1) (h+1+P.s) a.val (a.property.1 Q hQ)
  have he := AsymptoticCylinderReconstruction.extension_of_FE A hN P (multiplier e) (h+1)
    (fourier a.val.val) (periodic a.val.val) hFE f
    (AsymptoticCylinderLift.lift_fourierMap h (P.s+3) (h+1+P.s) P.epsilon_pos (by omega) a.val) hK
  refine ⟨g,?_⟩
  change inclusion P.epsilon_pos (AsymptoticCylinderReconstruction.extension A hN P (multiplier e) (h+1) g)=_
  rw [he]
  exact fourierMap_inclusion h (P.s+3) (h+1+P.s) P.epsilon_pos (by omega) (by omega) a.val

/-- One common auxiliary choice supplies bounded reconstruction and the
terminal lower bound for every weight and every actual sector. -/
theorem uniform_reconstruction (hN : 0<N) (P : Parameters A) :
    ∃ P' : Parameters A,P'.ε=P.ε ∧ P'.ρ=P.ρ ∧ P.s≤P'.s ∧
      ∀ h : ℕ,∀ e : Sector N,
        ‖AsymptoticCylinderReconstruction.extension A hN P' (multiplier e) (h+1)‖≤
          1+2*AsymptoticCertificateOperators.terminalConstant A P' ∧
        (∀ g,‖g‖≤‖(inclusion P'.epsilon_pos).comp
          (AsymptoticCylinderReconstruction.extension A hN P' (multiplier e) (h+1)) g‖) ∧
        (∀ w,w∈eulerCylinderSector P' h e → ∃ g,
          (inclusion P'.epsilon_pos).comp
            (AsymptoticCylinderReconstruction.extension A hN P' (multiplier e) (h+1)) g=(w:Space)) := by
  obtain ⟨P',hε,hρ,hs,hK⟩ := AsymptoticCertificateOperators.contraction_parameters A hN P
  refine ⟨P',hε,hρ,hs,?_⟩
  intro h e
  have hχ : ∀ q,q∣Q → ‖multiplier e q‖=1 := fun q _ => multiplier_norm e q
  have hk := hK (multiplier e) hχ (h+1)
  have hk1 : ‖AsymptoticCertificateOperators.low A hN P' (multiplier e) (P'.s+3) (h+1)‖<1 :=
    lt_trans hk (by norm_num)
  exact ⟨AsymptoticCylinderReconstruction.extension_norm_le A hN P' (multiplier e) hχ (h+1) hk,
    AsymptoticCylinderReconstruction.extension_inclusion_norm_ge A hN P' (multiplier e) (h+1) hk1,
    sector_reconstructed A hN P' h e hk1⟩

#print axioms coefficientSector_laws
#print axioms fourierMap_inclusion
#print axioms sector_reconstructed
#print axioms uniform_reconstruction

end AsymptoticSectorReconstruction
