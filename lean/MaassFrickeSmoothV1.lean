module

public import MaassFrickeCovarianceV1

set_option autoImplicit false
set_option maxHeartbeats 20000

@[expose] public section

open Set
open scoped ContDiff

namespace MaassDifferential

theorem F_contDiffOn {L : ℝ} (hL : 0<L) :
    ContDiffOn ℝ ∞ (fun Z : Point => F L Z.1 Z.2) {Z | 0<Z.2} := by
  have hd : ContDiffOn ℝ ∞ (fun Z : Point => L*(Z.1^2+Z.2^2)) {Z | 0<Z.2} :=
    contDiffOn_const.mul ((contDiff_fst.contDiffOn.pow 2).add (contDiff_snd.contDiffOn.pow 2))
  have hn : ∀ Z : Point, Z∈{Z | 0<Z.2} → L*(Z.1^2+Z.2^2)≠0 :=
    fun Z hZ => mul_ne_zero hL.ne' (radius_pos hZ).ne'
  exact (contDiff_fst.contDiffOn.neg.div hd hn).prodMk (contDiff_snd.contDiffOn.div hd hn)

theorem pullback_contDiffOn {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) {L : ℝ} (hL : 0<L) :
    ContDiffOn ℝ ∞ (pullback L u) {Z | 0<Z.2} := by
  exact ContDiffOn.comp (f := fun Z : Point => F L Z.1 Z.2) (g := u)
    hu (F_contDiffOn hL) (fun Z hZ => F_height_pos hL hZ)

#print axioms F_contDiffOn
#print axioms pullback_contDiffOn

end MaassDifferential
