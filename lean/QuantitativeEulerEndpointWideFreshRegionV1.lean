module

public import QuantitativeEulerEndpointWideCertificateV1
public import QuantitativeEulerEndpointFreshRegionV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane AsymptoticCompactFamilyTranslation AsymptoticFreshCompactDefects
open scoped Classical

def wideFreshRegion (B R Y H : ℝ) : Set ℍ :=
  observationRectangle (B*(H+R+1)/min 1 Y+1) (Y/wideDistortion B R H)
    (B*(H+R+1)/min 1 Y)

theorem wideFreshRegion_compact (B R H : ℝ) {Y : ℝ} (hY : 0<Y) :
    IsCompact (wideFreshRegion B R Y H) :=
  observationRectangle_compact _ _ (div_pos hY (wideDistortion_pos B R H))

theorem wide_subset_fresh (B R Y H : ℝ) : wideImageRegion B R Y H⊆wideFreshRegion B R Y H := by
  intro z hz
  exact ⟨hz.1.trans (by linarith),hz.2⟩

theorem wide_subset_fresh_shifted (B R Y H : ℝ) (q : ℕ) [Fact q.Prime] (j : Fin (q-1)) :
    wideImageRegion B R Y H⊆shifted (parameter q j) (wideFreshRegion B R Y H) :=
  rectangle_subset_shifted _ (parameter_abs_le_one q j)

#print axioms wideFreshRegion_compact
#print axioms wide_subset_fresh_shifted
end QuantitativeEulerEndpointPrepared
