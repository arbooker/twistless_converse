module

public import AsymptoticObservationTraceV1
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

@[expose] public section

namespace AsymptoticReconstruction

open ContinuousLinearMap

variable {G E : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The low-height reconstruction, defined by the actual operator Neumann
series. The contraction hypothesis is used in the following theorems. -/
noncomputable def low (K : E →L[ℂ] E) (B : G →L[ℂ] E) : G →L[ℂ] E :=
  (∑' n : ℕ,K^n).comp B

/-- The Neumann series solves the low-height equation. -/
theorem low_equation [CompleteSpace E] (K : E →L[ℂ] E) (B : G →L[ℂ] E) (hK : ‖K‖<1) (g : G) :
    low K B g=K (low K B g)+B g := by
  have hh := congrArg (fun T : E →L[ℂ] E => T (B g)) (mul_neg_geom_series K hK)
  change low K B g-K (low K B g)=B g at hh
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hh

/-- The reconstructed solution is the unique Hilbert-space solution of the
same equation, so the Neumann construction adds no new boundary condition. -/
theorem low_unique [CompleteSpace E] (K : E →L[ℂ] E) (B : G →L[ℂ] E) (hK : ‖K‖<1)
    {u : E} {g : G} (hu : u=K u+B g) : u=low K B g := by
  have he : (1-K) u=B g := by
    change u-K u=B g
    exact sub_eq_iff_eq_add.mpr (hu.trans (add_comm _ _))
  have hh := congrArg (fun T : E →L[ℂ] E => T u) (geom_series_mul_neg K hK)
  change (∑' n : ℕ,K^n) ((1-K) u)=u at hh
  rw [he] at hh
  exact hh.symm

theorem low_norm_le (K : E →L[ℂ] E) (B : G →L[ℂ] E) (hK : ‖K‖<1) :
    ‖low K B‖≤‖B‖/(1-‖K‖) := by
  have hgeom := tsum_geometric_le_of_norm_lt_one K hK
  have hone : ‖(1:E →L[ℂ] E)‖≤1 := ContinuousLinearMap.norm_id_le
  have hgeom' : ‖∑' n : ℕ,K^n‖≤(1-‖K‖)⁻¹ := by linarith
  calc
    ‖low K B‖ ≤ ‖∑' n : ℕ,K^n‖*‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1-‖K‖)⁻¹*‖B‖ := mul_le_mul_of_nonneg_right hgeom' (norm_nonneg B)
    _ = _ := by rw [div_eq_mul_inv,mul_comm]

/-- Join the reconstructed low part and the unchanged terminal data in
the orthogonal Hilbert sum. -/
noncomputable def extension (K : E →L[ℂ] E) (B : G →L[ℂ] E) :
    G →L[ℂ] WithLp 2 (E × G) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E G).symm.toContinuousLinearMap.comp
    ((low K B).prod (ContinuousLinearMap.id ℂ G))

@[simp] theorem extension_apply (K : E →L[ℂ] E) (B : G →L[ℂ] E) (g : G) :
    extension K B g=WithLp.toLp 2 (low K B g,g) := rfl

@[simp] theorem extension_terminal (K : E →L[ℂ] E) (B : G →L[ℂ] E) (g : G) :
    (extension K B g).snd=g := rfl

/-- The terminal identity supplies exactly the lower bound used in the
positive observation operator construction. -/
theorem extension_norm_ge (K : E →L[ℂ] E) (B : G →L[ℂ] E) (g : G) :
    ‖g‖≤‖extension K B g‖ := WithLp.norm_snd_le E (extension K B g)

theorem extension_norm_apply_le (K : E →L[ℂ] E) (B : G →L[ℂ] E) (hK : ‖K‖<1) (g : G) :
    ‖extension K B g‖≤(1+‖B‖/(1-‖K‖))*‖g‖ := by
  have he : extension K B g=WithLp.toLp 2 (low K B g,(0:G))+WithLp.toLp 2 ((0:E),g) := by
    apply (WithLp.equiv 2 (E×G)).injective
    simp [extension_apply]
  rw [he]
  calc
    ‖WithLp.toLp 2 (low K B g,(0:G))+WithLp.toLp 2 ((0:E),g)‖ ≤
        ‖WithLp.toLp 2 (low K B g,(0:G))‖+‖WithLp.toLp 2 ((0:E),g)‖ := norm_add_le _ _
    _ = ‖low K B g‖+‖g‖ := by rw [WithLp.norm_toLp_fst,WithLp.norm_toLp_snd]
    _ ≤ ‖low K B‖*‖g‖+‖g‖ := add_le_add ((low K B).le_opNorm g) le_rfl
    _ ≤ (‖B‖/(1-‖K‖))*‖g‖+‖g‖ := by gcongr; exact low_norm_le K B hK
    _ = _ := by ring

theorem extension_norm_le (K : E →L[ℂ] E) (B : G →L[ℂ] E) (hK : ‖K‖<1) :
    ‖extension K B‖≤1+‖B‖/(1-‖K‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact extension_norm_apply_le K B hK

/-- Once the weighted low-height equation is established, its Hilbert-space
solution is precisely the bounded extension of its terminal data. -/
theorem extension_unique [CompleteSpace E] (K : E →L[ℂ] E) (B : G →L[ℂ] E) (hK : ‖K‖<1)
    (u : WithLp 2 (E×G)) (hu : u.fst=K u.fst+B u.snd) : extension K B u.snd=u := by
  have he := low_unique K B hK hu
  apply (WithLp.equiv 2 (E×G)).injective
  apply Prod.ext
  · exact he.symm
  · rfl

#print axioms low_unique
#print axioms low_norm_le
#print axioms extension_norm_le
#print axioms extension_unique

end AsymptoticReconstruction
