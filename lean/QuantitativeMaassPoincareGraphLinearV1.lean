module

public import QuantitativeMaassPoincareClosedGraphV1
public import QuantitativeMaassLaplacianLinearV1

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

def SmoothUpperSeed.zero : SmoothUpperSeed where
  toFun := 0
  smooth := contDiffOn_const
  compact := by
    change IsCompact (tsupport (0 : ℍ → ℂ))
    simp

def SmoothUpperSeed.add (u v : SmoothUpperSeed) : SmoothUpperSeed where
  toFun := u.toFun+v.toFun
  smooth := u.smooth.add v.smooth
  compact := u.compact.add v.compact

def SmoothUpperSeed.smul (u : SmoothUpperSeed) (c : ℂ) : SmoothUpperSeed where
  toFun := c•u.toFun
  smooth := contDiffOn_const.smul u.smooth
  compact := by
    apply u.compact.mono
    intro z hz he
    apply hz
    change c * u.toFun (z.re,z.im)=0
    change u.toFun (z.re,z.im)=0 at he
    rw [he,mul_zero]

theorem poincareSeedVector_congr (N : ℕ) {u v : SmoothUpperSeed}
    (he : upperFunction u.toFun=upperFunction v.toFun) :
    poincareSeedVector N u=poincareSeedVector N v := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [poincareSeedVector_coeFn N u,poincareSeedVector_coeFn N v] with z hu hv
  rw [hu,hv,he]

theorem poincareSeedVector_zero (N : ℕ) : poincareSeedVector N SmoothUpperSeed.zero=0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [poincareSeedVector_inner]
  simp [SmoothUpperSeed.zero,upperFunction,poincareSum]

theorem poincareSeedVector_add (N : ℕ) (u v : SmoothUpperSeed) :
    poincareSeedVector N (u.add v)=poincareSeedVector N u+poincareSeedVector N v := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [poincareSeedVector_coeFn N (u.add v),poincareSeedVector_coeFn N u,
    poincareSeedVector_coeFn N v,Lp.coeFn_add (poincareSeedVector N u).val
      (poincareSeedVector N v).val] with z huv hu hv ha
  simp only [Submodule.coe_add,ha,Pi.add_apply,huv,hu,hv]
  have hsu : Summable (fun g : gamma N => upperFunction u.toFun (g•z)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support (upperFunction u.toFun) u.compact z)
  have hsv : Summable (fun g : gamma N => upperFunction v.toFun (g•z)) :=
    summable_of_hasFiniteSupport (compact_seed_point_support (upperFunction v.toFun) v.compact z)
  exact hsu.tsum_add hsv

theorem poincareSeedVector_smul (N : ℕ) (c : ℂ) (u : SmoothUpperSeed) :
    poincareSeedVector N (u.smul c)=c•poincareSeedVector N u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [poincareSeedVector_coeFn N (u.smul c),poincareSeedVector_coeFn N u,
    Lp.coeFn_smul c (poincareSeedVector N u).val] with z hcu hu hs
  simp only [Submodule.coe_smul,hs,Pi.smul_apply,hcu,hu,smul_eq_mul]
  exact tsum_mul_left

theorem poincareSeedVector_laplacian_zero (N : ℕ) :
    poincareSeedVector N SmoothUpperSeed.zero.laplacian=0 := by
  rw [← poincareSeedVector_zero N]
  apply poincareSeedVector_congr
  funext z
  simp [upperFunction,SmoothUpperSeed.zero,SmoothUpperSeed.laplacian,hyperbolic,euclidean]

theorem poincareSeedVector_laplacian_add (N : ℕ) (u v : SmoothUpperSeed) :
    poincareSeedVector N (u.add v).laplacian=
      poincareSeedVector N u.laplacian+poincareSeedVector N v.laplacian := by
  rw [← poincareSeedVector_add]
  apply poincareSeedVector_congr
  funext z
  exact hyperbolic_add_smooth u.smooth v.smooth z.im_pos

theorem poincareSeedVector_laplacian_smul (N : ℕ) (c : ℂ) (u : SmoothUpperSeed) :
    poincareSeedVector N (u.smul c).laplacian=c•poincareSeedVector N u.laplacian := by
  rw [← poincareSeedVector_smul]
  apply poincareSeedVector_congr
  funext z
  exact hyperbolic_const_smul c u.toFun (z.re,z.im)

theorem poincareGraph_zero (N : ℕ) : PoincareGraph N 0 0 :=
  ⟨SmoothUpperSeed.zero,(poincareSeedVector_zero N).symm,
    (poincareSeedVector_laplacian_zero N).symm⟩

theorem poincareGraph_add (N : ℕ) {x y x' y' : AutomorphicSpace N}
    (h : PoincareGraph N x y) (h' : PoincareGraph N x' y') :
    PoincareGraph N (x+x') (y+y') := by
  obtain ⟨u,rfl,rfl⟩ := h
  obtain ⟨v,rfl,rfl⟩ := h'
  exact ⟨u.add v,(poincareSeedVector_add N u v).symm,
    (poincareSeedVector_laplacian_add N u v).symm⟩

theorem poincareGraph_smul (N : ℕ) (c : ℂ) {x y : AutomorphicSpace N}
    (h : PoincareGraph N x y) : PoincareGraph N (c•x) (c•y) := by
  obtain ⟨u,rfl,rfl⟩ := h
  exact ⟨u.smul c,(poincareSeedVector_smul N c u).symm,
    (poincareSeedVector_laplacian_smul N c u).symm⟩

/-- Every finite linear combination of seed graph pairs is again the
literal differential pair of a single smooth compact seed. -/
theorem poincareLinearGraph_mem_iff (N : ℕ) (p : AutomorphicSpace N × AutomorphicSpace N) :
    p∈poincareLinearGraph N ↔ PoincareGraph N p.1 p.2 := by
  constructor
  · intro hp
    induction hp using Submodule.span_induction with
    | mem p hp => exact hp
    | zero => exact poincareGraph_zero N
    | add p q _ _ hp hq => exact poincareGraph_add N hp hq
    | smul c p _ hp => exact poincareGraph_smul N c hp
  · intro hp
    exact Submodule.subset_span hp

#print axioms poincareLinearGraph_mem_iff

end QuantitativeMaass
