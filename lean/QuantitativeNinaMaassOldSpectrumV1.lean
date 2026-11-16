module

public import QuantitativeNinaMaassOldTraceV1
public import QuantitativeMaassClassicalGraphV1
public import QuantitativeMaassCuspContinuousConstantV1
public import MaassFrickeSmoothV1
public import AsymptoticClassicalIntegralTriangularV1
public import AsymptoticClassicalTriangularSlashV1
public import AsymptoticClassicalFrickeGroupV1
public import QuantitativeNinaMaassSmallPeriodsV1
public import QuantitativeNinaMaassEigenRepresentativesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeMaass
open AsymptoticFreshMatrices AsymptoticCongruenceLabels
open AsymptoticClassicalCusp AsymptoticClassicalDiscriminant
open scoped Topology InnerProductSpace MatrixGroups ENNReal

/-!
Level change for the actual Friedrichs Laplacian. Unfolding a compact
Poincare test against a pulled-back representative gives the same integral
at both levels. Density extends this identity to every completed vector;
the proved weak-test characterization then transfers the full operator
graph. The finite trace transfers the graph by adjointness.

These statements contain no assumed oldform decomposition or counting law.
The common-period cusp averages are also preserved at every integral cusp.
Fricke covariance follows from the exact Cartesian differential calculation
and hyperbolic change of variables. Cuspidal multiplicities still require
the old-image overlap arguments. Fricke cusp preservation below is first
proved on continuous representatives, with the actual rational cusp change
and both periodicity assertions verified from automorphy.
-/

namespace QuantitativeNinaMaass

/-- Compact test pairings are unchanged by literal level pullback. -/
theorem poincareSeed_pairing_levelCover {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (u : SmoothUpperSeed) (v : AutomorphicSpace M) :
    inner ℂ (poincareSeedVector N u) (levelCover hMN v) =
      inner ℂ (poincareSeedVector M u) v := by
  have he : (fun x : AutomorphicSpace M =>
      inner ℂ (poincareSeedVector N u) (levelCover hMN x)) =
      fun x => inner ℂ (poincareSeedVector M u) x := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma M) (quotientMeasure M)).equalizer
      (continuous_const.inner (levelCover hMN).continuous)
      (continuous_const.inner continuous_id)
    funext f
    simp only [Function.comp_apply, id_eq, levelCover_apply, poincareSeed_pairing_representative]
    rfl
  exact congrFun he v

/-- Pullback transfers the full graph, not just formal differential tests. -/
theorem levelCover_friedrichsGraph {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) {v w : AutomorphicSpace M} (h : FriedrichsGraph M v w) :
    FriedrichsGraph N (levelCover hMN v) (levelCover hMN w) := by
  apply friedrichsGraph_of_seed_pairings
  intro u
  rw [poincareSeed_pairing_levelCover, poincareSeed_pairing_levelCover]
  exact friedrichsGraph_symmetric M (friedrichsGraph_poincareSeed M u) h

/-- The actual lower-level graph can also be recovered from the pullback. -/
theorem levelCover_friedrichsGraph_iff {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (v w : AutomorphicSpace M) :
    FriedrichsGraph N (levelCover hMN v) (levelCover hMN w) ↔
      FriedrichsGraph M v w := by
  constructor
  · intro h
    apply friedrichsGraph_of_seed_pairings
    intro u
    rw [← poincareSeed_pairing_levelCover hMN, ← poincareSeed_pairing_levelCover hMN]
    exact friedrichsGraph_symmetric N (friedrichsGraph_poincareSeed N u) h
  · exact levelCover_friedrichsGraph hMN

/-- The genuine finite-coset trace also preserves the operator graph. -/
theorem levelTrace_friedrichsGraph {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) {v w : AutomorphicSpace N} (h : FriedrichsGraph N v w) :
    FriedrichsGraph M (levelTrace hMN v) (levelTrace hMN w) := by
  apply friedrichsGraph_of_seed_pairings
  intro u
  simp only [levelTrace, ContinuousLinearMap.adjoint_inner_right]
  exact friedrichsGraph_symmetric N
    (levelCover_friedrichsGraph hMN (friedrichsGraph_poincareSeed M u)) h

/-- Level pullback intertwines the actual bounded Friedrichs resolvents. -/
theorem levelCover_resolvent {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (v : AutomorphicSpace M) :
    friedrichsResolvent N (levelCover hMN v) =
      levelCover hMN (friedrichsResolvent M v) := by
  have h := levelCover_friedrichsGraph hMN (friedrichsGraph_resolvent M v)
  simpa [FriedrichsGraph] using h

/-- The trace intertwines the same resolvents in the reverse direction. -/
theorem levelTrace_resolvent {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (v : AutomorphicSpace N) :
    friedrichsResolvent M (levelTrace hMN v) =
      levelTrace hMN (friedrichsResolvent N v) := by
  have h := levelTrace_friedrichsGraph hMN (friedrichsGraph_resolvent N v)
  simpa [FriedrichsGraph] using h

/-- In particular, pullback preserves the exact eigenvalue. -/
theorem levelCover_eigen {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (v : AutomorphicSpace M) (e : ℂ)
    (h : FriedrichsGraph M v (e • v)) :
    FriedrichsGraph N (levelCover hMN v) (e • levelCover hMN v) := by
  simpa only [map_smul] using levelCover_friedrichsGraph hMN h

/-- Finite trace preserves the exact eigenvalue, including its zero image. -/
theorem levelTrace_eigen {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (v : AutomorphicSpace N) (e : ℂ)
    (h : FriedrichsGraph N v (e • v)) :
    FriedrichsGraph M (levelTrace hMN v) (e • levelTrace hMN v) := by
  simpa only [map_smul] using levelTrace_friedrichsGraph hMN h

/-- Enlarging the common horocycle period by a positive integer leaves its
average unchanged, at every cusp and every height. -/
theorem cuspConstant_level {M N : ℕ} (hN : 0 < N) (hMN : M ∣ N)
    (s : SL(2,ℤ)) (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ g : gamma M, ∀ z : ℍ, f (g.val • z) = f z) (y : ℝ) :
    cuspConstant N s f y = cuspConstant M s f y := by
  obtain ⟨d, hNd⟩ := hMN
  have hd : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    simp only [hz, mul_zero] at hNd
    omega
  have he : cuspProfile N s f = fun x y => cuspProfile M s f ((d : ℝ) * x) y := by
    funext x y
    by_cases hy : 0 < y
    · simp only [cuspProfile, dite_eq_left hy]
      have hx : (N : ℝ) * x = (M : ℝ) * ((d : ℝ) * x) := by
        rw [hNd, Nat.cast_mul]
        ring
      rw [hx]
    · simp only [cuspProfile, dite_eq_right hy]
  unfold cuspConstant zeroFourier
  rw [he]
  exact periodic_dilate_average _ (cuspProfile_continuous M s f hf y)
    (cuspProfile_periodic M s f hinv y) d hd

/-- Literal vanishing constants suffice for membership in the actual
closed cusp space. This is the reverse of the continuous-representative
constant-term theorem. -/
theorem continuous_representative_mem_cuspidal (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hzero : ∀ s : SL(2,ℤ), ∀ y : ℝ, 0 < y → cuspConstant N s f.val y = 0) :
    AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN := by
  apply (mem_localCuspidalSpace N hN _).mpr
  intro s A B
  apply Lp.ext
  have he := cuspLogConstant_representative_ae N hN s A B f hf
  filter_upwards [he, Lp.coeFn_zero ℂ 2 (volume.restrict (Icc A B))] with x hx hz
  rw [hx, hz]
  simp only [logHalfDensity, hzero s (Real.exp x) (Real.exp_pos x), mul_zero, Pi.zero_apply]

/-- Extracting the underlying function before specializing the finite-cover
construction keeps the kernel from unfolding arithmetic instance proofs. -/
theorem coverRepresentative_coe_general {G X : Type*}
    [Group G] [Countable G] [MulAction G X] [MeasurableSpace X]
    (μ : Measure X) (hmp : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (H J : Subgroup G) (hHJ : H ≤ J) [Finite (J ⧸ H.subgroupOf J)]
    (ρ τ : X → ℝ≥0∞) (hρ : Measurable ρ) (hτ : Measurable τ)
    (hnρ : ∀ x, ∑' g : J, ρ (g.val • x) = 1)
    (hnτ : ∀ x, ∑' g : H, τ (g.val • x) = 1)
    (f : AutomorphicL2.representatives J (μ.withDensity ρ)) :
    (AutomorphicL2.coverRepresentative μ hmp H J hHJ ρ τ hρ hτ hnρ hnτ f).val = f.val := by
  funext x
  rfl

/-- Level pullback is literally the same function on the upper half-plane. -/
theorem levelCoverRepresentative_coe {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M)) :
    (levelCoverRepresentative hMN f).val = f.val :=
  coverRepresentative_coe_general volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N) f

theorem levelCoverRepresentative_continuous {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M))
    (hf : Continuous f.val) : Continuous (levelCoverRepresentative hMN f).val := by
  rw [levelCoverRepresentative_coe]
  exact hf

/-- The common-period average proves literal zero constants after pullback. -/
theorem levelCoverRepresentative_constant_zero {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M))
    (hf : Continuous f.val)
    (hz : ∀ s : SL(2,ℤ), ∀ y : ℝ, 0 < y → cuspConstant M s f.val y = 0)
    (s : SL(2,ℤ)) (y : ℝ) (hy : 0 < y) :
    cuspConstant N s (levelCoverRepresentative hMN f).val y = 0 := by
  rw [levelCoverRepresentative_coe, cuspConstant_level hN hMN s f.val hf f.property.2.1]
  exact hz s y hy

theorem levelCover_cuspidal_continuous {M N : ℕ} [NeZero N]
    (hM : 0 < M) (hN : 0 < N) (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M))
    (hf : Continuous f.val)
    (hcusp : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace M hM) :
    levelCover hMN (AutomorphicL2.denseEmbedding _ _ f) ∈ localCuspidalSpace N hN := by
  rw [levelCover_apply]
  apply continuous_representative_mem_cuspidal N hN _
    (levelCoverRepresentative_continuous hMN f hf)
  apply levelCoverRepresentative_constant_zero hN hMN f hf
  intro s y hy
  exact localCuspidalSpace_continuous_constant_zero M hM _ hcusp f.val hf
    f.property.2.1 f.property.2.2.coeFn_toLp s y hy

/-- Actual level pullback preserves the entire closed cusp space by the
checked density of continuous geometric eigenvectors. -/
theorem levelCover_mem_cuspidal {M N : ℕ} [NeZero N]
    (hM : 0 < M) (hN : 0 < N) (hMN : M ∣ N)
    (v : AutomorphicSpace M) (hv : v ∈ localCuspidalSpace M hM) :
    levelCover hMN v ∈ localCuspidalSpace N hN :=
  cuspidal_operator_mem_of_continuous M N hM hN (levelCover hMN)
    (levelCover_cuspidal_continuous hM hN hMN) v hv

/-- The Cartesian differential Fricke map is the actual rational action. -/
theorem frickeLabel_cartesian (N : ℕ) (hN : 0 < N) (z : ℍ) :
    MaassDifferential.F (N : ℝ) z.re z.im =
      ((frickeLabel N hN • z).re, (frickeLabel N hN • z).im) := by
  have hc : ((frickeLabel N hN • z : ℍ) : ℂ) = -1 / ((N : ℂ) * z) := by
    rw [frickeLabel, AsymptoticRationalBranches.ofMatrix_action,
      AsymptoticRationalBranches.realMatrix_branch]
    simpa using AsymptoticReconstructionBranch.branch_action
      (show (0 : ℝ) < N by exact_mod_cast hN) 0 0 z
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  change (frickeLabel N hN • z).re = _ at hre
  change (frickeLabel N hN • z).im = _ at him
  rw [hre, him]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hr : z.re ^ 2 + z.im ^ 2 ≠ 0 := (MaassDifferential.radius_pos z.im_pos).ne'
  have hd : ((N : ℝ) * z.re) ^ 2 + ((N : ℝ) * z.im) ^ 2 ≠ 0 := by
    rw [mul_pow, mul_pow, ← mul_add]
    exact mul_ne_zero (pow_ne_zero 2 hNR) hr
  apply Prod.ext <;>
    simp only [MaassDifferential.F, Complex.div_re, Complex.div_im, Complex.neg_re,
      Complex.neg_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.natCast_re, Complex.natCast_im, Complex.normSq_apply, zero_mul,
      add_zero, sub_zero, neg_zero, neg_mul, one_mul, coe_re, coe_im]
  all_goals field_simp [hNR, hr, hd]
  all_goals ring

theorem upperFunction_fricke_pullback (N : ℕ) (hN : 0 < N)
    (u : MaassDifferential.Point → ℂ) :
    upperFunction (MaassDifferential.pullback N u) =
      upperFunction u ∘ (fun z : ℍ => frickeLabel N hN • z) := by
  funext z
  change u (MaassDifferential.F N z.re z.im) = u _
  rw [frickeLabel_cartesian]

/-- Pulling a compact smooth test through the actual Fricke involution. -/
def frickeSeed (N : ℕ) (hN : 0 < N) (u : SmoothUpperSeed) : SmoothUpperSeed where
  toFun := MaassDifferential.pullback N u.toFun
  smooth := MaassDifferential.pullback_contDiffOn u.smooth (Nat.cast_pos.mpr hN)
  compact := by
    rw [upperFunction_fricke_pullback N hN]
    let : ContinuousConstSMul AsymptoticRationalGroup.Group ℍ :=
      ⟨AsymptoticRationalBranches.action_continuous⟩
    exact u.compact.comp_homeomorph (Homeomorph.smul (frickeLabel N hN))

theorem frickeSeed_upper (N : ℕ) (hN : 0 < N) (u : SmoothUpperSeed) (z : ℍ) :
    upperFunction (frickeSeed N hN u).toFun z = upperFunction u.toFun (frickeLabel N hN • z) :=
  congrFun (upperFunction_fricke_pullback N hN u.toFun) z

/-- Exact differential covariance on the transformed compact test. -/
theorem poincare_frickeSeed_laplacian (N : ℕ) (hN : 0 < N) (u : SmoothUpperSeed) :
    poincareSeedVector N (frickeSeed N hN u).laplacian =
      poincareSeedVector N (frickeSeed N hN u.laplacian) := by
  apply poincareSeedVector_congr
  funext z
  exact MaassDifferential.hyperbolic_pullback u.smooth (Nat.cast_pos.mpr hN) z.im_pos

theorem fricke_seed_pairing (N : ℕ) (hN : 0 < N) (u : SmoothUpperSeed) (f : ℍ → ℂ) :
    (∫ z : ℍ, star (upperFunction u.toFun z) * f (frickeLabel N hN • z)) =
      ∫ z : ℍ, star (upperFunction (frickeSeed N hN u).toFun z) * f z := by
  let : ContinuousConstSMul AsymptoticRationalGroup.Group ℍ :=
    ⟨AsymptoticRationalBranches.action_continuous⟩
  have he := (AsymptoticRationalGroup.measurePreserving (frickeLabel N hN)).integral_comp
    (Homeomorph.smul (frickeLabel N hN)).measurableEmbedding
    (fun z => star (upperFunction (frickeSeed N hN u).toFun z) * f z)
  simpa only [frickeSeed_upper, ← mul_smul, frickeLabel_mul_self, one_smul] using he

/-- The test transformation agrees with the actual completed Fricke action. -/
theorem poincareSeed_pairing_fricke (N : ℕ) (hN : 0 < N)
    (u : SmoothUpperSeed) (v : AutomorphicSpace N) :
    inner ℂ (poincareSeedVector N u) (frickeIsometry N hN v) =
      inner ℂ (poincareSeedVector N (frickeSeed N hN u)) v := by
  have he : (fun v : AutomorphicSpace N =>
      inner ℂ (poincareSeedVector N u) (frickeIsometry N hN v)) =
      fun v => inner ℂ (poincareSeedVector N (frickeSeed N hN u)) v := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (continuous_const.inner (frickeIsometry N hN).continuous)
      (continuous_const.inner continuous_id)
    funext f
    simp only [Function.comp_apply, id_eq, frickeIsometry_apply, poincareSeed_pairing_representative]
    exact fricke_seed_pairing N hN u f.val
  exact congrFun he v

/-- Fricke preserves the full actual self-adjoint Laplace graph. -/
theorem fricke_friedrichsGraph (N : ℕ) (hN : 0 < N)
    {v w : AutomorphicSpace N} (h : FriedrichsGraph N v w) :
    FriedrichsGraph N (frickeIsometry N hN v) (frickeIsometry N hN w) := by
  let : NeZero N := ⟨hN.ne'⟩
  apply friedrichsGraph_of_seed_pairings
  intro u
  rw [poincareSeed_pairing_fricke, poincareSeed_pairing_fricke]
  have hs := friedrichsGraph_poincareSeed N (frickeSeed N hN u)
  rw [poincare_frickeSeed_laplacian] at hs
  exact friedrichsGraph_symmetric N hs h

theorem fricke_resolvent (N : ℕ) (hN : 0 < N) (v : AutomorphicSpace N) :
    friedrichsResolvent N (frickeIsometry N hN v) =
      frickeIsometry N hN (friedrichsResolvent N v) := by
  have h := fricke_friedrichsGraph N hN (friedrichsGraph_resolvent N v)
  simpa [FriedrichsGraph] using h

theorem fricke_eigen (N : ℕ) (hN : 0 < N) (v : AutomorphicSpace N) (e : ℂ)
    (h : FriedrichsGraph N v (e • v)) :
    FriedrichsGraph N (frickeIsometry N hN v) (e • frickeIsometry N hN v) := by
  simpa only [map_smul] using fricke_friedrichsGraph N hN h

theorem frickeLabel_action_real (N : ℕ) (hN : 0 < N) (z : ℍ) :
    frickeLabel N hN • z = frickeReal N hN • z := by
  rw [frickeLabel, AsymptoticRationalBranches.ofMatrix_action]
  rfl

/-- Triangular reduction of the actual Fricke matrix in any integral cusp
chart. Both diagonal entries are positive integers. -/
theorem fricke_cusp_triangular (N : ℕ) (hN : 0 < N) (s : SL(2,ℤ)) :
    ∃ (U : SL(2,ℤ)) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d),
      frickeReal N hN * SpecialLinearGroup.mapGL ℝ s =
        SpecialLinearGroup.mapGL ℝ U *
          triangularGL (a : ℝ) (b : ℝ) (d : ℝ)
            (by exact_mod_cast ha) (by exact_mod_cast hd) := by
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; (N : ℤ), 0] * s.val
  have hdet : B.det = (N : ℤ) := by
    change (!![0, -1; (N : ℤ), 0] * s.val).det = _
    rw [Matrix.det_mul, s.property, mul_one]
    simp [Matrix.det_fin_two]
  obtain ⟨U, a, b, d, ha, hd, he⟩ :=
    integral_triangular B (by rw [hdet]; exact_mod_cast hN)
  refine ⟨U, a, b, d, ha, hd, ?_⟩
  apply Units.ext
  change (frickeReal N hN).val * s.val.map (Int.castRingHom ℝ) =
    U.val.map (Int.castRingHom ℝ) * !![(a : ℝ), (b : ℝ); 0, (d : ℝ)]
  ext i j
  have hh := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ => (X i j : ℝ)) he
  change (((!![0, -1; (N : ℤ), 0] * s.val) i j : ℤ) : ℝ) =
    (((U.val * !![a, b; 0, d]) i j : ℤ) : ℝ) at hh
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul] at hh
  fin_cases i <;> fin_cases j <;>
    simpa [frickeReal, fricke, AsymptoticReconstructionBranch.branch,
      GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero, triangularGL,
      Matrix.mul_apply, Fin.sum_univ_two] using hh

/-- Exact Fricke cusp-coordinate formula, retaining the rational slope
and shift. The common period remains the actual level N. -/
theorem cuspProfile_fricke_coordinates (N : ℕ) (hN : 0 < N)
    (s U : SL(2,ℤ)) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d)
    (he : frickeReal N hN * SpecialLinearGroup.mapGL ℝ s =
      SpecialLinearGroup.mapGL ℝ U *
        triangularGL (a : ℝ) (b : ℝ) (d : ℝ)
          (by exact_mod_cast ha) (by exact_mod_cast hd))
    (f : ℍ → ℂ) (x y : ℝ) (hy : 0 < y) :
    cuspProfile N s (fun z => f (frickeLabel N hN • z)) x y =
      cuspProfile N U f ((a : ℝ) / d * x + (b : ℝ) / d / N) ((a : ℝ) / d * y) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNy : (0 : ℝ) < (a : ℝ) / d * y := mul_pos (div_pos haR hdR) hy
  simp only [cuspProfile, dite_eq_left hy, dite_eq_left hNy]
  rw [frickeLabel_action_real, ← mul_smul, he, mul_smul, triangularGL_action]
  congr 1
  congr 1
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change ((affine ((a : ℝ) / d) (div_pos haR hdR) ((b : ℝ) / d)
        (horocyclePoint ((N : ℝ) * x) y hy)).re) = _
    simp only [affine, horocyclePoint, mk_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  · simp only [affine, horocyclePoint, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- Fricke transports vanishing literal constants to every integral cusp.
The rational-coordinate averaging lemma is applied only after proving the
transported profile's period from its actual normalizer representative. -/
theorem frickeRepresentative_constant_zero (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hzero : ∀ s : SL(2,ℤ), ∀ y : ℝ, 0 < y → cuspConstant N s f.val y = 0)
    (s : SL(2,ℤ)) (y : ℝ) (hy : 0 < y) :
    cuspConstant N s (frickeRepresentative N hN f).val y = 0 := by
  obtain ⟨U, a, b, d, ha, hd, he⟩ := fricke_cusp_triangular N hN s
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcoord : (fun x => cuspProfile N s (frickeRepresentative N hN f).val x y) =
      fun x => cuspProfile N U f.val
        ((a : ℝ) / d * x + (b : ℝ) / d / N) ((a : ℝ) / d * y) := by
    funext x
    exact cuspProfile_fricke_coordinates N hN s U a b d ha hd he f.val x y hy
  have hperiod := cuspProfile_periodic N s (frickeRepresentative N hN f).val
    (frickeRepresentative N hN f).property.2.1 y
  rw [hcoord] at hperiod
  unfold cuspConstant zeroFourier
  rw [hcoord]
  rw [periodic_mean_rational_affine _
    (cuspProfile_continuous N U f.val hf ((a : ℝ) / d * y))
    (cuspProfile_periodic N U f.val f.property.2.1 ((a : ℝ) / d * y))
    a d ha.ne' hd.ne' ((b : ℝ) / d / N) hperiod]
  exact hzero U ((a : ℝ) / d * y) (mul_pos (div_pos haR hdR) hy)

theorem frickeRepresentative_continuous (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) : Continuous (frickeRepresentative N hN f).val :=
  hf.comp (AsymptoticRationalBranches.action_continuous (frickeLabel N hN))

/-- Cuspidality is preserved by the actual Fricke action on any continuous
automorphic representative. No decay or automorphic expansion is assumed. -/
theorem fricke_cuspidal_continuous (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val)
    (hcusp : AutomorphicL2.denseEmbedding _ _ f ∈ localCuspidalSpace N hN) :
    frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ f) ∈ localCuspidalSpace N hN := by
  rw [frickeIsometry_apply]
  apply continuous_representative_mem_cuspidal N hN _ (frickeRepresentative_continuous N hN f hf)
  apply frickeRepresentative_constant_zero N hN f hf
  intro s y hy
  exact localCuspidalSpace_continuous_constant_zero N hN _ hcusp f.val hf
    f.property.2.1 f.property.2.2.coeFn_toLp s y hy

/-- Actual Fricke cusp preservation for every completed quotient vector. -/
theorem fricke_mem_cuspidal (N : ℕ) (hN : 0 < N)
    (v : AutomorphicSpace N) (hv : v ∈ localCuspidalSpace N hN) :
    frickeIsometry N hN v ∈ localCuspidalSpace N hN :=
  cuspidal_operator_mem_of_continuous N N hN hN (frickeIsometry N hN).toContinuousLinearMap
    (fricke_cuspidal_continuous N hN) v hv

theorem fricke_mem_cuspidal_iff (N : ℕ) (hN : 0 < N) (v : AutomorphicSpace N) :
    frickeIsometry N hN v ∈ localCuspidalSpace N hN ↔ v ∈ localCuspidalSpace N hN := by
  constructor
  · intro h
    have hh := fricke_mem_cuspidal N hN (frickeIsometry N hN v) h
    rwa [frickeIsometry_involutive N hN v] at hh
  · exact fricke_mem_cuspidal N hN v

#print axioms poincareSeed_pairing_levelCover
#print axioms levelCover_friedrichsGraph
#print axioms levelCover_friedrichsGraph_iff
#print axioms levelTrace_friedrichsGraph
#print axioms levelCover_resolvent
#print axioms levelTrace_resolvent
#print axioms levelCover_eigen
#print axioms levelTrace_eigen
#print axioms cuspConstant_level
#print axioms continuous_representative_mem_cuspidal
#print axioms coverRepresentative_coe_general
#print axioms levelCoverRepresentative_coe
#print axioms levelCoverRepresentative_continuous
#print axioms levelCoverRepresentative_constant_zero
#print axioms levelCover_cuspidal_continuous
#print axioms levelCover_mem_cuspidal
#print axioms frickeLabel_cartesian
#print axioms upperFunction_fricke_pullback
#print axioms frickeSeed_upper
#print axioms poincare_frickeSeed_laplacian
#print axioms fricke_seed_pairing
#print axioms poincareSeed_pairing_fricke
#print axioms fricke_friedrichsGraph
#print axioms fricke_resolvent
#print axioms fricke_eigen
#print axioms frickeLabel_action_real
#print axioms fricke_cusp_triangular
#print axioms cuspProfile_fricke_coordinates
#print axioms frickeRepresentative_constant_zero
#print axioms frickeRepresentative_continuous
#print axioms fricke_cuspidal_continuous
#print axioms fricke_mem_cuspidal
#print axioms fricke_mem_cuspidal_iff

end QuantitativeNinaMaass
