module

public import AsymptoticReconstructionBranchV1
public import AsymptoticMassTransportV1
public import FinitenessGlobalHeightV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticReconstructionBranch

open UpperHalfPlane

/-- The exact normalized branch identity. The rational reconstruction
coefficient is independent of weight; all weight dependence left in the
branch is the genuine unit-modulus slash phase. -/
theorem normalized_branch {L : ℝ} (hL : 0<L) (b d : ℝ) (m : ℕ) (F : ℍ → ℂ) (z : ℍ) :
    AsymptoticHyperbolicSlash.phase (branch L b d hL.ne') (2*m) z*
      ((branch L b d hL.ne' • z).im:ℂ)^m*F (branch L b d hL.ne' • z)=
    (z.im:ℂ)^m/((Real.sqrt L:ℂ)*((z:ℂ)+(b:ℂ)))^(2*m)*F (branch L b d hL.ne' • z) := by
  rw [AsymptoticHyperbolicSlash.normalized_slash _ (by rw [branch_det]; exact hL)]
  have hd : denom (branch L b d hL.ne') z=(L:ℂ)*((z:ℂ)+(b:ℂ)) := by
    change (L:ℂ)*(z:ℂ)+((L*b:ℝ):ℂ)=_
    push_cast
    ring
  have hs : (Real.sqrt L:ℂ)^2=(L:ℂ) := by exact_mod_cast Real.sq_sqrt hL.le
  have hp : ((Real.sqrt L:ℂ)*((z:ℂ)+(b:ℂ)))^(2*m)=
      (L:ℂ)^m*((z:ℂ)+(b:ℂ))^(2*m) := by rw [mul_pow,pow_mul,hs]
  have hLL : (L:ℂ)^(2*m)=(L:ℂ)^m*(L:ℂ)^m := by rw [two_mul,pow_add]
  have hz : (z:ℂ)+(b:ℂ)≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact z.im_ne_zero (by simpa using hi)
  have hL' : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  rw [branch_det,hd,hp,mul_pow,hLL]
  field_simp

end AsymptoticReconstructionBranch

namespace AsymptoticCertificateBranches

open UpperHalfPlane FinitenessCertificate FinitenessGlobalHeight SpanningIntegerRows
open FinitenessComplexGeometry AsymptoticReconstructionBranch

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def residues (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q)

/-- A finite list of the actual branch occurrences in the certificate.
Occurrences from different rows or cells are retained separately. -/
abbrev Index := Σ j : Fin Q, Σ i : (A.coeff j).support, residues i.val.val.1

noncomputable instance index_fintype : Fintype (Index A) := inferInstance

def modulus (v : Index A) : ℕ := v.2.1.val.val.1

noncomputable def level (v : Index A) : ℝ := Nat.lcm N ((modulus A v)^2)

noncomputable def inputShift (v : Index A) : ℝ :=
  (v.2.1.val.val.2-(v.1:ℕ):ℝ)/Q

noncomputable def outputShift (v : Index A) : ℝ := (v.2.2.val:ℝ)/modulus A v

def scalar (v : Index A) : ℚ := A.coeff v.1 v.2.1.val

theorem modulus_pos (v : Index A) : 0<modulus A v :=
  Nat.pos_of_dvd_of_pos v.2.1.val.property.1 hQ

theorem level_pos (hN : 0<N) (v : Index A) : 0<level A v := by
  unfold level
  exact_mod_cast Nat.lcm_pos hN (pow_pos (modulus_pos A v) 2)

theorem level_ge (hN : 0<N) (v : Index A) : (N:ℝ)≤level A v := by
  unfold level
  have hp : 0<Nat.lcm N ((modulus A v)^2) := Nat.lcm_pos hN (pow_pos (modulus_pos A v) 2)
  exact_mod_cast Nat.le_of_dvd hp (Nat.dvd_lcm_left N ((modulus A v)^2))

theorem outputShift_nonneg (v : Index A) : 0≤outputShift A v := by
  unfold outputShift
  positivity

theorem outputShift_lt_one (v : Index A) : outputShift A v<1 := by
  have hlt : v.2.2.val<modulus A v := Finset.mem_range.mp (Finset.mem_filter.mp v.2.2.property).1
  exact (div_lt_one (by exact_mod_cast modulus_pos A v)).mpr (by exact_mod_cast hlt)

noncomputable def matrix (hN : 0<N) (v : Index A) : GL (Fin 2) ℝ :=
  branch (level A v) (inputShift A v) (outputShift A v) (level_pos A hN v).ne'

/-- The cell interval is fixed independently of weight and sector. -/
def cell (v : Index A) : Set ℍ :=
  {z | (v.1:ℝ)/Q≤z.re ∧ z.re<((v.1:ℝ)+1)/Q}

theorem cell_measurable (v : Index A) : MeasurableSet (cell A v) :=
  (measurableSet_Ico.preimage continuous_re.measurable)

theorem cell_subset_strip (v : Index A) : cell A v⊆AsymptoticMassTransport.strip := by
  intro z hz
  have hQ' : (0 : ℝ)<Q := by exact_mod_cast hQ
  have hj : (v.1:ℝ)+1≤Q := by exact_mod_cast (show (v.1:ℕ)+1≤Q by omega)
  have hlo : (0 : ℝ)≤(v.1:ℝ)/Q := by positivity
  have hhi : ((v.1:ℝ)+1)/Q≤1 := (div_le_one hQ').mpr hj
  exact ⟨hlo.trans hz.1,hz.2.trans_le hhi⟩

/-- The strict spanning certificate supplies the ascending cap for every
one of these exact Möbius branches. -/
theorem ascending (hN : 0<N) (P : Parameters A) (v : Index A) (z : ℍ)
    (hz : z∈cell A v) (hy : z.im≤P.ε) : z.im/(matrix A hN v • z).im≤P.ρ := by
  rw [matrix,ratio_forward (level_pos A hN v)]
  have he := P.small v.1 v.2.1.val v.2.1.property (z:ℂ) hz.1 hz.2.le z.im_pos.le hy
  simpa [denominator,level,inputShift,modulus] using he

#print axioms level_pos
#print axioms outputShift_lt_one
#print axioms ascending
#print axioms AsymptoticReconstructionBranch.normalized_branch

end AsymptoticCertificateBranches
