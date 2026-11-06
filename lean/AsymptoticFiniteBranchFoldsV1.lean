module

public import AsymptoticConcreteBranchMatrixV1
public import AsymptoticFiniteBranchDataV1
public import AsymptoticRegularFoldedTerminalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Set

variable {L : ℚ} (hL : 0<L) (b d : ℚ)

noncomputable def lowFold {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t : ℕ) (n : ℤ) : Branch where
  label := AsymptoticRationalBranches.fold hL b d n
  coefficient := AsymptoticFoldedLow.coefficient (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) s r cap t n
  measurable := AsymptoticFoldedLow.coefficient_measurable
    (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) hs hr cap t n
  bound := AsymptoticFoldMajorant.majorant cap (4/(L:ℝ)) n^t
  bound_nonneg := pow_nonneg (AsymptoticFoldMajorant.majorant_nonneg hcap (by positivity) n) t
  norm_le := AsymptoticFoldedLow.coefficient_norm_le
    (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) hcap hd0 hd1 hstrip t n

theorem holomorphic_lowFold {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t nweight : ℕ) (n : ℤ) :
    holomorphic (lowFold hL b d hs hr hcap hd0 hd1 hstrip t n) nweight=
      AsymptoticFoldedLow.term (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ)
        hs hr hcap hd0 hd1 hstrip t nweight n := by
  exact AsymptoticConcreteRationalBranch.operator_fold hL b d n _ _ _ nweight

theorem regular_lowFold {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {cap : ℝ} (hcap : 0≤cap) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hstrip : r⊆AsymptoticMassTransport.strip) (t : ℕ) (n : ℤ) (z : ℍ) :
    regular (lowFold hL b d hs hr hcap hd0 hd1 hstrip t n) z=
      AsymptoticRegularFoldedLow.term hL b d s r hcap hd0 hd1 hstrip t n z := rfl

noncomputable def terminalFold {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (n : ℤ) : Branch where
  label := AsymptoticRationalBranches.fold hL b d n
  coefficient := AsymptoticFoldedTerminal.coefficient (show (0:ℝ)<L by exact_mod_cast hL)
    (b:ℝ) (d:ℝ) s r ε t n
  measurable := AsymptoticFoldedTerminal.coefficient_measurable
    (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) hs hr ε t n
  bound := AsymptoticFoldMajorant.majorant 1 ((ε*(L:ℝ))^2)⁻¹ n
  bound_nonneg := AsymptoticFoldMajorant.majorant_nonneg zero_le_one (by positivity) n
  norm_le := AsymptoticFoldedTerminal.coefficient_norm_le
    (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ) hε hd0 hd1 hsource hstrip ht n

theorem holomorphic_terminalFold {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (n : ℤ) :
    holomorphic (terminalFold hL b d hs hr hε hd0 hd1 hsource hstrip ht n) m=
      AsymptoticFoldedTerminal.term (show (0:ℝ)<L by exact_mod_cast hL) (b:ℝ) (d:ℝ)
        hs hr hε hd0 hd1 hsource hstrip ht m n := by
  exact AsymptoticConcreteRationalBranch.operator_fold hL b d n _ _ _ m

theorem regular_terminalFold {s r : Set ℍ} (hs : MeasurableSet s) (hr : MeasurableSet r)
    {ε : ℝ} (hε : 0<ε) (hd0 : 0≤(d:ℝ)) (hd1 : (d:ℝ)≤1)
    (hsource : s⊆{z | z.im≤ε}) (hstrip : r⊆AsymptoticMassTransport.strip)
    {t : ℕ} (ht : 2≤t) (n : ℤ) (z : ℍ) :
    regular (terminalFold hL b d hs hr hε hd0 hd1 hsource hstrip ht n) z=
      AsymptoticRegularFoldedTerminal.term hL b d s r hε hd0 hd1 hsource hstrip ht n z := rfl

#print axioms holomorphic_lowFold
#print axioms regular_lowFold
#print axioms holomorphic_terminalFold
#print axioms regular_terminalFold

end AsymptoticFiniteBranch
