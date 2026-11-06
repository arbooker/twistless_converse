module

public import QuantitativeEulerEndpointLocalSignSpanV1
public import QuantitativeEulerEndpointLocalUniformV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane QuantitativeEulerDiamondDecode QuantitativeEulerDensityGenerators
open AsymptoticSectorSigns AsymptoticCongruenceStrip AsymptoticFreshMatrices
open QuantitativeNewGap
open scoped Classical

def sectorLabel (N : ℕ) (hN : 0<N) : SectorSignIndex N → G
  | none => frickeLabel N hN
  | some p => localAtkinLabel N hN p

def sectorSignRingRow (N : ℕ) (hN : 0<N) (sector : Sector N) (i : SectorSignIndex N) : Ring :=
  symbol (sectorLabel N hN i)-(sectorNormalizerSign sector i:ℂ) • 1

def sectorRowPrime (N : ℕ) (hN : 2≤N) : SectorSignIndex N → ↥N.primeFactors
  | none => ⟨N.minFac,Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd N,by omega⟩⟩
  | some p => ⟨p.val,Nat.mem_primeFactors.mpr ⟨simplePrime_prime p,simplePrime_dvd p,by omega⟩⟩

theorem sectorSignRingRow_mem (N : ℕ) (hN : 0<N) (hN2 : 2≤N)
    (sector : Sector N) (i : SectorSignIndex N) :
    let p := sectorRowPrime N hN2 i
    sectorSignRingRow N hN sector i∈localRowSpan N p.val hN
      (Nat.mem_primeFactors.mp p.property).1.pos (sign sector.1)
      (AsymptoticCylinderRamified.eigenvalue sector p.val) := by
  cases i with
  | none =>
    dsimp only
    simpa only [sectorSignRingRow,sectorLabel,sectorNormalizerSign,signReal_coe] using
      globalSignRow_mem_localRowSpan N _ hN _ (sign sector.1) _
        (by simpa only [pow_two] using sign_sq sector.1)
  | some p =>
    dsimp only [sectorRowPrime]
    have hpM : ¬p.val∣N/p.val := (simplePrime_prime p).coprime_iff_not_dvd.mp (simplePrime_coprime N p)
    let : Fact p.val.Prime := ⟨simplePrime_prime p⟩
    have hr : sectorSignRingRow N hN sector (some p)=
        localSignRow (N/p.val) p.val (simplePrime_colevel_pos N hN p) (simplePrime_prime p).pos
          (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)
          (delta sector p.val) := by
      simp [sectorSignRingRow,sectorLabel,sectorNormalizerSign,signReal_coe,delta,
        localAtkinLabel,localSignRow,p.property]
    rw [hr,AsymptoticCylinderRamified.eigenvalue,ite_eq_right (mem_simplePrimes.mp p.property).2.2]
    have hh := localSignRow_mem_localRowSpan (N/p.val) p.val (simplePrime_colevel_pos N hN p) hpM
      (Nat.gcdA p.val (N/p.val)) (Nat.gcdB p.val (N/p.val)) (simplePrime_bezout N p)
      (sign sector.1) (delta sector p.val) (delta_sq sector p.val)
    simpa only [Nat.mul_div_cancel' (simplePrime_dvd p)] using hh

theorem sectorSignRingRow_original_control {N : ℕ} [NeZero N]
    {excluded : Finset ℕ} {threshold : ℕ} (P : Prepared N excluded threshold)
    (hN : 2≤N) (sector : Sector N) (i : SectorSignIndex N) :
    let p := sectorRowPrime N hN i
    ∃ B : ℝ, 1≤B ∧ ∃ K : ℝ, 0≤K ∧
      WideLocalControl P p.val (Nat.mem_primeFactors.mp p.property).1.pos (sign sector.1)
        (AsymptoticCylinderRamified.eigenvalue sector p.val)
        (sectorSignRingRow N (NeZero.pos N) sector i) B K := by
  apply wide_local_span_control
  · simpa only [pow_two] using sign_sq sector.1
  · exact sectorSignRingRow_mem N (NeZero.pos N) hN sector i

#print axioms sectorSignRingRow_mem
#print axioms sectorSignRingRow_original_control
end QuantitativeEulerEndpointPrepared
