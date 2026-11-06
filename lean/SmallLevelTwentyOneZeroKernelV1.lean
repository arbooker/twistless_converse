module

public import SmallLevelTwentyOneZeroConjugatesV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneZero
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelGenerators
open SmallLevelTwentyOneChiFiveGroup SmallLevelTwentyOneThree
open scoped MatrixGroups ModularForm

private theorem extend_two (F : ℍ → ℂ) (k : ℤ) (n : ℕ) (hn : n+1<24)
    (hprior : ∀ i : Fin 24, i.val<n → F ∣[k] kernel i=F)
    (h0 : F ∣[k] kernel ⟨n,by omega⟩=F) (h1 : F ∣[k] kernel ⟨n+1,hn⟩=F) :
    ∀ i : Fin 24, i.val<n+2 → F ∣[k] kernel i=F := by
  intro i hi
  by_cases h : i.val<n
  · exact hprior i h
  have hc : i.val=n ∨ i.val=n+1 := by omega
  rcases hc with hc|hc
  · have he : i=⟨n,by omega⟩ := Fin.ext hc
    rw [he]; exact h0
  · have he : i=⟨n+1,hn⟩ := Fin.ext hc
    rw [he]; exact h1

theorem original_kernel {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2=0)
    (i : Fin 24) : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  have hz : F ∣[k] (-1:SL(2,ℤ))=F := SmallLevelThirtySix.slash_neg_one_even F m
  obtain ⟨χ,_hχ,hW⟩ := original_fricke_sign (by decide : 0<21) m hf
  have hp (j : Fin 12) (hj : F ∣[k] kernel (sourceIndex j)=F) : F ∣[k] kernel (partnerIndex j)=F :=
    partner_invariant F k χ hW hz j hj
  obtain ⟨hC,hD⟩ := original_C_D hm hf
  obtain ⟨hKp,hKm⟩ := original_Kplus_Kminus hm hf hf2
  have hbase (j : Fin 7) : F ∣[k] kernel (j.castLE (by decide))=F := by
    fin_cases j
    · exact original_T (2*m) f
    · exact original_lower (by decide : 0<21) hf
    · exact original_E hf
    · exact hC
    · exact hD
    · exact hKp
    · exact hKm
  have hfirst (j : Fin 14) : F ∣[k] kernel (j.castLE (by decide))=F := by
    fin_cases j
    · exact hbase 0
    · exact hbase 1
    · exact hbase 2
    · exact hbase 3
    · exact hbase 4
    · exact hbase 5
    · exact hbase 6
    · exact hp 0 (hbase 0)
    · exact hp 1 (hbase 1)
    · exact hp 2 (hbase 2)
    · exact hp 3 (hbase 3)
    · exact hp 4 (hbase 4)
    · exact hp 5 (hbase 5)
    · exact hp 6 (hbase 6)
  have h14 (j : Fin 24) (hj : j.val<14) : F ∣[k] kernel j=F := hfirst ⟨j.val,hj⟩
  have he := SmallLevelGoodHeckeTwo.original_hecke_two (by decide : ¬2∣21) hf.toEulerData m
  rw [hf2,mul_zero,zero_div,zero_smul] at he
  change QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.heckeTwo k F=0 at he
  have h0 := step0 F k he hz h14
  have h16 := extend_two F k 14 (by decide) h14 h0 (hp 7 h0)
  have h1 := step1 F k he hz h16
  have h18 := extend_two F k 16 (by decide) h16 h1 (hp 8 h1)
  have h2 := step2 F k he hz h18
  have h20 := extend_two F k 18 (by decide) h18 h2 (hp 9 h2)
  have h3 := step3 F k he hz h20
  have h22 := extend_two F k 20 (by decide) h20 h3 (hp 10 h3)
  have he5 := SmallLevelGoodHeckeFive.original_hecke_five (by decide : ¬5∣21) hf.toEulerData m
  have h4 := step4 F k _ he5 hz h22
  have h24 := extend_two F k 22 (by decide) h22 h4 (hp 11 h4)
  exact h24 i i.isLt

def J : SL(2,ℤ) := ⟨!![-146,-25;987,169],by decide⟩

theorem original_J {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (hf2 : f 2=0) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] J=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  have hz : F ∣[k] (-1:SL(2,ℤ))=F := SmallLevelThirtySix.slash_neg_one_even F m
  have ht : F ∣[k] target 14=F := target_mem K hz 14 (fun i _ => original_kernel hm hf hf2 i)
  rw [show J=(-1)*target 14 by decide]
  exact K.mul_mem hz ht

#print axioms original_kernel
#print axioms original_J
end SmallLevelTwentyOneZero
