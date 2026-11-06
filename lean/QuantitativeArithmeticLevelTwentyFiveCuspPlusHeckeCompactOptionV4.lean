module
public meta import QuantitativeArithmeticCompactCommandsV1
public import QuantitativeArithmeticSmallLevelTwentyFiveCuspPlusLaurentTheoryV4
set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelTwentyFive.CuspPlusLaurent
open QuantitativeArithmeticSevenLaurentRows
compact_certificate theorem hecke_lookup_source_1058 : source 1058 = [(cuspCoefficient5,15,cuspExponent31),(cuspCoefficient2,30,cuspExponent22),(cuspCoefficient5,60,cuspExponent13),(cuspCoefficient5,90,cuspExponent31)] := by rfl
#print axioms hecke_lookup_source_1058
compact_certificate theorem hecke_lookup_source_1128 : source 1128 = [(cuspCoefficient5,10,cuspExponent31),(cuspCoefficient2,30,cuspExponent29),(cuspCoefficient5,60,cuspExponent31),(cuspCoefficient5,90,cuspExponent26),(cuspCoefficient5,110,cuspExponent31)] := by rfl
#print axioms hecke_lookup_source_1128
compact_certificate theorem hecke_lookup_basis_10 : basis 10 = [(basisCoefficient2,3,basisExponent19)] := by rfl
#print axioms hecke_lookup_basis_10
compact_certificate theorem hecke_lookup_basis_15 : basis 15 = [(basisCoefficient2,3,basisExponent11)] := by rfl
#print axioms hecke_lookup_basis_15
compact_certificate theorem hecke_lookup_basis_30 : basis 30 = [(basisCoefficient3,3,basisExponent23)] := by rfl
#print axioms hecke_lookup_basis_30
compact_certificate theorem hecke_lookup_basis_60 : basis 60 = [(basisCoefficient2,3,basisExponent23)] := by rfl
#print axioms hecke_lookup_basis_60
compact_certificate theorem hecke_lookup_basis_90 : basis 90 = [(basisCoefficient2,3,basisExponent23)] := by rfl
#print axioms hecke_lookup_basis_90
compact_certificate theorem hecke_lookup_basis_110 : basis 110 = [(basisCoefficient2,3,basisExponent19)] := by rfl
#print axioms hecke_lookup_basis_110
compact_certificate theorem hecke_two_certificate_compact : substitute basis (source 1058) = [(-2,3,(-2,0,0,0,0,0,0)),(-1,3,(-1,0,0,0,1,0,0)),(-1,3,(0,0,0,0,0,0,0))] := by
  rw [← substituteCompute_eq, hecke_lookup_source_1058]
  simp only [substituteCompute, hecke_lookup_basis_10, hecke_lookup_basis_15,
    hecke_lookup_basis_30, hecke_lookup_basis_60, hecke_lookup_basis_90, hecke_lookup_basis_110]
  decide +kernel
#print axioms hecke_two_certificate_compact
compact_certificate theorem hecke_three_certificate_compact : substitute basis (source 1128) = [(-3,3,(0,-2,0,0,0,0,0)),(-1,3,(0,-1,0,0,0,1,0)),(-1,3,(0,0,0,0,0,0,0))] := by
  rw [← substituteCompute_eq, hecke_lookup_source_1128]
  simp only [substituteCompute, hecke_lookup_basis_10, hecke_lookup_basis_15,
    hecke_lookup_basis_30, hecke_lookup_basis_60, hecke_lookup_basis_90, hecke_lookup_basis_110]
  decide +kernel
#print axioms hecke_three_certificate_compact
end QuantitativeArithmeticSmallLevelTwentyFive.CuspPlusLaurent
end
