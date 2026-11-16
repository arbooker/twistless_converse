module

public import QuantitativeMaassCuspAveragingCheckV1
public import QuantitativeMaassCuspAveragedWaveV1
public import QuantitativeArithmeticMaassWaveTestSeparationV1

/- Integration check only. This proves the actual height-averaged weak
wave equation, not yet the log-half-density local uniqueness/intertwining
or the full short-interval Weyl theorem. -/

#print axioms QuantitativeMaass.cuspPeriodTest_pairing
#print axioms QuantitativeMaass.cuspPeriodTest_laplacian_pairing
#print axioms QuantitativeMaass.Wave.cuspWaveTest_differentiable
#print axioms QuantitativeMaass.Wave.cuspWaveTest_second_derivative
#print axioms QuantitativeMaass.Wave.cuspWaveTest_initial_velocity
#print axioms QuantitativeArithmeticMaassLocalWave.ae_zero_of_classical_testAverages
