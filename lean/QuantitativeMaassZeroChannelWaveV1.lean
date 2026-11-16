module

public import QuantitativeMaassZeroWaveCauchyV1
public import QuantitativeMaassZeroWavePropagationV1
public import QuantitativeMaassHalfDensityGeneratorV1

/-!
# Checked zero-channel wave and differential identities

This entry point collects the actual translation cosine family on logarithmic
height L², its Schwartz Cauchy problem and finite propagation, differentiation
of the unit horocycle integral, and the half-density conjugation identity.

It does not construct a self-adjoint quotient Laplacian or a quotient wave.
In particular it does not assert that the full quotient constant-term map
has values in full-line L², or discard the exceptional spectral branch.
-/

#print axioms QuantitativeMaass.ZeroWave.shift_strongContinuous
#print axioms QuantitativeMaass.ZeroWave.cosine_law
#print axioms QuantitativeMaass.ZeroWave.cosine_norm_le
#print axioms QuantitativeMaass.ZeroWave.wave_toLp
#print axioms QuantitativeMaass.ZeroWave.schwartzWave_equation
#print axioms QuantitativeMaass.ZeroWave.wave_vanishes_outside
#print axioms QuantitativeMaass.zeroFourier_cartesianLaplacian
#print axioms QuantitativeMaass.logHalfDensity_generator
