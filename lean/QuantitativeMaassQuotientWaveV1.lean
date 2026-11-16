module

public import QuantitativeMaassWaveContinuityV1
public import QuantitativeMaassWaveDomainV1

/-! # Actual quotient energy realization and unshifted cosine family

This entry imports the constructed nonnegative self-adjoint Friedrichs
Laplacian on the literal quotient Hilbert space, its proved smooth Poincaré
form core, and the actual strongly continuous self-adjoint contraction
cosine family obtained from its bounded inverse. The family preserves the
unbounded operator graph and has its exact continuous-functional-calculus
formula on the inverse range.

No essential self-adjointness of the original differential graph, finite
propagation, shifted-wave normalization, kernel formula, pretrace formula,
or quantitative Lindenstrauss–Venkatesh estimate is asserted here.
-/

#print axioms QuantitativeMaass.friedrichsLaplacian_isSelfAdjoint
#print axioms QuantitativeMaass.poincareEnergySeed_completion_dense
#print axioms QuantitativeMaass.Wave.quotientWave_cosine
#print axioms QuantitativeMaass.Wave.quotientWave_stronglyContinuous
#print axioms QuantitativeMaass.Wave.quotientWave_graph
