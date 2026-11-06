module

public import QuantitativeEulerEndpointReconstructedCheckV1
public import QuantitativeEulerEndpointSharpPacketV1
public import QuantitativeEulerEndpointBlockScheduleV1

/- Sharper actual packet spectral estimate and finite-horizon endpoint budget.
The required actual block-filter recurrence and finite-count transfer remain
unproved; the full goal is not asserted here. -/
#print axioms QuantitativeEulerEndpointSharpPacket.packet_source_sharp_log_error
#print axioms QuantitativeEulerEndpointBlocks.finite_horizon_block_endpoint
