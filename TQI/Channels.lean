import TQI.States

/-!
# Quantum channels

This file tracks Chapter 2.2: linear maps on operators, channels,
representations of channels, and basic examples.

Use Physlib's existing channel API rather than defining local channel
structures:

* bundled channels: `CPTPMap` from `QuantumInfo.Channels.CPTP`;
* unbundled matrix maps and CP/TP predicates:
  `QuantumInfo.Channels.MatrixMap` and `QuantumInfo.Channels.Unbundled`;
* Choi, Kraus, composition, tensor products, and standard examples are already
  developed in Physlib's `QuantumInfo.Channels.*` files.
-/

namespace TQI

end TQI
