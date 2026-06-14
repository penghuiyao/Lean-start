import TQI.Operators

/-!
# Quantum states and registers

This file tracks Chapter 2.1: registers, classical state sets, quantum states,
reduced states, product states, and purifications.

Use Physlib's existing state API rather than defining local state structures:

* mixed states/density operators: `MState` from
  `QuantumInfo.States.Mixed.MState`;
* pure states: `Ket` from `QuantumInfo.States.Pure.Braket`;
* ensembles: `MEnsemble` and `PEnsemble` from `QuantumInfo.States.Ensemble`.
-/

namespace TQI

end TQI
