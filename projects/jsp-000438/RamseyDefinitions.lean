/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0. See LICENSE-APACHE-2.0.

The two definitions below are extracted verbatim (including their namespace)
from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean at
40e7c98697de6f66b8cbdbf641749ab39ed9c152. Imports and comments are shortened.
-/
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Order.Lattice.Nat

namespace SimpleGraph

noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { n : ℕ | ∀ (C : SimpleGraph (Fin n)), G.IsContained C ∨ H.IsContained Cᶜ }

noncomputable def diagonalGraphRamsey {α : Type*} [Fintype α] (G : SimpleGraph α) : ℕ :=
  graphRamsey G G

end SimpleGraph
