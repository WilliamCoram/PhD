/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

/-
The root module of the Tau Ceti chain (`PhD/TauCeti/`).

This chain restates material for upstreaming to Tau Ceti and is deliberately separate from
`PhD/Main/`: neither side may import the other (CI-gated).  `lake build PhD.TauCeti` builds the
whole chain, which is how it is gated in CI.

The project root `PhD.lean` must **not** import this module: both chains develop the
`NewtonPolygon` namespace, so importing the two into one environment would clash.
-/
import PhD.TauCeti.Code.NewtonPolygons.Examples
import PhD.TauCeti.Code.NewtonPolygons.Int
import PhD.TauCeti.Code.NewtonPolygons.Minkowski
