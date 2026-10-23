/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendSelection
public import PierceLengthBound.Main

/-!
# Slow growth under a shift

A slowly growing function remains slowly growing after adding one.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

lemma slowGrowth_add_one {K : ℕ → ℕ} (hK : SlowGrowth K) :
    SlowGrowth (fun a => K a + 1) :=
  slowGrowth_add hK (slowGrowth_const 1)

end PierceLengthBound.FixedDividend
