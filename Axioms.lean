/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound

/-!
# Axiom check

`lake env lean Axioms.lean` fails unless each main theorem depends only on the three standard
axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

open PierceLengthBound

/-- info: 'PierceLengthBound.P_le_45_152' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_45_152

/-- info: 'PierceLengthBound.P_le_8_27' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_8_27

/-- info: 'PierceLengthBound.P_le_11_37' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_11_37

/-- info: 'PierceLengthBound.P_le_23_77' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_23_77

/-- info: 'PierceLengthBound.P_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le

/-- info: 'PierceLengthBound.P_le_loglog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_loglog

/-- info: 'PierceLengthBound.P_le_rises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_rises

/-- info: 'PierceLengthBound.hankelInv_pos_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hankelInv_pos_int

/-! The following audit covers proved components of the unfinished `13/44` refinement. -/

/-- info: 'PierceLengthBound.FixedDividend.pattern_cubic_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.pattern_cubic_obstruction

/-- info: 'PierceLengthBound.FixedDividend.line_direction_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.line_direction_exceptional

/-- info: 'PierceLengthBound.FixedDividend.exceptional_minors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.exceptional_minors

/-- info: 'PierceLengthBound.newtonQuartic_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms newtonQuartic_orthogonal

/-- info: 'PierceLengthBound.FixedDividend.resultant_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.resultant_four

/-- info: 'PierceLengthBound.FixedDividend.local_count_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.local_count_dichotomy
