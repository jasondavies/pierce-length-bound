import PierceBound

/-!
# Axiom check

`lake env lean Axioms.lean` fails unless each main theorem depends only on the three standard
axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

open PierceBound

/-- info: 'PierceBound.P_le_45_152' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms P_le_45_152

/-- info: 'PierceBound.P_le_8_27' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms P_le_8_27

/-- info: 'PierceBound.P_le_11_37' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms P_le_11_37

/-- info: 'PierceBound.P_le_23_77' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms P_le_23_77

/-- info: 'PierceBound.P_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms P_le

/-- info: 'PierceBound.P_le_loglog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms P_le_loglog

/-- info: 'PierceBound.P_le_rises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms P_le_rises

/-- info: 'PierceBound.hankelInv_pos_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hankelInv_pos_int
