/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound
import Lean.Util.CollectAxioms

/-!
# Axiom check

`lake env lean Axioms.lean` fails unless each main theorem depends only on the three standard
axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

open PierceLengthBound

/-- info: 'PierceLengthBound.P_le_joint_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_joint_optimal

/-- info: 'PierceLengthBound.P_le_2201_7480' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_2201_7480

/-- info: 'PierceLengthBound.P_le_128_435' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_128_435

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

/-! Proved components of the unfinished `18/61` refinement. -/

/-- info: 'PierceLengthBound.FixedDividend.line_identity_03' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.line_identity_03

/-- info: 'PierceLengthBound.FixedDividend.line_identity_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.line_identity_12

/-- info: 'PierceLengthBound.FixedDividend.line_identity_23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.line_identity_23

/-- info: 'PierceLengthBound.FixedDividend.line_identity_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.line_identity_14

/-- info: 'PierceLengthBound.FixedDividend.norm_degree_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.norm_degree_le_one

/-- info: 'PierceLengthBound.FixedDividend.half_weight_minor_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.half_weight_minor_bound

/-- info: 'PierceLengthBound.FixedDividend.weighted_count_sixth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.weighted_count_sixth

/-- info: 'PierceLengthBound.FixedDividend.weighted_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.weighted_exponent

/-- info: 'PierceLengthBound.FixedDividend.small_scale_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.small_scale_exponent

/-! Actual orbit identities and universal resultant degree bounds. -/


/-- info: 'PierceLengthBound.FixedDividend.orbit_fixed_dividend_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbit_fixed_dividend_identity

/-- info: 'PierceLengthBound.FixedDividend.orthPoly_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orthPoly_recurrence

/-- info: 'PierceLengthBound.FixedDividend.orbitNorm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbitNorm_pos

/-- info: 'PierceLengthBound.FixedDividend.orbitNorm_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbitNorm_hankel

/-- info: 'PierceLengthBound.FixedDividend.orbit_line_obstructions_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbit_line_obstructions_excluded

/-- info: 'PierceLengthBound.FixedDividend.orbitQuartic_newton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbitQuartic_newton

/-- info: 'PierceLengthBound.FixedDividend.nextQuartic_newton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.nextQuartic_newton

/-- info: 'PierceLengthBound.FixedDividend.orbit_lineQuadratic_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbit_lineQuadratic_zero

/-- info: 'PierceLengthBound.FixedDividend.orbit_lineNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbit_lineNorm_eq

/-- info: 'PierceLengthBound.FixedDividend.line_resultant_natDegree_le_six' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.line_resultant_natDegree_le_six

/-- info: 'PierceLengthBound.FixedDividend.orbit_no_exceptional_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbit_no_exceptional_line

/-! Audit all exported mathematical declarations, including intermediate results.
The separate exercise statements in Challenge are intentionally outside this scope. -/

open Lean Elab Command

set_option maxHeartbeats 0 in
-- Traverse the transitive axiom metadata for every exported project declaration.
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut curve : Nat := 0
  let mut curveVendor : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing module for {name}"
    let isPierce := (`PierceLengthBound).isPrefixOf mod
    let isCurve := (`AffineCurveCounting).isPrefixOf mod
    let isCurveVendor := (`ArithmeticHeights).isPrefixOf mod
    if !isPierce && !isCurve && !isCurveVendor then continue
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => !allowed.contains a
    unless bad.isEmpty do
      throwError "Disallowed axioms in {name}: {bad}"
    if isPierce then checked := checked + 1
    if isCurve then curve := curve + 1
    if isCurveVendor then curveVendor := curveVendor + 1
  unless checked > 0 ∧ curve > 0 ∧ curveVendor > 0 do
    throwError "Axiom audit coverage failure"
  logInfo m!"Axiom audit passed: {checked} PierceLengthBound, {curve} AffineCurveCounting \
    and {curveVendor} curve-vendor declarations; only {allowed}."
