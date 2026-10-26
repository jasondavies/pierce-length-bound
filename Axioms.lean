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

`lake env lean Axioms.lean` (also run by `lake build`) fails unless each theorem selected in
`comparator.json` depends only on the three standard axioms `propext`, `Classical.choice` and
`Quot.sound`. Further `#print axioms` checks cover selected intermediate results: the moment
and line identities, the orbit identities and resultant degree bounds, and the polar identities,
certificates and reductions. The final check audits every exported declaration of
`PierceLengthBound`, of the CCDN library, and of CCDN's vendored Bombieri–Vaaler development
(`ArithmeticHeights`).
-/

open PierceLengthBound

/-- info: 'PierceLengthBound.P_le_polar_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_polar_optimal

/-- info: 'PierceLengthBound.P_le_4317_14677' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_4317_14677

/-- info: 'PierceLengthBound.P_le_lattice_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_lattice_optimal

/-- info: 'PierceLengthBound.P_le_153_520' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P_le_153_520

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

/-- info: 'PierceLengthBound.hankelInv_first_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hankelInv_first_four

/-! Orthogonality of the Newton quartic and the rank-four resultant. -/

/-- info: 'PierceLengthBound.newtonQuartic_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms newtonQuartic_orthogonal

/-- info: 'PierceLengthBound.FixedDividend.resultant_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.resultant_four

/-! The line identities and the affine-norm degree argument. -/

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

/-! Orbit identities, line exclusion and universal resultant degree bounds. -/

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

/-! The polar identities and certificates, the hypersurface pattern count, and the reductions
of the polar exponents to the six-term estimates. -/

/-- info: 'PierceLengthBound.FixedDividend.orbit_polar_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbit_polar_identity

/-- info: 'PierceLengthBound.FixedDividend.orbit_rankFive_polar_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.orbit_rankFive_polar_identity

/-- info: 'PierceLengthBound.FixedDividend.polar_good_axis_local_colength_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.polar_good_axis_local_colength_four

/-- info: 'PierceLengthBound.FixedDividend.branchSexticSpecialization_irreducible_rat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.branchSexticSpecialization_irreducible_rat

/-- info: 'PierceLengthBound.FixedDividend.normal_short_weight_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.normal_short_weight_sum

/-- info: 'PierceLengthBound.FixedDividend.P_le_4317_14677_of_six_term_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.P_le_4317_14677_of_six_term_count

/-- info: 'PierceLengthBound.FixedDividend.P_le_polar_optimal_of_six_term_estimates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.P_le_polar_optimal_of_six_term_estimates

/-- info: 'PierceLengthBound.FixedDividend.hypersurface_pattern_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FixedDividend.hypersurface_pattern_count

/-! Audit all exported mathematical declarations, including intermediate results, from
`PierceLengthBound`, CCDN and CCDN's vendored `ArithmeticHeights`.
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
  let mut heights : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing module for {name}; \
      the environment's module table is inconsistent, so rebuild with `lake build`"
    let isPierce := (`PierceLengthBound).isPrefixOf mod
    let isCurve := (`CCDN).isPrefixOf mod
    let isHeights := (`ArithmeticHeights).isPrefixOf mod
    if !isPierce && !isCurve && !isHeights then continue
    let axioms ← collectAxioms name
    let bad := axioms.filter fun a => !allowed.contains a
    unless bad.isEmpty do
      throwError "Disallowed axioms in {name}: {bad}"
    if isPierce then checked := checked + 1
    if isCurve then curve := curve + 1
    if isHeights then heights := heights + 1
  unless checked > 0 ∧ curve > 0 ∧ heights > 0 do
    throwError "Axiom audit coverage failure: found {checked} PierceLengthBound, {curve} CCDN \
      and {heights} ArithmeticHeights declarations. Each must be positive; if CCDN renamed \
      its `CCDN` or vendored `ArithmeticHeights` module prefix, update the prefixes above."
  logInfo m!"Axiom audit passed: {checked} PierceLengthBound, {curve} CCDN \
    and {heights} ArithmeticHeights declarations; only {allowed}."
