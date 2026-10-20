#!/usr/bin/env python3
"""After lake build, audit the weighted-count dependencies of the main bounds.

The integral lift and the joint-invariant bounds use no weighted-count theorem.
The exterior-lattice bounds use exactly the short-vector count and the
reciprocal weight bound, and none of the other weighted counts.

Lean's module system hides imported theorem bodies by default. Import every
project dependency with `import all` before traversing those bodies.
"""
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGETS = (
    "PierceLengthBound.IntegralLiftPatternCount",
    "PierceLengthBound.JointLiftPatternCount",
    "PierceLengthBound.JointLiftCoverCount",
    "PierceLengthBound.OrbitConicGapCount",
    "PierceLengthBound.JointLiftInfinityOrder",
    "PierceLengthBound.ChartRawDeterminantOrders",
    "PierceLengthBound.JointLiftChartOrders",
    "PierceLengthBound.JointLiftNormalizedOrders",
    "PierceLengthBound.JointLiftNormalizedFiniteOrders",
    "PierceLengthBound.NormalizationInfinityDegree",
    "PierceLengthBound.ChartFunctionParameters",
    "PierceLengthBound.JointLiftCurvatureTranscendence",
    "PierceLengthBound.BranchZeroDegree",
    "PierceLengthBound.JointLiftPoleDegree",
    "PierceLengthBound.JointLiftFiniteZero",
    "PierceLengthBound.JointLiftCurvatureDegree",
    "PierceLengthBound.JointLiftGraphLowerDegree",
    "PierceLengthBound.JointLiftBound",
    "PierceLengthBound.PoweredJointGraphLowerDegree",
    "PierceLengthBound.PoweredJointPointCount",
    "PierceLengthBound.JointLiftMain",
    "PierceLengthBound.LatticeJointMain",
)
IMPORT = re.compile(r"^(?:public )?import (?:all )?(\S+)", re.MULTILINE)


def main() -> int:
    modules: set[str] = set()

    def visit(module: str) -> None:
        if module in modules or not module.startswith("PierceLengthBound."):
            return
        modules.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        for dependency in IMPORT.findall(source.read_text()):
            visit(dependency)

    for target in TARGETS:
        visit(target)
    imports = "\n".join(f"import all {module}" for module in sorted(modules))
    audit = r"""
import Lean
open Lean Elab Command
set_option maxHeartbeats 1000000 in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let banned : Array Name := #[`PierceLengthBound.FixedDividendWeights,
    `PierceLengthBound.ConicWeights, `PierceLengthBound.ParityWeights,
    `PierceLengthBound.ShortSum]
  let bannedDeclarations : Array Name := #[`PierceLengthBound.short_count,
    `PierceLengthBound.lattice_fiber_count, `PierceLengthBound.pattern_count_lattice,
    `PierceLengthBound.two_state_window_152]
  let mut pending := #[``PierceLengthBound.P_le_joint_optimal,
    ``PierceLengthBound.P_le_2201_7480,
    ``PierceLengthBound.FixedDividend.orbitPoweredJointGraph_retained_degree_range,
    ``PierceLengthBound.FixedDividend.selected_poweredJointGraph_gap_count,
    ``PierceLengthBound.FixedDividend.P_le_128_435,
    ``PierceLengthBound.FixedDividend.jointLiftPatternEstimate_exists,
    ``PierceLengthBound.FixedDividend.P_le_151_513_of_pattern_estimate,
    ``PierceLengthBound.FixedDividend.P_le_128_435_of_pattern_estimate,
    ``PierceLengthBound.FixedDividend.selected_jointGraph_cover_gap_count_slow,
    ``PierceLengthBound.FixedDividend.orbit_conic_gap_count_slow,
    ``PierceLengthBound.FixedDividend.nonexceptional_rank_five_discrete_order,
    ``PierceLengthBound.FixedDividend.monic_quartic_quotient_discrete_order,
    ``PierceLengthBound.FixedDividend.curvature_discrete_orders,
    ``PierceLengthBound.FixedDividend.nonexceptional_raw_determinant_discrete_orders,
    ``PierceLengthBound.FixedDividend.retained_quotient_and_rank_three_discrete_orders,
    ``PierceLengthBound.FixedDividend.retained_joint_coordinates_discrete_orders,
    ``PierceLengthBound.FixedDividend.orbit_curvature_finite_discrete_order,
    ``PierceLengthBound.FixedDividend.nonexceptional_chart_infinity_branch,
    ``PierceLengthBound.FixedDividend.retained_normalized_branch_joint_orders,
    ``PierceLengthBound.FixedDividend.normalized_affine_curvature_order,
    ``PierceLengthBound.FixedDividend.nonexceptional_normalized_infinity_dimension,
    ``PierceLengthBound.FixedDividend.nonexceptional_normalized_infinity_degree,
    ``PierceLengthBound.FixedDividend.polynomial_parameter_branch_orders,
    ``PierceLengthBound.FixedDividend.function_zero_pole_fiber_degrees,
    ``PierceLengthBound.FixedDividend.functionParameterBranchOrder_inverse,
    ``PierceLengthBound.FixedDividend.nonexceptional_function_finite,
    ``PierceLengthBound.FixedDividend.orbitJoint_exists_transcendental_curvature_combination,
    ``PierceLengthBound.FixedDividend.branch_order_nonnegative_of_finite_parameter,
    ``PierceLengthBound.FixedDividend.function_parameter_branch_transport_with_degree,
    ``PierceLengthBound.FixedDividend.branch_zero_degree_with_extra,
    ``PierceLengthBound.FixedDividend.retained_curvature_pole_affine_center,
    ``PierceLengthBound.FixedDividend.retained_curvature_function_degree_le_envelope,
    ``PierceLengthBound.FixedDividend.orbitJoint_exists_extra_normalized_zero,
    ``PierceLengthBound.FixedDividend.retained_curvature_function_degree_lower_bound,
    ``PierceLengthBound.FixedDividend.retained_curvature_pole_degree_lower_bound,
    ``PierceLengthBound.FixedDividend.jointGraph_pole_envelope_degree_le_hilbert,
    ``PierceLengthBound.FixedDividend.orbitJointGraph_retained_degree_range]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if bannedDeclarations.contains name then
      throwError "Weighted-count dependency: {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing module for {name}"
    unless (`PierceLengthBound).isPrefixOf mod do continue
    if banned.contains mod then
      throwError "Weighted-count dependency: {name} in {mod}"
    let some ci := env.find? name | throwError "Missing declaration {name}"
    pending := pending ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  logInfo m!"Integral/joint-lift dependency audit passed ({seen.size} visited constants)."

set_option maxHeartbeats 1000000 in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let banned : Array Name := #[`PierceLengthBound.ConicWeights,
    `PierceLengthBound.ParityWeights, `PierceLengthBound.ShortSum]
  let bannedDeclarations : Array Name := #[`PierceLengthBound.lattice_fiber_count,
    `PierceLengthBound.pattern_count_lattice, `PierceLengthBound.two_state_window_152]
  let required : Array Name := #[`PierceLengthBound.short_count,
    `PierceLengthBound.FixedDividend.reciprocal_sum_bound]
  let mut pending := #[``PierceLengthBound.P_le_lattice_optimal,
    ``PierceLengthBound.P_le_153_520]
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if bannedDeclarations.contains name then
      throwError "Unexpected weighted-count dependency: {name}"
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | throwError "Missing module for {name}"
    unless (`PierceLengthBound).isPrefixOf mod do continue
    if banned.contains mod then
      throwError "Unexpected weighted-count dependency: {name} in {mod}"
    let some ci := env.find? name | throwError "Missing declaration {name}"
    pending := pending ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
  for name in required do
    unless seen.contains name do
      throwError "Expected lattice dependency not reached: {name}"
  logInfo m!"Exterior-lattice dependency audit passed ({seen.size} visited constants)."
"""
    with tempfile.TemporaryDirectory(prefix="pierce-lift-audit-") as directory:
        source = Path(directory) / "Audit.lean"
        source.write_text("module\n" + imports + "\n" + audit)
        return subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT).returncode


if __name__ == "__main__":
    raise SystemExit(main())
