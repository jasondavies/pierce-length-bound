#!/usr/bin/env python3
"""After lake build, audit which weighted lattice counts the main bounds depend on.

Two audits run in one Lean file:

1. Joint-lift audit. The joint-invariant bounds `P_le_joint_optimal`, `P_le_2201_7480`
   and `P_le_128_435`, and the intermediate joint-lift and fixed-dividend results listed
   as roots below, use none of the weighted-lattice machinery of the `45/152` bound
   (short-vector counts, lattice fiber counts and reciprocal or fractional weights).
2. Exterior-lattice audit. The lattice bounds `P_le_lattice_optimal` and `P_le_153_520`
   reach exactly two weighted counts, `short_count` and
   `FixedDividend.reciprocal_sum_bound`, and none of the others.

The traversal follows the types and values of every reachable `PierceLengthBound`
declaration. Declarations are written as ``Foo.bar`` literals, so a renamed declaration
fails at elaboration instead of silently checking nothing; banned modules must be
imported, for the same reason. A failure prints the dependency path from a root.

Lean's module system hides imported theorem bodies by default, so the audit imports every
module under PierceLengthBound/ with `import all` before traversing those bodies.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = "PierceLengthBound"
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.MULTILINE)

AUDIT = r"""
import Lean
open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  -- The path by which `name` was first reached, from one of the roots.
  let pathTo (parent : Std.HashMap Name Name) (name : Name) : String := Id.run do
    let mut path := [name]
    let mut current := name
    for _ in List.range (parent.size + 1) do
      match parent[current]? with
      | some previous =>
        path := previous :: path
        current := previous
      | none => break
    return " → ".intercalate (path.map toString)
  -- Traverse the type and value dependencies of `roots` through `PierceLengthBound`
  -- declarations, failing if a banned module or declaration is reached.
  -- Returns every visited constant.
  let audit (label : String) (roots bannedModules bannedDeclarations : Array Name) :
      CommandElabM (Std.HashSet Name) := do
    for mod in bannedModules do
      unless modules.contains mod do
        throwError "{label}: banned module {mod} is not imported. Update the banned \
          module list in scripts/check-weighted-count-dependencies.py after a rename."
    let mut pending := roots
    let mut parent : Std.HashMap Name Name := {}
    let mut seen : Std.HashSet Name := {}
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      if bannedDeclarations.contains name then
        throwError "{label}: banned declaration reached: {pathTo parent name}"
      let some idx := env.getModuleIdxFor? name | continue
      let some mod := modules[idx.toNat]?
        | throwError "{label}: no module recorded for {name}; rebuild with `lake build`"
      unless (`PierceLengthBound).isPrefixOf mod do continue
      if bannedModules.contains mod then
        throwError "{label}: declaration from banned module {mod} reached: \
          {pathTo parent name}"
      let some ci := env.find? name
        | throwError "{label}: declaration {name} is not in the environment; rebuild with \
            `lake build` and check that its module is imported"
      let mut children := ci.type.getUsedConstants
      if let some value := ci.value? (allowOpaque := true) then
        children := children ++ value.getUsedConstants
      for child in children do
        unless seen.contains child || parent.contains child do
          parent := parent.insert child name
      pending := pending ++ children
    return seen

  -- Audit 1: the joint-lift and fixed-dividend bounds avoid the `45/152` weighted-lattice
  -- machinery entirely. Each root is a public bound or a main intermediate result.
  let jointRoots : Array Name := #[``PierceLengthBound.P_le_joint_optimal,
    ``PierceLengthBound.P_le_2201_7480,
    ``PierceLengthBound.P_le_128_435,
    ``PierceLengthBound.FixedDividend.orbitPoweredJointGraph_retained_degree_range,
    ``PierceLengthBound.FixedDividend.selected_poweredJointGraph_gap_count,
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
  -- Banned modules: the reciprocal and half-power minor-lattice weights
  -- (`FixedDividendWeights`), the cube-root and quarter-power weights of the proposed
  -- `135/458` and `180/611` refinements (`ConicWeights`, `ParityWeights`), and the
  -- short-interval divisor sums of the conditional refinement (`ShortSum`).
  let jointBannedModules : Array Name := #[`PierceLengthBound.FixedDividendWeights,
    `PierceLengthBound.ConicWeights, `PierceLengthBound.ParityWeights,
    `PierceLengthBound.ShortSum]
  -- Banned declarations: the `45/152` short-vector count, lattice fiber and pattern
  -- counts, and window bound. Their modules also hold results the joint lift may use.
  let jointBannedDeclarations : Array Name := #[``PierceLengthBound.short_count,
    ``PierceLengthBound.lattice_fiber_count, ``PierceLengthBound.pattern_count_lattice,
    ``PierceLengthBound.two_state_window_152]
  let jointSeen ← audit "Joint-lift audit" jointRoots jointBannedModules
    jointBannedDeclarations
  logInfo m!"Joint-lift dependency audit passed ({jointSeen.size} visited constants)."

  -- Audit 2: the exterior-lattice bounds reach only the weighted counts `short_count` and
  -- `FixedDividend.reciprocal_sum_bound`. Unlike audit 1, `FixedDividendWeights` is
  -- allowed here because it holds `reciprocal_sum_bound`, and `short_count` is required.
  let latticeRoots : Array Name := #[``PierceLengthBound.P_le_lattice_optimal,
    ``PierceLengthBound.P_le_153_520]
  -- Banned modules: the other lattice weights and the short-interval divisor sums.
  let latticeBannedModules : Array Name := #[`PierceLengthBound.ConicWeights,
    `PierceLengthBound.ParityWeights, `PierceLengthBound.ShortSum]
  -- Banned declarations: the `45/152` lattice fiber and pattern counts and window bound.
  let latticeBannedDeclarations : Array Name := #[``PierceLengthBound.lattice_fiber_count,
    ``PierceLengthBound.pattern_count_lattice, ``PierceLengthBound.two_state_window_152]
  -- Required declarations: the two weighted counts the lattice bounds must use.
  let latticeRequired : Array Name := #[``PierceLengthBound.short_count,
    ``PierceLengthBound.FixedDividend.reciprocal_sum_bound]
  let latticeSeen ← audit "Exterior-lattice audit" latticeRoots latticeBannedModules
    latticeBannedDeclarations
  for name in latticeRequired do
    unless latticeSeen.contains name do
      throwError "Exterior-lattice audit: expected dependency {name} was not reached"
  logInfo m!"Exterior-lattice dependency audit passed ({latticeSeen.size} visited constants)."
"""


def project_modules() -> list[str]:
    """Every module under PierceLengthBound/, each of which must be built by `lake build`."""
    directory = ROOT / PACKAGE
    modules = sorted(
        ".".join((PACKAGE, *path.relative_to(directory).with_suffix("").parts))
        for path in directory.rglob("*.lean")
    )
    reached: set[str] = set()

    def visit(module: str) -> None:
        if module in reached or not (module == PACKAGE or module.startswith(PACKAGE + ".")):
            return
        reached.add(module)
        source = ROOT / (module.replace(".", "/") + ".lean")
        for dependency in IMPORT.findall(source.read_text(encoding="utf-8")):
            visit(dependency)

    visit(PACKAGE)
    unbuilt = [module for module in modules if module not in reached]
    if unbuilt:
        raise ValueError(f"not imported (transitively) by {PACKAGE}.lean, so lake build "
                         f"does not build them: {', '.join(unbuilt)}")
    return modules


def main() -> int:
    try:
        modules = project_modules()
    except (OSError, ValueError) as error:
        print(f"Weighted-count dependency audit setup failed: {error}", file=sys.stderr)
        return 1
    imports = "\n".join(f"import all {module}" for module in modules)
    with tempfile.TemporaryDirectory(prefix="pierce-weighted-audit-") as directory:
        source = Path(directory) / "Audit.lean"
        source.write_text("module\n" + imports + "\n" + AUDIT, encoding="utf-8")
        return subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT).returncode


if __name__ == "__main__":
    raise SystemExit(main())
