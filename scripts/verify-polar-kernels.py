#!/usr/bin/env python3
"""Replay the new polar proofs through the three bundled kernels.

Run after the normal build/check setup in README.md. This checks proof terms for
the listed additional endpoints, including the explicitly conditional bounds. It does
not compare their statements with an independent Challenge; that separate check
for the fifteen selected main statements is scripts/verify-comparator.sh.
"""
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENDPOINTS = [
    "orbit_polar_identity",
    "orbit_rankFive_polar_identity",
    "polarHomogeneousVector_eq_zero_iff",
    "polarBaseNodes_on_curve",
    "polar_good_axis_local_colength_four",
    "polar_centered_quadric_of_base",
    "polar_local_component_axis_colength_le_four",
    "branchSexticSpecialization_irreducible_rat",
    "branchInfinity_resultant",
    "branchGenericLocationSextic_irreducible",
    "branchGenericSignExtension_field_degree",
    "hypersurface_pattern_count",
    "retained_polar_linearJointGraph_degree_of_base_degree_le_four",
    "local_normalization_order_sum_le",
    "functionCommonBaseDegree_le_local_section",
    "exists_polar_full_minor_exceptional_polynomial",
    "retained_polar_base_degree_le_four",
    "branch_uniform_integral_root_bound",
    "branch_integer_specialization_witness",
    "orbit_infinity_residue_scaled_sign",
    "selected_hypersurface_pattern_count_slow",
    "polar_six_term_of_retained_degree",
    "branch_uniform_monic_hilbert_bound",
    "branch_multivariate_monic_hilbert_bound",
    "branch_vertex_good_scaled_box_count_slow",
    "branch_full_pattern_count",
    "selected_branch_pattern_count_slow",
    "polar_projection_six_term_estimates",
    "P_le_4317_14677_of_six_term_count",
    "P_le_polar_optimal_of_six_term_estimates",
]
# The same kernel primitives explicitly exported by Lake's Comparator.
PRIMITIVES = [
    "propext", "Quot.sound", "Classical.choice", "Nat.add", "Nat.sub", "Nat.mul",
    "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land",
    "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList",
    "Char.ofNat", "List", "eagerReduce", "Nat", "String", "String.mk", "Char",
    "optParam", "autoParam", "semiOutParam", "outParam",
]


def main() -> None:
    subprocess.run(["lake", "build", "PierceLengthBound"], cwd=ROOT, check=True)
    prefix = Path(subprocess.check_output(
        ["lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    roots = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
    roots += ["PierceLengthBound.FixedDividend." + name for name in ENDPOINTS]
    roots += PRIMITIVES
    with tempfile.TemporaryDirectory(prefix="pierce-polar-kernels-") as directory:
        export = Path(directory) / "proofs.ndjson"
        config = Path(directory) / "nanoda.json"
        with export.open("w", encoding="utf-8") as stream:
            subprocess.run(
                ["lake", "env", str(prefix / "bin/leanexport"), "PierceLengthBound", "--", *roots],
                cwd=ROOT, stdout=stream, check=True)
        config.write_text(json.dumps({
            "export_file_path": str(export),
            "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "unpermitted_axiom_hard_error": True,
            "nat_extension": True,
            "string_extension": True,
            "print_success_message": True,
        }, indent=2) + "\n", encoding="utf-8")
        commands = [
            ("con-ron", [str(prefix / "bin/con-ron"), str(export)]),
            ("NanoDa", [str(prefix / "bin/nanoda_bin"), str(config)]),
            ("Lean", [str(prefix / "bin/leanchecker"), "--from-export", str(export)]),
        ]
        for name, command in commands:
            print(f"Checking {len(ENDPOINTS)} polar endpoints with {name}...", flush=True)
            subprocess.run(command, cwd=ROOT, check=True)
        print("All three kernels accepted the polar endpoint proofs.")


if __name__ == "__main__":
    main()
