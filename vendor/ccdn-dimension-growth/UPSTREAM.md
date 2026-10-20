# Verified affine curve counting snapshot

This is a source-hashed snapshot of the author's separate `ccdn-dimension-growth`
development, captured after the full `AffineCurveCounting.affineCurveBound`
theorem passed its build and axiom audit. It was captured from uncommitted proof
work; its base commit alone does **not** identify this snapshot. The Pierce
commit containing this directory archives the complete imported snapshot.

The exact source inventory and SHA-256 hashes are in `upstream.json`.
Source worktree inventory digest: `07b7c9b92ff70e334a56622dde89e730a870a37e87369d4b0d949c377ddcc37c`.
Every mathematical source file is copied unchanged. The only adapted source
configuration is `lakefile.toml`: it uses the parent's Mathlib/toolchain and
omits the standalone `Axioms` library, whose name would conflict with the parent.
The parent axiom audit covers these imported modules and their vendored inputs.

The related canonical CCDN checkpoint is commit
`cecde215a9349ce066c1aa7e1bb77acdd718064b`. It includes later dimension-growth
development and is **not** the exact source of this snapshot: seven shared
mathematical dependency files have since been extended, refactored or documented.
The affine counting theorem and its public curve/plane interfaces are unchanged.
The inventory above, rather than that later commit, identifies the proofs
imported by Pierce. The remaining full-paper CCDN formalisation is separate.

The snapshot includes the upstream Apache-2.0 license and the Bombieri–Vaaler
and Mertens provenance records and licenses. Run builds from the parent project;
the upstream README's standalone build commands describe the source repository.

Verification in the source checkout: 9262 Lake jobs, 1140 project and 555
vendored declarations; only `propext`, `Classical.choice`, and `Quot.sound`.
This is Lean verification, not independent human review. The counting theorem
is complete; the application-specific Pierce geometry remains separate.
