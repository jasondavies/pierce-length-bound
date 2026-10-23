/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveArithmeticVertexBounds
public import PierceLengthBound.BranchSieveVertexMonic
public import PierceLengthBound.BranchSieveMultivariateHilbert
import Mathlib.Tactic
public import PierceLengthBound.BranchSieveDilation

/-! The branch sieve in scaled four-vertex boxes. Generic irreducibility comes
from the explicit monic degree-twelve family of `BranchSieveVertexMonic`.
Vertices with nonzero first coordinate are counted by the multivariate monic
specialization estimate (Theorem 10.4) applied to the dilated family; those
with first coordinate zero are counted directly. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

open Classical in
/-- For a common divisor `g` and radius `B`, both at most `2·10^16 a^7`, the
vertices `x ∈ [-B,B]^4` for which `g x` is not branch-good number at most
`R a · B^(7/2)`, with `R` slowly growing and independent of `g` and `B`. -/
theorem branch_vertex_good_scaled_box_count_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ a : ℕ, 0 < a → ∀ g B : ℕ,
      0 < g → g ≤ 2 * (10 ^ 16 * a ^ 7) → 0 < B → B ≤ 2 * (10 ^ 16 * a ^ 7) →
      (((ibox4 B).filter fun x : Fin 4 → ℤ =>
        ¬branchVertexGood a (fun i => (g : ℤ) * x i)).card : ℝ) ≤
        (R a : ℝ) * (B : ℝ) ^ (7 / 2 : ℝ) := by
  classical
  obtain ⟨d, C₀, hC₀, hfamily⟩ := branchMonicVertexFamilyAt_uniform_bounds
  obtain ⟨K, hK, hcount⟩ := branch_multivariate_monic_hilbert_bound 4 d
  let V : ℕ := 2 * 10 ^ 16
  obtain ⟨R₀, hR₀, hslack⟩ := branch_four_parameter_hilbert_slack K hK.le
    (C₀ * (2 * V) ^ d + 1) (8 * d) V 7
  refine ⟨fun a => R₀ a + 27, slowGrowth_add hR₀ (slowGrowth_const 27), ?_⟩
  intro a ha g B hg hga hB hBa
  obtain ⟨c, hc, hir⟩ := branchMonicVertexFamilyAt_exists_irreducible (a : ℤ) (by positivity)
  obtain ⟨hdegree, hcoeff, hheight⟩ := hfamily (a : ℤ) c hc
  let p := branchMonicVertexFamilyAt (a : ℤ) c
  let H := C₀ * (a + 1) ^ d
  have hpheight : ∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ) := by
    simpa only [Int.natAbs_natCast] using hheight
  obtain ⟨hgd, hgc, hgh⟩ := branchFamilyDilation_degree_height g hg p hdegree hcoeff hpheight
  let S := (ibox4 B).filter (fun x : Fin 4 → ℤ =>
    ¬branchVertexGood a (fun i => (g : ℤ) * x i))
  let S₁ := S.filter (fun x => x 0 ≠ 0)
  let S₀ := S.filter (fun x => x 0 = 0)
  have hbox (x : Fin 4 → ℤ) (hx : x ∈ S) (j : Fin 4) : |x j| ≤ (B : ℤ) := by
    have hxbox := (mem_filter.mp hx).1
    exact abs_le.mpr (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hxbox j))
  have hzero : (S₀.card : ℝ) ≤ 27 * (B : ℝ) ^ (7 / 2 : ℝ) :=
    branch_zero_axis_card_le B hB S₀ (fun x hx =>
      ⟨hbox x (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
  have hnonzero : (S₁.card : ℝ) ≤ K * branchHilbertSize 4 (H * g ^ d) B := by
    apply hcount (branchFamilyDilation g p)
      ((branchMonicVertexFamilyAt_monic (a : ℤ) c).map _)
      (branchFamilyDilation_irreducible g hg p hir) hgd hgc (H * g ^ d) B hgh hB S₁
    intro x hx
    obtain ⟨hxS, hxzero⟩ := mem_filter.mp hx
    refine ⟨hbox x hxS, ?_⟩
    intro hgood
    rw [branchFamilyDilation_eval] at hgood
    apply (mem_filter.mp hxS).2
    apply branchVertexGood_of_monic_irreducible a c _ ?_ hgood
    exact mul_ne_zero (by positivity : (g : ℤ) ≠ 0) hxzero
  have hpoly : H * g ^ d + 1 ≤ (C₀ * (2 * V) ^ d + 1) * a ^ (8 * d) :=
    branch_dilated_height_polynomial C₀ d V a g ha (by simpa only [V, mul_assoc] using hga)
  have hnonzero' : (S₁.card : ℝ) ≤ (R₀ a : ℝ) * (B : ℝ) ^ (7 / 2 : ℝ) :=
    hnonzero.trans (hslack a (H * g ^ d) B ha hB hpoly
      (by simpa only [V, mul_assoc] using hBa))
  have hsplit : S₁.card + S₀.card = S.card := by
    simpa only [not_ne_iff] using
      (Finset.card_filter_add_card_filter_not (s := S) (fun x => x 0 ≠ 0))
  change (S.card : ℝ) ≤ _
  rw [← hsplit, Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, add_mul]
  exact add_le_add hnonzero' hzero

end
end PierceLengthBound.FixedDividend
