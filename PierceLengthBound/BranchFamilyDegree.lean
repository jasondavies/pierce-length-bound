/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchResidueComparison

/-! Weighted zero and pole counts for a finite family of branches `p k` on possibly different
Dedekind models `R k` of one function field `L`. If the normalized orders of the branches are
pairwise distinct and `x` has a zero (or pole) of order `m k` at each, then
`∑ₖ m k · [R k / p k : ℚ] ≤ [L : ℚ(x)]`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField

/-- Branches on different Dedekind models with pairwise distinct normalized orders, at which
`x` has zero orders `m k > 0`, satisfy `∑ₖ m k · [R k / p k : ℚ] ≤ [L : ℚ(x)]`. -/
theorem branch_family_zero_degree_le {κ L : Type*} [Fintype κ]
    [Field L] [Algebra ℚ L] (R : κ → Type*)
    [∀ k, CommRing (R k)] [∀ k, IsDedekindDomain (R k)] [∀ k, Algebra ℚ (R k)]
    [∀ k, Algebra (R k) L] [∀ k, IsScalarTower ℚ (R k) L] [∀ k, IsFractionRing (R k) L]
    (p : ∀ k, IsDedekindDomain.HeightOneSpectrum (R k))
    (hinj : Function.Injective (fun k => normalizedBranchOrder (p k) L))
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (m : κ → ℕ) (hm : ∀ k, 0 < m k)
    (horder : ∀ k, normalizedBranchOrder (p k) L x = ((m k : ℤ) : WithTop ℤ)) :
    ∑ k, m k * Module.finrank ℚ (R k ⧸ (p k).asIdeal) ≤ Module.finrank ℚ⟮x⟯ L := by
  classical
  let C := functionParameterNormalization x
  obtain ⟨B, hB, hsum⟩ := function_parameter_fiber_degree x hx
  have ht (k : κ) : ∃ q : IsDedekindDomain.HeightOneSpectrum C,
      functionParameterElement x ∈ q.asIdeal ∧
      functionParameterBranchOrder x hx q = normalizedBranchOrder (p k) L ∧
      Module.finrank ℚ (C ⧸ q.asIdeal) = Module.finrank ℚ (R k ⧸ (p k).asIdeal) := by
    apply function_parameter_branch_transport_with_degree (p k) x hx
    rw [horder k]
    exact_mod_cast hm k
  choose f hfmem hford hfdegree using ht
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    change normalizedBranchOrder (p i) L = normalizedBranchOrder (p j) L
    rw [← hford i, ← hford j, hij]
  let weight := fun q : IsDedekindDomain.HeightOneSpectrum C =>
    multiplicity q.asIdeal (Ideal.span {functionParameterElement x}) *
      Module.finrank ℚ (C ⧸ q.asIdeal)
  have hweight (k : κ) : weight (f k) = m k * Module.finrank ℚ (R k ⧸ (p k).asIdeal) := by
    have he := functionParameterBranchOrder_parameter x hx (f k)
    rw [hford k, horder k] at he
    have hmult : multiplicity (f k).asIdeal (Ideal.span {functionParameterElement x}) = m k := by
      exact_mod_cast he.symm
    exact congrArg₂ (· * ·) hmult (hfdegree k)
  have hsub : Finset.univ.image f ⊆ B := by
    intro q hq
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hB _).mpr (hfmem k)
  calc
    ∑ k, m k * Module.finrank ℚ (R k ⧸ (p k).asIdeal) = ∑ k, weight (f k) :=
      Finset.sum_congr rfl (fun k _ => (hweight k).symm)
    _ = ∑ q ∈ Finset.univ.image f, weight q :=
      (Finset.sum_image (fun i _ j _ h => hf h)).symm
    _ ≤ ∑ q ∈ B, weight q := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = Module.finrank ℚ⟮x⟯ L := hsum

/-- The pole version of `branch_family_zero_degree_le`: pole orders `m k > 0` of `x` at
branches with pairwise distinct normalized orders satisfy
`∑ₖ m k · [R k / p k : ℚ] ≤ [L : ℚ(x)]`. -/
theorem branch_family_pole_degree_le {κ L : Type*} [Fintype κ]
    [Field L] [Algebra ℚ L] (R : κ → Type*)
    [∀ k, CommRing (R k)] [∀ k, IsDedekindDomain (R k)] [∀ k, Algebra ℚ (R k)]
    [∀ k, Algebra (R k) L] [∀ k, IsScalarTower ℚ (R k) L] [∀ k, IsFractionRing (R k) L]
    (p : ∀ k, IsDedekindDomain.HeightOneSpectrum (R k))
    (hinj : Function.Injective (fun k => normalizedBranchOrder (p k) L))
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (m : κ → ℕ) (hm : ∀ k, 0 < m k)
    (horder : ∀ k, normalizedBranchOrder (p k) L x = ((-(m k : ℤ)) : WithTop ℤ)) :
    ∑ k, m k * Module.finrank ℚ (R k ⧸ (p k).asIdeal) ≤ Module.finrank ℚ⟮x⟯ L := by
  have hinv : Transcendental ℚ x⁻¹ := fun h => hx (by simpa using h.inv)
  have hfield := intermediateField_adjoin_inv (K := ℚ) x
  let : FiniteDimensional ℚ⟮x⁻¹⟯ L := hfield.symm ▸ inferInstance
  have hzero (k) : normalizedBranchOrder (p k) L x⁻¹ = ((m k : ℤ) : WithTop ℤ) := by
    rw [(normalizedBranchOrder (p k) L).map_inv, horder k, neg_neg]
  have hh := branch_family_zero_degree_le R p hinj x⁻¹ hinv m hm hzero
  rwa [hfield] at hh

end
end PierceLengthBound.FixedDividend
