/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.GraphFunctionField
public import PierceLengthBound.BranchFamilyDegree
public import PierceLengthBound.BranchModelSum
public import PierceLengthBound.ValuationLinearCombination
public import PierceLengthBound.NormalizationPointBranch

/-! The graph Hilbert degree bounds the residue-degree weighted coordinate
pole envelope over any finite collection of distinct normalized branches,
including branches represented on different affine charts. A generic rational combination of
the graph coordinates attains every envelope, and its field degree is at most the Hilbert
degree. This gives the lower bounds for the graph degrees in Lemmas 8.13 and 9.9
(`LinearJointGraph`). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField
universe u

/-- For finitely many branches, on Dedekind models `R k`, with pairwise distinct normalized
orders and positive pole envelopes of the graph coordinates, the envelopes weighted by residue
degrees sum to at most the graph Hilbert degree `d`. -/
theorem jointGraph_pole_envelope_degree_le_hilbert {σ τ κ F : Type*}
    [Field F] [Algebra ℚ F] [Fintype σ] [Fintype τ] [Fintype κ]
    (I : Ideal (MvPolynomial σ ℚ)) [I.IsPrime]
    (P : τ → MvPolynomial σ ℚ) (D : MvPolynomial σ ℚ)
    (ι : (MvPolynomial σ ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial σ ℚ ⧸ I, z = ι x / ι y)
    {d : ℕ} (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace (jointGraphIdeal I P D) n) : ℤ) =
        (d : ℤ) * n + b)
    (R : κ → Type*)
    [∀ k, CommRing (R k)] [∀ k, IsDedekindDomain (R k)] [∀ k, Algebra ℚ (R k)]
    [∀ k, Algebra (R k) F] [∀ k, IsScalarTower ℚ (R k) F] [∀ k, IsFractionRing (R k) F]
    (p : ∀ k, IsDedekindDomain.HeightOneSpectrum (R k))
    (hinj : Function.Injective (fun k => normalizedBranchOrder (p k) F))
    (hpos : ∀ k, 0 < branchPoleEnvelope (normalizedBranchOrder (p k) F)
      (jointGraphFieldCoordinates I P D ι)) :
    ∑ k, branchPoleEnvelope (normalizedBranchOrder (p k) F)
      (jointGraphFieldCoordinates I P D ι) * Module.finrank ℚ (R k ⧸ (p k).asIdeal) ≤ d := by
  classical
  cases isEmpty_or_nonempty κ with
  | inl h => simp
  | inr h =>
    let ν := fun k => normalizedBranchOrder (p k) F
    let W := jointGraphFieldCoordinates I P D ι
    have hQ (k : κ) (c : ℚ) : 0 ≤ ν k (algebraMap ℚ F c) := by
      rw [IsScalarTower.algebraMap_apply ℚ (R k) F]
      exact normalizedBranchOrder_nonnegative (p k) F _
    obtain ⟨c, hc⟩ := exists_combination_attaining_pole_envelopes ν hQ W hpos
    let x := ∑ j, algebraMap ℚ F (c j) * W j
    have hx : Transcendental ℚ x := by
      let k : κ := Classical.choice h
      apply transcendental_of_negative_order (ν k) (hQ k)
      rw [hc k, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
      exact_mod_cast (show -(branchPoleEnvelope (ν k) W : ℤ) < 0 by
        exact neg_neg_of_pos (by exact_mod_cast hpos k))
    obtain ⟨hfinite, hupper⟩ :=
      jointGraph_linear_function_degree_le I P D ι hι hD hfrac hdegree c hx
    let : FiniteDimensional ℚ⟮x⟯ F := hfinite
    exact (branch_family_pole_degree_le R p hinj x hx
      (fun k => branchPoleEnvelope (ν k) W) hpos hc).trans hupper

/-- If at each branch `k` some graph coordinate has pole order at least `m k > 0`, then
`∑ₖ m k · [R k / p k : ℚ] ≤ d`. -/
theorem jointGraph_branch_poles_degree_le {σ τ κ F : Type*}
    [Field F] [Algebra ℚ F] [Finite σ] [Finite τ] [Fintype κ]
    (I : Ideal (MvPolynomial σ ℚ)) [I.IsPrime]
    (P : τ → MvPolynomial σ ℚ) (D : MvPolynomial σ ℚ)
    (ι : (MvPolynomial σ ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial σ ℚ ⧸ I, z = ι x / ι y)
    {d : ℕ} (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace (jointGraphIdeal I P D) n) : ℤ) =
        (d : ℤ) * n + b)
    (R : κ → Type*)
    [∀ k, CommRing (R k)] [∀ k, IsDedekindDomain (R k)] [∀ k, Algebra ℚ (R k)]
    [∀ k, Algebra (R k) F] [∀ k, IsScalarTower ℚ (R k) F] [∀ k, IsFractionRing (R k) F]
    (p : ∀ k, IsDedekindDomain.HeightOneSpectrum (R k))
    (hinj : Function.Injective (fun k => normalizedBranchOrder (p k) F))
    (m : κ → ℕ) (hm : ∀ k, 0 < m k)
    (hpole : ∀ k, ∃ j, m k ≤ discretePoleOrder (normalizedBranchOrder (p k) F)
      (jointGraphFieldCoordinates I P D ι j)) :
    ∑ k, m k * Module.finrank ℚ (R k ⧸ (p k).asIdeal) ≤ d := by
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype τ := Fintype.ofFinite τ
  have hle (k) : m k ≤ branchPoleEnvelope (normalizedBranchOrder (p k) F)
      (jointGraphFieldCoordinates I P D ι) := by
    obtain ⟨j, hj⟩ := hpole k
    exact hj.trans (pole_order_le_envelope _ _ j)
  apply le_trans _ (jointGraph_pole_envelope_degree_le_hilbert I P D ι hι hD hfrac hdegree R p
    hinj (fun k => (hm k).trans_le (hle k)))
  exact Finset.sum_le_sum (fun k _ => Nat.mul_le_mul_right _ (hle k))

/-- The same bound for a branch set `B` on a model `R` and a branch set `E` on a model `S`,
when no branch of `B` has the same normalized order as a branch of `E`. -/
theorem jointGraph_two_model_poles_degree_le {σ τ F : Type*} {R S : Type u}
    [Field F] [Algebra ℚ F] [Finite σ] [Finite τ]
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [Algebra R F] [IsScalarTower ℚ R F] [IsFractionRing R F]
    [CommRing S] [IsDedekindDomain S] [Algebra ℚ S]
    [Algebra S F] [IsScalarTower ℚ S F] [IsFractionRing S F]
    (I : Ideal (MvPolynomial σ ℚ)) [I.IsPrime]
    (P : τ → MvPolynomial σ ℚ) (D : MvPolynomial σ ℚ)
    (ι : (MvPolynomial σ ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    (hD : ι (Ideal.Quotient.mk I D) ≠ 0)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial σ ℚ ⧸ I, z = ι x / ι y)
    {d : ℕ} (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace (jointGraphIdeal I P D) n) : ℤ) =
        (d : ℤ) * n + b)
    (B : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (E : Finset (IsDedekindDomain.HeightOneSpectrum S))
    (m : IsDedekindDomain.HeightOneSpectrum R → ℕ)
    (n : IsDedekindDomain.HeightOneSpectrum S → ℕ)
    (hm : ∀ p ∈ B, 0 < m p) (hn : ∀ q ∈ E, 0 < n q)
    (hdisjoint : ∀ p ∈ B, ∀ q ∈ E, normalizedBranchOrder p F ≠ normalizedBranchOrder q F)
    (hB : ∀ p ∈ B, ∃ j, m p ≤ discretePoleOrder (normalizedBranchOrder p F)
      (jointGraphFieldCoordinates I P D ι j))
    (hE : ∀ q ∈ E, ∃ j, n q ≤ discretePoleOrder (normalizedBranchOrder q F)
      (jointGraphFieldCoordinates I P D ι j)) :
    (∑ p ∈ B, m p * Module.finrank ℚ (R ⧸ p.asIdeal)) +
      (∑ q ∈ E, n q * Module.finrank ℚ (S ⧸ q.asIdeal)) ≤ d := by
  classical
  let A : B ⊕ E → Type _ := branchModelSum R S
  let : ∀ k, CommRing (A k) := fun k => inferInstanceAs (CommRing (branchModelSum R S k))
  let : ∀ k, IsDedekindDomain (A k) := fun k =>
    inferInstanceAs (IsDedekindDomain (branchModelSum R S k))
  let : ∀ k, Algebra ℚ (A k) := fun k => inferInstanceAs (Algebra ℚ (branchModelSum R S k))
  let : ∀ k, Algebra (A k) F := fun k => inferInstanceAs (Algebra (branchModelSum R S k) F)
  let : ∀ k, IsScalarTower ℚ (A k) F := fun k =>
    inferInstanceAs (IsScalarTower ℚ (branchModelSum R S k) F)
  let : ∀ k, IsFractionRing (A k) F := fun k =>
    inferInstanceAs (IsFractionRing (branchModelSum R S k) F)
  let p : ∀ k, IsDedekindDomain.HeightOneSpectrum (A k) :=
    fun k => match k with | .inl p => p.1 | .inr q => q.1
  let v : B ⊕ E → ℕ := Sum.elim (fun p => m p.1) (fun q => n q.1)
  have hinj : Function.Injective (fun k => normalizedBranchOrder (p k) F) := by
    intro k l he
    cases k with
    | inl k => cases l with
      | inl l =>
        exact congrArg Sum.inl
          (Subtype.ext (normalizedBranchOrder_injective (R := R) (L := F) he))
      | inr l => exact False.elim (hdisjoint k.1 k.2 l.1 l.2 he)
    | inr k => cases l with
      | inl l => exact False.elim (hdisjoint l.1 l.2 k.1 k.2 he.symm)
      | inr l =>
        exact congrArg Sum.inr
          (Subtype.ext (normalizedBranchOrder_injective (R := S) (L := F) he))
  have hv (k) : 0 < v k := by
    cases k with
    | inl k => exact hm k.1 k.2
    | inr k => exact hn k.1 k.2
  have hpole (k) : ∃ j, v k ≤ discretePoleOrder (normalizedBranchOrder (p k) F)
      (jointGraphFieldCoordinates I P D ι j) := by
    cases k with
    | inl k => exact hB k.1 k.2
    | inr k => exact hE k.1 k.2
  have hh := jointGraph_branch_poles_degree_le I P D ι hι hD hfrac hdegree A p hinj v hv hpole
  simp only [Fintype.sum_sum_type, A, p, v, Sum.elim_inl, Sum.elim_inr] at hh
  change (∑ p : B, m p.1 * Module.finrank ℚ (R ⧸ p.1.asIdeal)) +
    (∑ q : E, n q.1 * Module.finrank ℚ (S ⧸ q.1.asIdeal)) ≤ d at hh
  rw [B.sum_coe_sort (fun p => m p * Module.finrank ℚ (R ⧸ p.asIdeal)),
    E.sum_coe_sort (fun q => n q * Module.finrank ℚ (S ⧸ q.asIdeal))] at hh
  exact hh

end
end PierceLengthBound.FixedDividend
