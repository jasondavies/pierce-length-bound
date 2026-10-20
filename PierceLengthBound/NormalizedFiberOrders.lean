/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ParameterFiberDegree
public import PierceLengthBound.NormalizedBranchValuation
public import Mathlib.RingTheory.RamificationInertia.Basic

/-! Residue-degree weighted branch orders in a finite parameter fiber. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped BigOperators

theorem normalizedBranchOrder_eq_multiplicity {R : Type*} [CommRing R]
    [IsDedekindDomain R] (p : IsDedekindDomain.HeightOneSpectrum R)
    (L : Type*) [Field L] [Algebra R L] [IsFractionRing R L]
    {x : R} (hx : x ≠ 0) :
    normalizedBranchOrder p L (algebraMap R L x) =
      ((multiplicity p.asIdeal (Ideal.span {x}) : ℤ) : WithTop ℤ) := by
  change discreteNegativeLog (p.valuation L (algebraMap R L x)) = _
  rw [p.valuation_of_algebraMap, p.intValuation_eq_exp_neg_multiplicity hx,
    discreteNegativeLog_exp, neg_neg]

/-- Over a rational base point, inertia degrees are the residue degrees over
the ground field. -/
theorem inertiaDeg_eq_ground_finrank {K T C : Type*} [Field K]
    [CommRing T] [Algebra K T] [CommRing C] [Algebra K C] [Algebra T C]
    [IsScalarTower K T C] (p : Ideal T) (q : Ideal C)
    [p.IsMaximal] [q.IsMaximal] [q.LiesOver p]
    (hp : Module.finrank K (T ⧸ p) = 1) :
    q.inertiaDeg T = Module.finrank K (C ⧸ q) := by
  let : Field (T ⧸ p) := Ideal.Quotient.field p
  let : Field (C ⧸ q) := Ideal.Quotient.field q
  rw [Ideal.inertiaDeg_eq_of_isMaximal p q,
    ← Module.finrank_mul_finrank K (T ⧸ p) (C ⧸ q), hp, one_mul]

/-- Every closed branch above a rational base point has positive residue degree. -/
theorem fiber_residue_degree_pos {K T C : Type*} [Field K]
    [CommRing T] [Algebra K T] [CommRing C] [Algebra K C] [Algebra T C]
    [IsScalarTower K T C] [Module.Finite T C]
    (p : Ideal T) (q : Ideal C) [p.IsMaximal] [q.IsPrime] [q.LiesOver p]
    (hp : Module.finrank K (T ⧸ p) = 1) :
    0 < Module.finrank K (C ⧸ q) := by
  let : Field (T ⧸ p) := Ideal.Quotient.field p
  let : Module.Finite K (T ⧸ p) := Module.finite_of_finrank_pos (hp.symm ▸ Nat.zero_lt_one)
  let : Module.Finite (T ⧸ p) (C ⧸ q) :=
    Module.Finite.of_restrictScalars_finite T (T ⧸ p) (C ⧸ q)
  let : Module.Finite K (C ⧸ q) := Module.Finite.trans (T ⧸ p) (C ⧸ q)
  exact Module.finrank_pos

/-- The sum of the multiplicities times residue degrees over a rational point
equals the rank of a finite flat Dedekind algebra. -/
theorem sum_fiber_multiplicity_residue_degree {K T C : Type*} [Field K]
    [CommRing T] [IsDomain T] [Algebra K T]
    [CommRing C] [IsDedekindDomain C] [Algebra K C] [Algebra T C]
    [IsScalarTower K T C] [Module.Finite T C] [Module.Flat T C]
    (p : Ideal T) [p.IsMaximal] [Fintype (p.primesOver C)]
    (hp : Module.finrank K (T ⧸ p) = 1)
    (hp0 : p.map (algebraMap T C) ≠ ⊥) :
    ∑ q : p.primesOver C,
      multiplicity q.1 (p.map (algebraMap T C)) * Module.finrank K (C ⧸ q.1) =
        Module.finrank T C := by
  rw [← Ideal.sum_ramification_inertia_eq_finrank p C]
  apply Finset.sum_congr rfl
  intro q _
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p q.1 hp0,
    inertiaDeg_eq_ground_finrank p q.1 hp]

/-- All branches of a polynomial parameter fiber, with their weighted total
multiplicity. The finite set contains exactly the height-one primes through
the fiber, including branches with nontrivial residue-field extensions. -/
theorem polynomial_parameter_branches {K T C : Type*} [Field K]
    [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [Algebra K T]
    [CommRing C] [IsDedekindDomain C] [Algebra K C] [Algebra T C]
    [IsScalarTower K T C] [FaithfulSMul T C] [Module.Finite T C]
    (e : Polynomial K ≃ₐ[K] T) :
    let w := algebraMap T C (e Polynomial.X)
    ∃ B : Finset (IsDedekindDomain.HeightOneSpectrum C),
      (∀ q, q ∈ B ↔ w ∈ q.asIdeal) ∧
      ∑ q ∈ B, multiplicity q.asIdeal (Ideal.span {w}) *
        Module.finrank K (C ⧸ q.asIdeal) = Module.finrank T C := by
  classical
  let w := algebraMap T C (e Polynomial.X)
  let p : Ideal T := Ideal.span {e Polynomial.X}
  have he : Prime (e Polynomial.X) := (MulEquiv.prime_iff e).mpr Polynomial.prime_X
  let : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible he.irreducible
  have hp : p ≠ ⊥ := by
    exact fun h => he.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have hmap : p.map (algebraMap T C) = Ideal.span {w} := by
    simp [p, w, Ideal.map_span]
  have hw : w ≠ 0 := by
    exact fun h => he.ne_zero ((FaithfulSMul.algebraMap_injective T C)
      (h.trans (map_zero (algebraMap T C)).symm))
  have hp0 : p.map (algebraMap T C) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    exact hw
  have hdim : Module.finrank K (T ⧸ p) = 1 := by
    simpa [p] using polynomial_parameter_fiber_finrank (S := T) e
  let f : p.primesOver C → IsDedekindDomain.HeightOneSpectrum C := fun q =>
    ⟨q.1, inferInstance, Ideal.ne_bot_of_mem_primesOver hp q.2⟩
  have hf : Function.Injective f := by
    intro q r h
    exact Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro q
    constructor
    · intro hq
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hq
      exact (Ideal.mem_of_liesOver r.1 p (e Polynomial.X)).mp (Ideal.subset_span rfl)
    · intro hq
      have hdiv : q.asIdeal ∣ p.map (algebraMap T C) := by
        rw [hmap, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
        exact hq
      let : q.asIdeal.LiesOver p := (Ideal.liesOver_iff_dvd_map q.isPrime.ne_top).mpr hdiv
      exact Finset.mem_image.mpr ⟨Ideal.primesOver.mk p q.asIdeal, Finset.mem_univ _,
        IsDedekindDomain.HeightOneSpectrum.ext rfl⟩
  · rw [Finset.sum_image (fun q _ r _ h => hf h)]
    simpa only [hmap] using sum_fiber_multiplicity_residue_degree p hdim hp0

/-- The same fiber formula expressed directly in the canonical normalized
orders, without choosing or assuming valuations. -/
theorem polynomial_parameter_branch_orders {K T C L : Type*} [Field K]
    [CommRing T] [IsDomain T] [IsPrincipalIdealRing T] [Algebra K T]
    [CommRing C] [IsDedekindDomain C] [Algebra K C] [Algebra T C]
    [IsScalarTower K T C] [FaithfulSMul T C] [Module.Finite T C]
    [Field L] [Algebra C L] [IsFractionRing C L]
    (e : Polynomial K ≃ₐ[K] T) :
    let w := algebraMap T C (e Polynomial.X)
    ∃ (B : Finset (IsDedekindDomain.HeightOneSpectrum C))
      (m : IsDedekindDomain.HeightOneSpectrum C → ℕ),
      (∀ q, q ∈ B ↔ w ∈ q.asIdeal) ∧
      (∀ q, normalizedBranchOrder q L (algebraMap C L w) = ((m q : ℤ) : WithTop ℤ)) ∧
      (∀ q, q ∈ B ↔ 0 < m q) ∧
      ∑ q ∈ B, m q * Module.finrank K (C ⧸ q.asIdeal) = Module.finrank T C := by
  let w := algebraMap T C (e Polynomial.X)
  have hw : w ≠ 0 := by
    simpa only [Function.comp_apply, map_zero] using
      ((FaithfulSMul.algebraMap_injective T C).comp e.injective).ne Polynomial.X_ne_zero
  obtain ⟨B, hB, hsum⟩ := polynomial_parameter_branches (C := C) e
  let m := fun q : IsDedekindDomain.HeightOneSpectrum C =>
    multiplicity q.asIdeal (Ideal.span {w})
  have hm : ∀ q, normalizedBranchOrder q L (algebraMap C L w) =
      ((m q : ℤ) : WithTop ℤ) := fun q => normalizedBranchOrder_eq_multiplicity q L hw
  refine ⟨B, m, hB, hm, ?_, hsum⟩
  intro q
  rw [hB q, ← normalizedBranchOrder_positive_iff q L w, hm q]
  norm_cast

end
end PierceLengthBound.FixedDividend
