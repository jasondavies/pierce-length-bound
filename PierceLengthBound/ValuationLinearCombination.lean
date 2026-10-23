/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchPoleEnvelope
public import Mathlib.Algebra.Module.Submodule.Union

/-! A single constant linear combination simultaneously attains the least
coordinate order at finitely many branches. Cancellation is a proper linear
condition over the infinite constant field. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The linear map `c ↦ ∑ⱼ cⱼ Wⱼ`. -/
def coordinateCombinationMap {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype ι] (W : ι → L) : (ι → K) →ₗ[K] L where
  toFun c := ∑ j, algebraMap K L (c j) * W j
  map_add' c d := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c d := by
    simp [Algebra.smul_def, map_mul, Finset.mul_sum, mul_assoc]

@[simp] theorem coordinateCombinationMap_single {K L ι : Type*}
    [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]
    (W : ι → L) (j : ι) : coordinateCombinationMap W (Pi.single j (1 : K)) = W j := by
  simp [coordinateCombinationMap, Pi.single_apply]

/-- The `K`-subspace of elements of order greater than `n`. -/
def orderAboveSubmodule {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ν : AddValuation L (WithTop ℤ)) (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c))
    (n : ℤ) : Submodule K L where
  carrier := {x | (n : WithTop ℤ) < ν x}
  zero_mem' := by simp
  add_mem' hx hy := (lt_min hx hy).trans_le (ν.map_add _ _)
  smul_mem' c x hx := by
    change (n : WithTop ℤ) < ν (c • x)
    rw [Algebra.smul_def, ν.map_mul]
    exact hx.trans_le (le_add_of_nonneg_left (hK c))

/-- Over an infinite field `K` of constants, suppose that at each of finitely many orders
`ν k` every `W j` has order at least `n k`, and some `W j` has order exactly `n k`. Then a single
combination `∑ cⱼ Wⱼ` has order exactly `n k` at every `k`. The residue fields may be
extensions of `K`. -/
theorem exists_combination_exact_orders {K L ι κ : Type*}
    [Field K] [Infinite K] [Field L] [Algebra K L] [Fintype ι] [Finite κ]
    (ν : κ → AddValuation L (WithTop ℤ))
    (hK : ∀ k c, 0 ≤ ν k (algebraMap K L c))
    (W : ι → L) (n : κ → ℤ)
    (hlower : ∀ k j, (n k : WithTop ℤ) ≤ ν k (W j))
    (hexact : ∀ k, ∃ j, ν k (W j) = (n k : WithTop ℤ)) :
    ∃ c : ι → K, ∀ k, ν k (∑ j, algebraMap K L (c j) * W j) = (n k : WithTop ℤ) := by
  classical
  let V (k : κ) := (orderAboveSubmodule (ν k) (hK k) (n k)).comap (coordinateCombinationMap W)
  have hV (k : κ) : V k ≠ ⊤ := by
    obtain ⟨j, hj⟩ := hexact k
    intro h
    have hm : Pi.single j 1 ∈ V k := by rw [h]; trivial
    change (n k : WithTop ℤ) < ν k (coordinateCombinationMap W (Pi.single j 1)) at hm
    rw [coordinateCombinationMap_single, hj] at hm
    exact lt_irrefl _ hm
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  refine ⟨c, fun k => le_antisymm (le_of_not_gt (hc k)) ?_⟩
  apply (ν k).map_le_sum
  intro j _
  rw [(ν k).map_mul]
  simpa only [zero_add] using add_le_add (hK k (c j)) (hlower k j)

/-- At finitely many branches with poles, one combination realizes every
coordinate pole envelope simultaneously. -/
theorem exists_combination_attaining_pole_envelopes {K L ι κ : Type*}
    [Field K] [Infinite K] [Field L] [Algebra K L] [Fintype ι] [Finite κ]
    (ν : κ → AddValuation L (WithTop ℤ))
    (hK : ∀ k c, 0 ≤ ν k (algebraMap K L c)) (W : ι → L)
    (hpos : ∀ k, 0 < branchPoleEnvelope (ν k) W) :
    ∃ c : ι → K, ∀ k,
      ν k (∑ j, algebraMap K L (c j) * W j) =
        ((-(branchPoleEnvelope (ν k) W : ℤ)) : WithTop ℤ) := by
  apply exists_combination_exact_orders ν hK W (fun k => -(branchPoleEnvelope (ν k) W : ℤ))
  · intro k j
    exact (discretePoleOrder_le_iff (ν k) (W j) _).mp (pole_order_le_envelope (ν k) W j)
  · exact fun k => branchPoleEnvelope_attained (ν k) W (hpos k)

end
end PierceLengthBound.FixedDividend
