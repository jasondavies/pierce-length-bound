/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizationBranchCover
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-! Pole multiplicities and the pole envelope of a finite family of functions. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The pole multiplicity of a function; zero functions have no poles. -/
def discretePoleOrder {L : Type*} [Field L] (ν : AddValuation L (WithTop ℤ)) (x : L) : ℕ :=
  (-(ν x).untopD 0).toNat

theorem discretePoleOrder_eq {L : Type*} [Field L] (ν : AddValuation L (WithTop ℤ))
    {x : L} {n : ℤ} (hx : ν x = (n : WithTop ℤ)) : discretePoleOrder ν x = (-n).toNat := by
  simp [discretePoleOrder, hx]

theorem discretePoleOrder_pos_iff {L : Type*} [Field L]
    (ν : AddValuation L (WithTop ℤ)) (x : L) : 0 < discretePoleOrder ν x ↔ ν x < 0 := by
  cases h : ν x with
  | top => simp [discretePoleOrder, h]
  | coe n =>
      rw [discretePoleOrder_eq ν h]
      change 0 < (-n).toNat ↔ (n : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
      rw [WithTop.coe_lt_coe]
      omega

theorem discretePoleOrder_le_iff {L : Type*} [Field L]
    (ν : AddValuation L (WithTop ℤ)) (x : L) (n : ℕ) :
    discretePoleOrder ν x ≤ n ↔ ((-(n : ℤ)) : WithTop ℤ) ≤ ν x := by
  cases h : ν x with
  | top => simp [discretePoleOrder, h]
  | coe z =>
      rw [discretePoleOrder_eq ν h]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_le_coe]
      omega

/-- A positive pole multiplicity specifies the exact negative order. -/
theorem discretePoleOrder_eq_iff_of_pos {L : Type*} [Field L]
    (ν : AddValuation L (WithTop ℤ)) (x : L) {m : ℕ} (hm : 0 < m) :
    discretePoleOrder ν x = m ↔ ν x = ((-(m : ℤ)) : WithTop ℤ) := by
  cases h : ν x with
  | top =>
      constructor
      · intro he
        have hz : 0 = m := by simpa [discretePoleOrder, h] using he
        omega
      · intro he
        rw [← WithTop.LinearOrderedAddCommGroup.coe_neg] at he
        exact False.elim (WithTop.coe_ne_top he.symm)
  | coe z =>
      rw [discretePoleOrder_eq ν h]
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_inj]
      omega

/-- The largest pole among the coordinates at a fixed branch. -/
def branchPoleEnvelope {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (W : ι → L) : ℕ :=
  Finset.univ.sup (fun j => discretePoleOrder ν (W j))

theorem pole_order_le_envelope {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (W : ι → L) (j : ι) :
    discretePoleOrder ν (W j) ≤ branchPoleEnvelope ν W :=
  Finset.le_sup (f := fun k => discretePoleOrder ν (W k)) (Finset.mem_univ j)

theorem branchPoleEnvelope_pos_iff {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (W : ι → L) :
    0 < branchPoleEnvelope ν W ↔ ∃ j, 0 < discretePoleOrder ν (W j) := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hh : branchPoleEnvelope ν W ≤ 0 :=
      Finset.sup_le (fun j _ => hn j)
    omega
  · rintro ⟨j, hj⟩
    exact hj.trans_le (pole_order_le_envelope ν W j)

theorem branchPoleEnvelope_attained {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (W : ι → L) (hpos : 0 < branchPoleEnvelope ν W) :
    ∃ j, ν (W j) = ((-(branchPoleEnvelope ν W : ℤ)) : WithTop ℤ) := by
  classical
  obtain ⟨j, _⟩ := (branchPoleEnvelope_pos_iff ν W).mp hpos
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨j, Finset.mem_univ j⟩
    (fun k => discretePoleOrder ν (W k))
  exact ⟨k, (discretePoleOrder_eq_iff_of_pos ν (W k) hpos).mp hk.symm⟩

/-- Constant coefficients regular at a branch cannot produce a pole larger
than the largest pole of the coordinates. -/
theorem combination_pole_order_le_envelope {K L ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype ι] (ν : AddValuation L (WithTop ℤ))
    (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c)) (W : ι → L) (c : ι → K) :
    discretePoleOrder ν (∑ j, algebraMap K L (c j) * W j) ≤ branchPoleEnvelope ν W := by
  rw [discretePoleOrder_le_iff]
  apply ν.map_le_sum
  intro j _
  rw [ν.map_mul]
  have hj := (discretePoleOrder_le_iff ν (W j) (branchPoleEnvelope ν W)).mp
    (pole_order_le_envelope ν W j)
  simpa only [zero_add] using add_le_add (hK (c j)) hj

/-- A rational function on a Dedekind model has only finitely many poles. -/
theorem normalized_branch_poles_finite {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (x : L) :
    {p : IsDedekindDomain.HeightOneSpectrum R |
      0 < discretePoleOrder (normalizedBranchOrder p L) x}.Finite := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : (Ideal.span {b} : Ideal R) ≠ 0 := fun h => hb0 (Ideal.span_singleton_eq_bot.mp h)
  apply (Ideal.finite_factors hI).subset
  intro p hp
  change 0 < discretePoleOrder (normalizedBranchOrder p L) x at hp
  change p.asIdeal ∣ Ideal.span {b}
  rw [discretePoleOrder_pos_iff] at hp
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hmem
  have hnonneg := normalizedBranchOrder_nonnegative p L b
  have hnpos := (normalizedBranchOrder_positive_iff p L b).not.mpr hmem
  have hzero : normalizedBranchOrder p L (algebraMap R L b) = 0 :=
    le_antisymm (le_of_not_gt hnpos) hnonneg
  rw [← hab, AddValuation.map_div, hzero, sub_zero] at hp
  exact (not_lt_of_ge (normalizedBranchOrder_nonnegative p L a)) hp

theorem branch_pole_envelope_finite {R L ι : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] [Fintype ι] (W : ι → L) :
    {p : IsDedekindDomain.HeightOneSpectrum R |
      0 < branchPoleEnvelope (normalizedBranchOrder p L) W}.Finite := by
  apply (Set.finite_iUnion (fun j => normalized_branch_poles_finite (R := R) (W j))).subset
  intro p hp
  obtain ⟨j, hj⟩ := (branchPoleEnvelope_pos_iff (normalizedBranchOrder p L) W).mp hp
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

/-- The finite support of the coordinate pole envelope. -/
def poleEnvelopeBranches (R : Type*) {L ι : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] [Fintype ι] (W : ι → L) :
    Finset (IsDedekindDomain.HeightOneSpectrum R) :=
  (branch_pole_envelope_finite (R := R) W).toFinset

@[simp] theorem mem_poleEnvelopeBranches {R L ι : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] [Fintype ι] (W : ι → L)
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    p ∈ poleEnvelopeBranches R W ↔ 0 < branchPoleEnvelope (normalizedBranchOrder p L) W :=
  Set.Finite.mem_toFinset _

/-- The pole envelope degree, with residue-field degrees as weights. -/
def poleEnvelopeDegree (R : Type*) {L ι : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra ℚ R] [Field L] [Algebra R L] [IsFractionRing R L] [Fintype ι] (W : ι → L) : ℕ :=
  ∑ p ∈ poleEnvelopeBranches R W,
    branchPoleEnvelope (normalizedBranchOrder p L) W * Module.finrank ℚ (R ⧸ p.asIdeal)

end
end PierceLengthBound.FixedDividend
