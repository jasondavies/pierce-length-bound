/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchResidueComparison

/-! Weighted zero orders on any Dedekind model are bounded by the degree of
the function as a parameter. Branch transport preserves the weights and is
injective, so no zero is counted twice. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField BigOperators

theorem branch_zero_degree_le {R L : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (B : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (m : IsDedekindDomain.HeightOneSpectrum R → ℕ)
    (hm : ∀ p ∈ B, 0 < m p)
    (horder : ∀ p ∈ B, normalizedBranchOrder p L x = ((m p : ℤ) : WithTop ℤ)) :
    ∑ p ∈ B, m p * Module.finrank ℚ (R ⧸ p.asIdeal) ≤ Module.finrank ℚ⟮x⟯ L := by
  classical
  let C := functionParameterNormalization x
  obtain ⟨Q, hQ, hsumQ⟩ := function_parameter_fiber_degree x hx
  have ht (p : B) : ∃ q : IsDedekindDomain.HeightOneSpectrum C,
      functionParameterElement x ∈ q.asIdeal ∧
      functionParameterBranchOrder x hx q = normalizedBranchOrder p.1 L ∧
      Module.finrank ℚ (C ⧸ q.asIdeal) = Module.finrank ℚ (R ⧸ p.1.asIdeal) := by
    apply function_parameter_branch_transport_with_degree p.1 x hx
    rw [horder p.1 p.2]
    exact_mod_cast hm p.1 p.2
  choose f hfmem hford hfdegree using ht
  have hf : Function.Injective f := by
    intro p r h
    apply Subtype.ext
    apply normalizedBranchOrder_injective (L := L)
    change normalizedBranchOrder p.1 L = normalizedBranchOrder r.1 L
    rw [← hford p, ← hford r, h]
  let W := fun q : IsDedekindDomain.HeightOneSpectrum C =>
    multiplicity q.asIdeal (Ideal.span {functionParameterElement x}) *
      Module.finrank ℚ (C ⧸ q.asIdeal)
  have hweight (p : B) : W (f p) = m p.1 * Module.finrank ℚ (R ⧸ p.1.asIdeal) := by
    have hmult : multiplicity (f p).asIdeal (Ideal.span {functionParameterElement x}) = m p.1 := by
      have hh := functionParameterBranchOrder_parameter x hx (f p)
      rw [hford p, horder p.1 p.2] at hh
      exact_mod_cast hh.symm
    exact congrArg₂ (· * ·) hmult (hfdegree p)
  have hsub : Finset.univ.image f ⊆ Q := by
    intro q hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hQ _).mpr (hfmem p)
  calc
    ∑ p ∈ B, m p * Module.finrank ℚ (R ⧸ p.asIdeal) =
        ∑ p : B, m p.1 * Module.finrank ℚ (R ⧸ p.1.asIdeal) :=
      (B.sum_coe_sort _).symm
    _ = ∑ p : B, W (f p) := Finset.sum_congr rfl (fun p _ => (hweight p).symm)
    _ = ∑ q ∈ Finset.univ.image f, W q :=
      (Finset.sum_image (fun p _ r _ h => hf h)).symm
    _ ≤ ∑ q ∈ Q, W q := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = Module.finrank ℚ⟮x⟯ L := hsumQ

/-- Lower bounds for positive zero orders suffice for the weighted degree
bound; cancellation may increase a zero order without invalidating the bound. -/
theorem branch_zero_degree_lower_bounds {R L : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (B : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (m : IsDedekindDomain.HeightOneSpectrum R → ℕ)
    (hm : ∀ p ∈ B, 0 < m p)
    (horder : ∀ p ∈ B, ((m p : ℤ) : WithTop ℤ) ≤ normalizedBranchOrder p L x) :
    ∑ p ∈ B, m p * Module.finrank ℚ (R ⧸ p.asIdeal) ≤ Module.finrank ℚ⟮x⟯ L := by
  classical
  have hk (p : IsDedekindDomain.HeightOneSpectrum R) :
      ∃ k : ℤ, (k : WithTop ℤ) = normalizedBranchOrder p L x :=
    WithTop.ne_top_iff_exists.mp ((normalizedBranchOrder p L).ne_top_iff.mpr hx.ne_zero)
  choose k hk using hk
  have hmk (p) (hp : p ∈ B) : (m p : ℤ) ≤ k p := by
    have hh := horder p hp
    rw [← hk p] at hh
    exact_mod_cast hh
  have hkpos (p) (hp : p ∈ B) : 0 < k p := by
    have := hmk p hp
    have := hm p hp
    omega
  have hactual := branch_zero_degree_le x hx B (fun p => (k p).toNat)
    (fun p hp => by have := hkpos p hp; omega)
    (fun p hp => by
      have he : ((k p).toNat : ℤ) = k p := by have := hkpos p hp; omega
      rw [he, hk p])
  apply le_trans _ hactual
  apply Finset.sum_le_sum
  intro p hp
  apply Nat.mul_le_mul_right
  have := hmk p hp
  omega

/-- One additional zero on a branch outside B contributes at least one more
degree. This is the integer gain needed by the joint-lift argument. -/
theorem branch_zero_degree_with_extra {R L : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (B : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (m : IsDedekindDomain.HeightOneSpectrum R → ℕ)
    (hm : ∀ p ∈ B, 0 < m p)
    (horder : ∀ p ∈ B, ((m p : ℤ) : WithTop ℤ) ≤ normalizedBranchOrder p L x)
    (p : IsDedekindDomain.HeightOneSpectrum R) (hp : p ∉ B)
    (hpos : 0 < normalizedBranchOrder p L x) :
    (∑ q ∈ B, m q * Module.finrank ℚ (R ⧸ q.asIdeal)) + 1 ≤
      Module.finrank ℚ⟮x⟯ L := by
  classical
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
    ((normalizedBranchOrder p L).ne_top_iff.mpr hx.ne_zero)
  have hkpos : 0 < k := by rw [← hk] at hpos; exact_mod_cast hpos
  have hone : (1 : WithTop ℤ) ≤ normalizedBranchOrder p L x := by
    rw [← hk]
    exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  let n := fun q : IsDedekindDomain.HeightOneSpectrum R => if q = p then 1 else m q
  have hn (q) (hq : q ∈ insert p B) : 0 < n q := by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simp [n]
    · have hqp : q ≠ p := fun he => hp (he ▸ hq)
      simpa only [n, ite_eq_right hqp] using hm q hq
  have hno (q) (hq : q ∈ insert p B) :
      ((n q : ℤ) : WithTop ℤ) ≤ normalizedBranchOrder q L x := by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simpa only [n, ite_eq_left rfl, Nat.cast_one, WithTop.coe_one] using hone
    · have hqp : q ≠ p := fun he => hp (he ▸ hq)
      simpa only [n, ite_eq_right hqp] using horder q hq
  have htotal := branch_zero_degree_lower_bounds x hx (insert p B) n hn hno
  have hsum : (∑ q ∈ insert p B, n q * Module.finrank ℚ (R ⧸ q.asIdeal)) =
      Module.finrank ℚ (R ⧸ p.asIdeal) +
        ∑ q ∈ B, m q * Module.finrank ℚ (R ⧸ q.asIdeal) := by
    rw [Finset.sum_insert hp]
    simp only [n, ite_eq_left rfl, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have hqp : q ≠ p := fun he => hp (he ▸ hq)
    rw [ite_eq_right hqp]
  rw [hsum] at htotal
  have := branch_residue_degree_pos p
  omega

/-- Orders at least 3t, over a fiber whose orders are 2t and total degree d,
give 3d/2 plus the contribution from a separate zero. The doubled form avoids
rounding or rational casts. -/
theorem branch_zero_degree_three_halves {R L : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (B : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (t : IsDedekindDomain.HeightOneSpectrum R → ℕ)
    (ht : ∀ q ∈ B, 0 < t q) {d : ℕ}
    (hdegree : ∑ q ∈ B, (2 * t q) * Module.finrank ℚ (R ⧸ q.asIdeal) = d)
    (horder : ∀ q ∈ B, (((3 * t q : ℕ) : ℤ) : WithTop ℤ) ≤ normalizedBranchOrder q L x)
    (p : IsDedekindDomain.HeightOneSpectrum R) (hp : p ∉ B)
    (hpos : 0 < normalizedBranchOrder p L x) :
    3 * d + 2 ≤ 2 * Module.finrank ℚ⟮x⟯ L := by
  have hh := branch_zero_degree_with_extra x hx B (fun q => 3 * t q)
    (fun q hq => Nat.mul_pos (by decide) (ht q hq)) horder p hp hpos
  simp_rw [mul_assoc] at hdegree hh
  rw [← Finset.mul_sum] at hdegree hh
  omega

end
end PierceLengthBound.FixedDividend
