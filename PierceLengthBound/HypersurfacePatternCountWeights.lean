/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendWeights
public import PierceLengthBound.MinorCount
public import PierceLengthBound.ShortVec

/-!
# Short vectors in the normal congruence lattices

For an integer triple `u`, the normal lattice is `{z : n ∣ u · z}`, and `μ(u) = normalShortR n u`
is its least nonzero sup norm, which lies between `1` and about `n^(1/3)`. Incidence counting
and partial summation give `∑_u 1/μ(u) ≤ 5859 τ(n) n^(8/3)` over all `u ∈ [-n,n]³`, primitive
or not. This bounds the reciprocal weights in the nonzero-fiber count of the
hypersurface-pattern estimate.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- A nonzero vector of sup norm at most `R` in the normal congruence lattice. -/
def NormalHasShort (n : ℕ) (u : Fin 3 → ℤ) (R : ℕ) : Prop :=
  ∃ z : Fin 3 → ℤ, (n : ℤ) ∣ u ⬝ᵥ z ∧ z ≠ 0 ∧ ∀ j, |z j| ≤ R

/-- The least nonzero sup norm in the normal congruence lattice. -/
def normalShortR (n : ℕ) (u : Fin 3 → ℤ) : ℕ := sInf {R : ℕ | NormalHasShort n u R}

lemma normalHasShort_nonempty {n : ℕ} (hn : 0 < n) (u : Fin 3 → ℤ) :
    NormalHasShort n u n := by
  refine ⟨![(n : ℤ), 0, 0], ?_, ?_, ?_⟩
  · simp
  · intro hz
    have := congrFun hz 0
    simp at this
    omega
  · intro j
    fin_cases j <;> simp

/-- `μ(u) ≥ 1`, and the normal lattice has a nonzero vector of sup norm at most `μ(u)`. -/
lemma normalShortR_spec {n : ℕ} (hn : 0 < n) (u : Fin 3 → ℤ) :
    1 ≤ normalShortR n u ∧ NormalHasShort n u (normalShortR n u) := by
  have hne : ({R : ℕ | NormalHasShort n u R} : Set ℕ).Nonempty :=
    ⟨n, normalHasShort_nonempty hn u⟩
  have hmem : NormalHasShort n u (normalShortR n u) := Nat.sInf_mem hne
  refine ⟨?_, hmem⟩
  by_contra hc
  have hzero : normalShortR n u = 0 := by omega
  obtain ⟨z, _, hz, hbound⟩ := hmem
  apply hz
  funext j
  have hj := hbound j
  rw [hzero, Nat.cast_zero] at hj
  exact abs_nonpos_iff.mp hj

lemma normalShortR_le {n R : ℕ} {u : Fin 3 → ℤ} (h : NormalHasShort n u R) :
    normalShortR n u ≤ R := Nat.sInf_le h

/-- Pigeonhole: if `n < (L + 1)³`, the normal lattice of every `u` has a nonzero vector
of sup norm at most `L`. -/
theorem normal_lattice_short {n L : ℕ} (hn : 0 < n) (u : Fin 3 → ℤ)
    (hL : n < (L + 1) ^ 3) : NormalHasShort n u L := by
  classical
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  let ψ : (Fin 3 → ℤ) → ℤ := fun x => (u ⬝ᵥ x) % n
  have hmaps : ∀ x ∈ Fintype.piFinset (fun _ : Fin 3 => Icc (0 : ℤ) L),
      ψ x ∈ Ico (0 : ℤ) n := fun x _ => mem_Ico.mpr
    ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩
  have hcard : (Ico (0 : ℤ) n).card <
      (Fintype.piFinset fun _ : Fin 3 => Icc (0 : ℤ) L).card := by
    rw [Int.card_Ico, Fintype.card_piFinset, Fin.prod_univ_three, Int.card_Icc]
    rw [show ((n : ℤ) - 0).toNat = n by omega,
      show ((L : ℤ) + 1 - 0).toNat = L + 1 by omega]
    simpa only [pow_succ, pow_zero, one_mul] using hL
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  refine ⟨x - y, ?_, sub_ne_zero.mpr hne, fun j => ?_⟩
  · rw [dotProduct_sub]
    exact Int.ModEq.dvd hxy.symm
  · have hxj := mem_Icc.mp (Fintype.mem_piFinset.mp hx j)
    have hyj := mem_Icc.mp (Fintype.mem_piFinset.mp hy j)
    simp only [Pi.sub_apply]
    rw [abs_le]
    constructor <;> linarith

/-- Few normal lattices have a short vector: at most `729 n² τ(n) R³` triples
`u ∈ [-n,n]³` have `μ(u) ≤ R`. -/
theorem normal_short_count {n : ℕ} (hn : 0 < n) (R : ℕ) :
    ((ibox3 n).filter fun u => normalShortR n u ≤ R).card ≤
      729 * n ^ 2 * n.divisors.card * R ^ 3 := by
  classical
  let Z := (ibox3 R).filter fun z => z ≠ 0
  have hsub : (ibox3 n).filter (fun u => normalShortR n u ≤ R) ⊆
      Z.biUnion fun z => (ibox3 n).filter fun u => (n : ℤ) ∣ u ⬝ᵥ z := by
    intro u hu
    obtain ⟨hub, huR⟩ := mem_filter.mp hu
    obtain ⟨_, z, hdz, hz, hzb⟩ := normalShortR_spec hn u
    refine mem_biUnion.mpr ⟨z, mem_filter.mpr ⟨?_, hz⟩, mem_filter.mpr ⟨hub, hdz⟩⟩
    exact Fintype.mem_piFinset.mpr fun j => mem_Icc.mpr
      (abs_le.mp ((hzb j).trans (by exact_mod_cast huR)))
  calc ((ibox3 n).filter fun u => normalShortR n u ≤ R).card
      ≤ ∑ z ∈ Z, ((ibox3 n).filter fun u => (n : ℤ) ∣ u ⬝ᵥ z).card :=
        (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ z ∈ Z, 27 * n ^ 2 * gcd4 n z := sum_le_sum fun z _ => card_dot_dvd_le hn z
    _ = 27 * n ^ 2 * ∑ z ∈ Z, gcd4 n z := by rw [mul_sum]
    _ ≤ 27 * n ^ 2 * (27 * R ^ 3 * n.divisors.card) :=
      Nat.mul_le_mul_left _ (sum_gcd4_box_le hn R)
    _ = _ := by ring

/-- `∑_{u ∈ [-n,n]³} 1/μ(u) ≤ 5859 τ(n) n^(8/3)`: the reciprocal normal-lattice minimum
has average `O(τ(n) n^(-1/3))` over the coefficient box. -/
theorem normal_short_weight_sum {n : ℕ} (hn : 0 < n) :
    ∑ u ∈ ibox3 n, (normalShortR n u : ℝ)⁻¹ ≤
      5859 * (n.divisors.card : ℝ) * (n : ℝ) ^ (8 / 3 : ℝ) := by
  classical
  obtain ⟨L, hL1, hnL, hL8⟩ := exists_cube_root (show 1 ≤ n by omega)
  have hR : ∀ u ∈ ibox3 n, 1 ≤ normalShortR n u ∧ normalShortR n u ≤ L := by
    intro u _
    refine ⟨(normalShortR_spec hn u).1, normalShortR_le (normal_lattice_short hn u ?_)⟩
    exact hnL.trans_lt (Nat.pow_lt_pow_left (by omega) (by norm_num))
  have hab := reciprocal_sum_bound (ibox3 n) (normalShortR n)
    (C := 729 * n ^ 2 * n.divisors.card) hR (fun r _ => normal_short_count hn r)
  have hc : (ibox3 n).card ≤ 27 * n ^ 3 := by
    rw [ibox3, Fintype.card_piFinset, Fin.prod_univ_three, Int.card_Icc]
    rw [show ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 by omega]
    calc (2 * n + 1) * (2 * n + 1) * (2 * n + 1) ≤ (3 * n) * (3 * n) * (3 * n) := by
            gcongr <;> omega
      _ = _ := by ring
  have hτ : 1 ≤ n.divisors.card := Finset.card_pos.mpr
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hτR : (1 : ℝ) ≤ n.divisors.card := by exact_mod_cast hτ
  have hL3 : (L : ℝ) ^ 3 ≤ 8 * n := by exact_mod_cast hL8
  have hcR : ((ibox3 n).card : ℝ) ≤ 27 * (n : ℝ) ^ 3 := by exact_mod_cast hc
  have hsum : (L : ℝ) * ∑ u ∈ ibox3 n, (normalShortR n u : ℝ)⁻¹ ≤
      5859 * (n.divisors.card : ℝ) * (n : ℝ) ^ 3 := by
    simp only [one_div] at hab
    refine hab.trans ?_
    push_cast
    have hp := mul_le_mul_of_nonneg_left hL3
      (show (0 : ℝ) ≤ 729 * n ^ 2 * n.divisors.card by positivity)
    have hp' := mul_le_mul_of_nonneg_right hτR (show (0 : ℝ) ≤ 27 * n ^ 3 by positivity)
    nlinarith
  have hn13 : (n : ℝ) ^ (1 / 3 : ℝ) ≤ L := by
    have h : (n : ℝ) ≤ (L : ℝ) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact_mod_cast hnL
    calc (n : ℝ) ^ (1 / 3 : ℝ) ≤ ((L : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hnR.le h (by norm_num)
      _ = L := by rw [← Real.rpow_mul hLr.le]; norm_num
  have hprod : (n : ℝ) ^ (1 / 3 : ℝ) * ∑ u ∈ ibox3 n, (normalShortR n u : ℝ)⁻¹ ≤
      5859 * (n.divisors.card : ℝ) * (n : ℝ) ^ 3 :=
    (mul_le_mul_of_nonneg_right hn13 (sum_nonneg fun _ _ => by positivity)).trans hsum
  have hquot : (∑ u ∈ ibox3 n, (normalShortR n u : ℝ)⁻¹) ≤
      (5859 * (n.divisors.card : ℝ) * (n : ℝ) ^ 3) / (n : ℝ) ^ (1 / 3 : ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact hprod
  convert hquot using 1
  rw [mul_div_assoc, ← Real.rpow_natCast, ← Real.rpow_sub hnR]
  norm_num

end
end PierceLengthBound.FixedDividend
