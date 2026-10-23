/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividend
public import PierceLengthBound.FixedDividendLeadingResultant
public import Mathlib.Analysis.Complex.Basic

/-!
# The four normalized line directions

The Vandermonde and cluster arguments work over arbitrary fields, including complex
node directions. Real coefficient signs restrict the two-element cluster to four pairs.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

/-- A zero-weight cluster has at least two entries when all individual weights are nonzero. -/
lemma cluster_card_ge_two {K : Type*} [Field K] [DecidableEq K] (c z : Fin 5 → K)
    (hc : ∀ j, c j ≠ 0)
    (hs : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => z j = z i), c j = 0) (i : Fin 5) :
    2 ≤ (Finset.univ.filter (fun j => z j = z i)).card := by
  classical
  let F := Finset.univ.filter (fun j => z j = z i)
  have hi : i ∈ F := by simp [F]
  by_contra h
  have hsmall : F.card ≤ 1 := by change (Finset.univ.filter (fun j => z j = z i)).card ≤ 1; omega
  have he : F = {i} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hi, fun j hj => Finset.card_le_one.mp hsmall j hj i hi⟩
  have hsum : ∑ j ∈ F, c j = 0 := hs i
  rw [he, Finset.sum_singleton] at hsum
  exact hc i hsum

/-- Five nonzero weights with vanishing cluster sums cannot have three distinct clusters. -/
lemma at_most_two_clusters {K : Type*} [Field K] [DecidableEq K] (c z : Fin 5 → K)
    (hc : ∀ j, c j ≠ 0)
    (hs : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => z j = z i), c j = 0)
    (i j k : Fin 5) : z i = z j ∨ z i = z k ∨ z j = z k := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨hij, hik, hjk⟩ := hn
  let F (i : Fin 5) := Finset.univ.filter (fun j => z j = z i)
  have hd : ∀ a b, z a ≠ z b → Disjoint (F a) (F b) := by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    exact hab ((Finset.mem_filter.mp hxa).2.symm.trans (Finset.mem_filter.mp hxb).2)
  have hc5 : ((F i ∪ F j) ∪ F k).card ≤ 5 :=
    (Finset.card_le_univ _).trans (by decide)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd i k hik, hd j k hjk⟩),
    Finset.card_union_of_disjoint (hd i j hij)] at hc5
  have hi := cluster_card_ge_two c z hc hs i
  have hj := cluster_card_ge_two c z hc hs j
  have hk := cluster_card_ge_two c z hc hs k
  change 2 ≤ (F i).card at hi
  change 2 ≤ (F j).card at hj
  change 2 ≤ (F k).card at hk
  omega

/-- The two-element cluster, retaining the membership information needed for directions. -/
theorem exists_pair_cluster {K : Type*} [Field K] [DecidableEq K] (c z : Fin 5 → K)
    (hc : ∀ j, c j ≠ 0) (hz : ∃ i j, z i ≠ z j)
    (hs : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => z j = z i), c j = 0) :
    ∃ j l : Fin 5, j < l ∧ c j + c l = 0 ∧ z j = z l ∧
      (∀ k, z k = z j ↔ k = j ∨ k = l) ∧
      (∀ k m, k ≠ j → k ≠ l → m ≠ j → m ≠ l → z k = z m) := by
  classical
  let F (i : Fin 5) := Finset.univ.filter (fun j => z j = z i)
  have hpair : ∀ i, (F i).card = 2 →
      ∃ j l : Fin 5, j < l ∧ c j + c l = 0 ∧ z j = z l ∧
        (∀ k, z k = z j ↔ k = j ∨ k = l) ∧
        (∀ k m, k ≠ j → k ≠ l → m ≠ j → m ≠ l → z k = z m) := by
    intro i hi
    obtain ⟨j, l, hjl, he⟩ := Finset.card_eq_two.mp hi
    have hsum : c j + c l = 0 := by
      have hsum := hs i
      change ∑ k ∈ F i, c k = 0 at hsum
      simpa [he, hjl] using hsum
    have hzj : z j = z i := by
      have hj : j ∈ F i := by rw [he]; simp
      exact (Finset.mem_filter.mp hj).2
    have hzl : z l = z i := by
      have hl : l ∈ F i := by rw [he]; simp
      exact (Finset.mem_filter.mp hl).2
    have hmem : ∀ k, z k = z j ↔ k = j ∨ k = l := by
      intro k
      rw [hzj]
      have h : z k = z i ↔ k ∈ F i := by simp [F]
      rw [h, he]
      simp
    have hrest : ∀ k m, k ≠ j → k ≠ l → m ≠ j → m ≠ l → z k = z m := by
      intro k m hkj hkl hmj hml
      rcases at_most_two_clusters c z hc hs j k m with h | h | h
      · exact False.elim ((hmem k).mp h.symm |>.elim hkj hkl)
      · exact False.elim ((hmem m).mp h.symm |>.elim hmj hml)
      · exact h
    rcases lt_or_gt_of_ne hjl with hjl | hjl
    · exact ⟨j, l, hjl, hsum, hzj.trans hzl.symm, hmem, hrest⟩
    · refine ⟨l, j, hjl, by rw [add_comm]; exact hsum, hzl.trans hzj.symm, ?_, ?_⟩
      · intro k
        rw [show z l = z j from hzl.trans hzj.symm, hmem]
        exact or_comm
      · intro k m hkl hkj hml hmj
        exact hrest k m hkj hkl hmj hml
  obtain ⟨i, j, hij⟩ := hz
  by_cases hi : (F i).card = 2
  · exact hpair i hi
  by_cases hj : (F j).card = 2
  · exact hpair j hj
  have hd : Disjoint (F i) (F j) := by
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    exact hij ((Finset.mem_filter.mp hki).2.symm.trans (Finset.mem_filter.mp hkj).2)
  have hcard : (F i).card + (F j).card ≤ 5 := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_univ _).trans (by decide)
  have hi2 : 2 ≤ (F i).card := cluster_card_ge_two c z hc hs i
  have hj2 : 2 ≤ (F j).card := cluster_card_ge_two c z hc hs j
  omega

/-- Vandermonde clustering over an arbitrary field. -/
theorem cluster_sums_zero_field {K : Type*} [Field K] [DecidableEq K] (c z : Fin 5 → K)
    (hcard : (Finset.univ.image z).card ≤ 4)
    (hmom : ∀ m < 4, ∑ j : Fin 5, c j * z j ^ m = 0) :
    ∀ i, ∑ j ∈ Finset.univ.filter (fun j => z j = z i), c j = 0 := by
  classical
  let S := Finset.univ.image z
  let w (x : K) := ∑ j ∈ Finset.univ.filter (fun j => z j = x), c j
  let e := (Fintype.equivFin S).symm
  have hgroup : ∀ m < 4, ∑ x : S, w x * (x : K) ^ m = 0 := by
    intro m hm
    calc (∑ x : S, w x * (x : K) ^ m) = ∑ x ∈ S, w x * x ^ m :=
          Finset.sum_coe_sort S (fun x => w x * x ^ m)
      _ =
        ∑ x ∈ S, ∑ j ∈ Finset.univ.filter (fun j => z j = x), c j * z j ^ m := by
          refine Finset.sum_congr rfl fun x hx => ?_
          dsimp only [w]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(Finset.mem_filter.mp hj).2]
      _ = ∑ j : Fin 5, c j * z j ^ m :=
        Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem z hj) _
      _ = 0 := hmom m hm
  have hinj : Function.Injective (fun j : Fin (Fintype.card S) => (e j : K)) := by
    intro j l h
    exact e.injective (Subtype.ext h)
  have hw : (fun j : Fin (Fintype.card S) => w (e j)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro m
    have hm : (m : ℕ) < 4 := by
      have hn : Fintype.card S ≤ 4 := by simpa only [Fintype.card_coe] using hcard
      exact m.isLt.trans_le hn
    calc (∑ j : Fin (Fintype.card S), w (e j) * (e j : K) ^ (m : ℕ)) =
        ∑ x : S, w x * (x : K) ^ (m : ℕ) := Equiv.sum_comp e (fun x : S => w x * (x : K) ^ (m : ℕ))
      _ = 0 := hgroup m hm
  intro i
  let xi : S := ⟨z i, Finset.mem_image_of_mem z (Finset.mem_univ i)⟩
  have he := congrFun hw (e.symm xi)
  simpa only [e.apply_symm_apply, Pi.zero_apply] using he

/-- The four normalized direction vectors, including the fixed initial node zero. -/
def normalizedDirection {K : Type*} [Zero K] [One K] (d : Fin 4) : Fin 5 → K :=
  ![![0, 1, 1, 0, 1], ![0, 1, 1, 0, 0], ![0, 0, 1, 1, 0], ![0, 1, 0, 0, 1]] d

/-- The two-element cluster corresponding to each normalized direction. -/
def exceptionalPair (d : Fin 4) : Fin 5 × Fin 5 := ![(0, 3), (1, 2), (2, 3), (1, 4)] d

/-- Exact normalization of two-cluster directions, over arbitrary fields. -/
theorem normalized_direction_of_clusters {K : Type*} [Field K] [DecidableEq K]
    (c z : Fin 5 → K) (hc : ∀ j, c j ≠ 0) (hz : ∃ i j, z i ≠ z j) (hz0 : z 0 = 0)
    (hs : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => z j = z i), c j = 0)
    (hallowed : ∀ j l : Fin 5, j < l → c j + c l = 0 →
      (j = 0 ∧ l = 3) ∨ (j = 1 ∧ l = 2) ∨ (j = 2 ∧ l = 3) ∨ (j = 1 ∧ l = 4)) :
    ∃ d : Fin 4, ∃ t : K, t ≠ 0 ∧ (∀ j, z j = t * normalizedDirection d j) ∧
      c (exceptionalPair d).1 + c (exceptionalPair d).2 = 0 := by
  obtain ⟨j, l, hjl, hsum, heq, hmem, hrest⟩ := exists_pair_cluster c z hc hz hs
  rcases hallowed j l hjl hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h10 : z 1 ≠ z 0 := by
      intro h
      have := (hmem 1).mp h
      norm_num at this
    refine ⟨0, z 1, by simpa [hz0] using h10, ?_, hsum⟩
    intro k
    fin_cases k
    · simpa [normalizedDirection] using hz0
    · simp [normalizedDirection]
    · simpa [normalizedDirection] using hrest 2 1 (by decide) (by decide) (by decide) (by decide)
    · simpa [normalizedDirection, hz0] using heq.symm
    · simpa [normalizedDirection] using hrest 4 1 (by decide) (by decide) (by decide) (by decide)
  · have h01 : z 0 ≠ z 1 := by
      intro h
      have := (hmem 0).mp h
      norm_num at this
    refine ⟨1, z 1, by simpa [hz0] using h01.symm, ?_, hsum⟩
    intro k
    fin_cases k
    · simpa [normalizedDirection] using hz0
    · simp [normalizedDirection]
    · simpa [normalizedDirection] using heq.symm
    · simpa [normalizedDirection, hz0] using
        hrest 3 0 (by decide) (by decide) (by decide) (by decide)
    · simpa [normalizedDirection, hz0] using
        hrest 4 0 (by decide) (by decide) (by decide) (by decide)
  · have h02 : z 0 ≠ z 2 := by
      intro h
      have := (hmem 0).mp h
      norm_num at this
    refine ⟨2, z 2, by simpa [hz0] using h02.symm, ?_, hsum⟩
    intro k
    fin_cases k
    · simpa [normalizedDirection] using hz0
    · simpa [normalizedDirection, hz0] using
        hrest 1 0 (by decide) (by decide) (by decide) (by decide)
    · simp [normalizedDirection]
    · simpa [normalizedDirection] using heq.symm
    · simpa [normalizedDirection, hz0] using
        hrest 4 0 (by decide) (by decide) (by decide) (by decide)
  · have h01 : z 0 ≠ z 1 := by
      intro h
      have := (hmem 0).mp h
      norm_num at this
    refine ⟨3, z 1, by simpa [hz0] using h01.symm, ?_, hsum⟩
    intro k
    fin_cases k
    · simpa [normalizedDirection] using hz0
    · simp [normalizedDirection]
    · simpa [normalizedDirection, hz0] using
        hrest 2 0 (by decide) (by decide) (by decide) (by decide)
    · simpa [normalizedDirection, hz0] using
        hrest 3 0 (by decide) (by decide) (by decide) (by decide)
    · simpa [normalizedDirection] using heq.symm

/-- For `ρ > 0`, `u > 0`, `v < 0`, only four index pairs have Newton coefficients
summing to zero. -/
lemma pair_indices_exceptional {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    {j l : Fin 5} (hjl : j < l) (h : coeffs ρ u v j + coeffs ρ u v l = 0) :
    (j = 0 ∧ l = 3) ∨ (j = 1 ∧ l = 2) ∨ (j = 2 ∧ l = 3) ∨ (j = 1 ∧ l = 4) := by
  fin_cases j <;> fin_cases l <;> norm_num at hjl
  all_goals norm_num [coeffs] at h ⊢
  all_goals linarith

/-- The coefficient relation belonging to each exceptional pair. -/
def exceptionalRelation (ρ u v : ℝ) (d : Fin 4) : Prop :=
  ![v = 1 - ρ, v = -ρ, u = 1, u = 1 - ρ] d

/-- A vanishing pair sum gives the corresponding coefficient relation. -/
lemma exceptionalRelation_of_pair {ρ u v : ℝ} (d : Fin 4)
    (h : coeffs ρ u v (exceptionalPair d).1 + coeffs ρ u v (exceptionalPair d).2 = 0) :
    exceptionalRelation ρ u v d := by
  fin_cases d <;> norm_num [coeffs, exceptionalPair, exceptionalRelation] at h ⊢ <;> linarith

/-- The generic coefficient formula commutes with the real-to-complex embedding. -/
lemma coeffs_ofReal (ρ u v : ℝ) (j : Fin 5) :
    coeffs (ρ : ℂ) (u : ℂ) (v : ℂ) j = ((coeffs ρ u v j : ℝ) : ℂ) := by
  fin_cases j <;> simp [coeffs]

/-- A nonconstant complex direction with `z 0 = 0`, at most four distinct entries and
vanishing moments of order below four is a nonzero multiple of one of the four
normalized directions, and the corresponding coefficient relation holds. -/
theorem complex_direction_classification {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (z : Fin 5 → ℂ) (hz : ∃ i j, z i ≠ z j) (hz0 : z 0 = 0)
    (hcard : (Finset.univ.image z).card ≤ 4)
    (hmom : ∀ m < 4, ∑ j : Fin 5, (coeffs ρ u v j : ℂ) * z j ^ m = 0) :
    ∃ d : Fin 4, ∃ t : ℂ, t ≠ 0 ∧ (∀ j, z j = t * normalizedDirection d j) ∧
      exceptionalRelation ρ u v d := by
  classical
  let c : Fin 5 → ℂ := fun j => ((coeffs ρ u v j : ℝ) : ℂ)
  have hcR : ∀ j, coeffs ρ u v j ≠ 0 := by
    intro j
    fin_cases j <;> norm_num [coeffs] <;> linarith
  have hc : ∀ j, c j ≠ 0 := by intro j; dsimp [c]; exact_mod_cast hcR j
  have hmom' : ∀ m < 4, ∑ j : Fin 5, c j * z j ^ m = 0 := by
    intro m hm
    simpa only [c, coeffs_ofReal] using hmom m hm
  have hs := cluster_sums_zero_field c z hcard hmom'
  have hallowed : ∀ j l : Fin 5, j < l → c j + c l = 0 →
      (j = 0 ∧ l = 3) ∨ (j = 1 ∧ l = 2) ∨ (j = 2 ∧ l = 3) ∨ (j = 1 ∧ l = 4) := by
    intro j l hjl hsum
    apply pair_indices_exceptional hρ hu hv hjl
    dsimp [c] at hsum
    exact_mod_cast hsum
  obtain ⟨d, t, ht, hz', hpair⟩ := normalized_direction_of_clusters c z hc hz hz0 hs hallowed
  refine ⟨d, t, ht, hz', exceptionalRelation_of_pair d ?_⟩
  dsimp [c] at hpair
  exact_mod_cast hpair

/-- A collision among five directions leaves at most four distinct directions. -/
lemma direction_card_of_collision {K : Type*} [DecidableEq K] (z : Fin 5 → K)
    {j l : Fin 5} (hjl : j ≠ l) (heq : z j = z l) :
    (Finset.univ.image z).card ≤ 4 := by
  have hle : (Finset.univ.image z).card ≤ 5 :=
    (Finset.card_image_le).trans (by decide)
  by_contra h
  have hcard : (Finset.univ.image z).card = (Finset.univ : Finset (Fin 5)).card := by
    have : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
    omega
  have hinj := Finset.card_image_iff.mp hcard
  exact hjl (hinj (by simp) (by simp) heq)

/-- Vanishing of the degree-ten Vandermonde form gives a node collision. -/
lemma direction_card_of_vandermonde {K : Type*} [Field K] [DecidableEq K]
    (z : Fin 5 → K) (hz0 : z 0 = 0)
    (hV : nodeVandermonde (fun j : Fin 4 => z j.succ) = 0) :
    (Finset.univ.image z).card ≤ 4 := by
  simp only [nodeVandermonde, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    mul_eq_zero, sub_eq_zero, or_assoc] at hV
  rcases hV with h | h | h | h | h | h | h | h | h | h
  · exact direction_card_of_collision z (j := 0) (l := 1) (by decide) (hz0.trans h.symm)
  · exact direction_card_of_collision z (j := 0) (l := 2) (by decide) (hz0.trans h.symm)
  · exact direction_card_of_collision z (j := 0) (l := 3) (by decide) (hz0.trans h.symm)
  · exact direction_card_of_collision z (j := 0) (l := 4) (by decide) (hz0.trans h.symm)
  · exact direction_card_of_collision z (j := 2) (l := 1) (by decide) h
  · exact direction_card_of_collision z (j := 3) (l := 1) (by decide) h
  · exact direction_card_of_collision z (j := 4) (l := 1) (by decide) h
  · exact direction_card_of_collision z (j := 3) (l := 2) (by decide) h
  · exact direction_card_of_collision z (j := 4) (l := 2) (by decide) h
  · exact direction_card_of_collision z (j := 4) (l := 3) (by decide) h

/-- The same classification, with the node collision supplied by vanishing of the
Vandermonde form. -/
theorem complex_direction_of_leading_equations {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (z : Fin 5 → ℂ) (hz : ∃ i j, z i ≠ z j) (hz0 : z 0 = 0)
    (hV : nodeVandermonde (fun j : Fin 4 => z j.succ) = 0)
    (hmom : ∀ m < 4, ∑ j : Fin 5, (coeffs ρ u v j : ℂ) * z j ^ m = 0) :
    ∃ d : Fin 4, ∃ t : ℂ, t ≠ 0 ∧ (∀ j, z j = t * normalizedDirection d j) ∧
      exceptionalRelation ρ u v d :=
  complex_direction_classification hρ hu hv z hz hz0
    (direction_card_of_vandermonde z hz0 hV) hmom

end PierceLengthBound.FixedDividend
