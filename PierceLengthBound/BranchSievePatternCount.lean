/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveVertexCount

/-! Branch-bad full minor patterns (Lemma 10.5). The branch-sieve vertex of a
pattern consists of its minors `0, 1, 3, 6`. On each of the four Plücker charts
pivoted at one of these minors, the vertex is a signed permutation of the
chart coordinates `(m, u)`. Choosing the pivot of largest absolute value among these
four minors covers the patterns by eight charts, and the dyadic scaled-vertex
count bounds each chart. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open scoped Matrix
noncomputable section
open Finset

/-- The four minors forming the branch-sieve vertex of a pattern. -/
def branchFirstIndex : Fin 4 → Fin 10 := ![0, 1, 3, 6]
def branchFirstVertex (p : Fin 10 → ℤ) : Fin 4 → ℤ := fun i => p (branchFirstIndex i)
def branchPivotSign (b : Bool) : ℤ := if b then 1 else -1

/-- The branch-sieve vertex in terms of the coordinates `(m, u)` of the chart
pivoted at minor `branchFirstIndex t`, with pivot sign `b`. -/
def branchVertexFromChart (t : Fin 4) (b : Bool) (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![![branchPivotSign b * x 0, x 3, -x 2, x 1],
    ![x 3, branchPivotSign b * x 0, x 2, -x 1],
    ![-x 3, x 2, branchPivotSign b * x 0, x 1],
    ![x 3, -x 2, x 1, branchPivotSign b * x 0]] t

theorem branchVertexFromChart_injective (t : Fin 4) (b : Bool) :
    Function.Injective (branchVertexFromChart t b) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  funext i
  fin_cases t <;> cases b <;> fin_cases i <;>
    simp_all [branchVertexFromChart, branchPivotSign]

theorem branchVertexFromChart_scale (t : Fin 4) (b : Bool) (g : ℤ) (x : Fin 4 → ℤ) :
    branchVertexFromChart t b (fun i => g * x i) =
      fun i => g * branchVertexFromChart t b x i := by
  funext i
  fin_cases t <;> cases b <;> fin_cases i <;>
    simp [branchVertexFromChart, branchPivotSign]

theorem branchVertexFromChart_mem (t : Fin 4) (b : Bool) {R : ℕ} {x : Fin 4 → ℤ}
    (hx : x ∈ ibox4 R) : branchVertexFromChart t b x ∈ ibox4 R := by
  have h j := abs_le.mpr (mem_Icc.mp (Fintype.mem_piFinset.mp hx j))
  apply Fintype.mem_piFinset.mpr
  intro i
  apply mem_Icc.mpr
  apply abs_le.mp
  fin_cases t <;> cases b <;> fin_cases i <;>
    simpa [branchVertexFromChart, branchPivotSign] using h _

lemma branch_signed_abs (z : ℤ) :
    branchPivotSign (decide (0 < z)) * z.natAbs = z := by
  by_cases h : 0 < z
  · simp [branchPivotSign, h, abs_of_pos h]
  · simp [branchPivotSign, h, abs_of_nonpos (by omega : z ≤ 0)]

lemma integerFirstVertex_eq_vector (m : ℕ) (u : Fin 3 → ℤ) :
    integerFirstVertex m u = ![(m : ℤ), u 0, u 1, u 2] := by
  funext i
  fin_cases i <;> rfl

theorem branchFirstVertex_from_chart (p : Fin 10 → ℤ) (t : Fin 4) :
    branchVertexFromChart t (decide (0 < p (branchFirstIndex t)))
      (integerFirstVertex (p (branchFirstIndex t)).natAbs (uVec p (branchFirstIndex t))) =
      branchFirstVertex p := by
  have he := branch_signed_abs (p (branchFirstIndex t))
  rw [integerFirstVertex_eq_vector]
  funext i
  fin_cases t <;> fin_cases i <;>
    simp_all [branchVertexFromChart, branchFirstVertex, branchFirstIndex, uVec, puS, puX]

open Classical in
theorem branch_chart_scaled_vertex_count (bad : (Fin 4 → ℤ) → Prop)
    (t : Fin 4) (b : Bool) (g R : ℕ) :
    (((ibox4 R).filter fun x => bad
      (branchVertexFromChart t b (fun i => (g : ℤ) * x i))).card : ℝ) ≤
      (((ibox4 R).filter fun x => bad (fun i => (g : ℤ) * x i)).card : ℝ) := by
  exact_mod_cast card_le_card_of_injOn (branchVertexFromChart t b)
    (fun x hx => mem_filter.mpr ⟨branchVertexFromChart_mem t b (mem_filter.mp hx).1,
      by simpa only [branchVertexFromChart_scale] using (mem_filter.mp hx).2⟩)
    (branchVertexFromChart_injective t b).injOn

/-- A vertex minor of largest absolute value, used as the chart pivot. -/
def branchFirstPivot (p : Fin 10 → ℤ) : Fin 4 :=
  (exists_max_image univ (fun t => |branchFirstVertex p t|) univ_nonempty).choose

theorem branchFirstPivot_max (p : Fin 10 → ℤ) (t : Fin 4) :
    |branchFirstVertex p t| ≤ |branchFirstVertex p (branchFirstPivot p)| :=
  (exists_max_image univ (fun t => |branchFirstVertex p t|) univ_nonempty).choose_spec.2
    t (mem_univ t)

theorem branchFirstPivot_ne_zero {p : Fin 10 → ℤ} (hp : branchFirstVertex p ≠ 0) :
    p (branchFirstIndex (branchFirstPivot p)) ≠ 0 := by
  intro h
  apply hp
  funext i
  have hi := branchFirstPivot_max p i
  change |branchFirstVertex p i| ≤ |p (branchFirstIndex (branchFirstPivot p))| at hi
  rw [h, abs_zero] at hi
  exact abs_nonpos_iff.mp hi

lemma branchFirstIndex_u (t : Fin 4) (j : Fin 3) :
    ∃ k : Fin 4, puX (branchFirstIndex t) j = branchFirstIndex k := by
  fin_cases t <;> fin_cases j <;> decide

lemma branch_chart_injective {p q : Fin 10 → ℤ} (hp : PluckerRel p) (hq : PluckerRel q)
    (t : Fin 10) (ht : p t ≠ 0) (hm : p t = q t)
    (hu : uVec p t = uVec q t) (hv : vVec p t = vVec q t) : p = q := by
  funext s
  rcases cover t s with h | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, h⟩
  · rw [h, hm]
  · have e := congrFun hu a
    simp only [uVec] at e
    have hs := (sign_sq t a).1
    rw [h]
    linear_combination puS t a * e + (q (puX t a) - p (puX t a)) * hs
  · have e := congrFun hv a
    simp only [vVec] at e
    have hs := (sign_sq t a).2.1
    rw [h]
    linear_combination pvS t a * e + (q (pvX t a) - p (pvX t a)) * hs
  · have e1 := hp t a
    have e2 := hq t a
    rw [← hm, ← hu, ← hv] at e2
    rw [h]
    exact mul_left_cancel₀ ht (e1.trans e2.symm)

def branchPatternChartKey (t : Fin 4) (p : Fin 10 → ℤ) : BranchChartState :=
  ((p (branchFirstIndex t)).natAbs, uVec p (branchFirstIndex t), vVec p (branchFirstIndex t))

lemma branchPatternChartKey_injOn (t : Fin 4) (b : Bool) (S : Finset (Fin 10 → ℤ))
    (hS : ∀ p ∈ S, PluckerRel p ∧ p (branchFirstIndex t) ≠ 0 ∧
      decide (0 < p (branchFirstIndex t)) = b) : Set.InjOn (branchPatternChartKey t) S := by
  intro p hp q hq he
  obtain ⟨hpp, hpt, hpb⟩ := hS p hp
  obtain ⟨hqp, hqt, hqb⟩ := hS q hq
  have hab : (p (branchFirstIndex t)).natAbs = (q (branchFirstIndex t)).natAbs :=
    congrArg Prod.fst he
  have hu := congrArg (fun x : BranchChartState => x.2.1) he
  have hv := congrArg (fun x : BranchChartState => x.2.2) he
  apply branch_chart_injective hpp hqp (branchFirstIndex t) hpt ?_ hu hv
  have ep := branch_signed_abs (p (branchFirstIndex t))
  have eq := branch_signed_abs (q (branchFirstIndex t))
  rw [hpb, hab] at ep
  rw [hqb] at eq
  exact ep.symm.trans eq

lemma branchPatternChartKey_properties {X : ℕ} {p : Fin 10 → ℤ}
    (hb : ∀ j, |p j| ≤ X) (hp : PluckerRel p) (hnz : branchFirstVertex p ≠ 0) :
    let w := branchPatternChartKey (branchFirstPivot p) p
    0 < w.1 ∧ w.1 ≤ X ∧ w.2.1 ∈ ibox3 w.1 ∧ w.2.2 ∈ ibox3 X ∧
      ∀ j, (w.1 : ℤ) ∣ (w.2.1 ⨯₃ w.2.2) j := by
  let t := branchFirstIndex (branchFirstPivot p)
  have ht : p t ≠ 0 := branchFirstPivot_ne_zero hnz
  have hsU j : |puS t j| = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (sign_sq t j).1 with h | h <;> simp [h]
  have hsV j : |pvS t j| = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (sign_sq t j).2.1 with h | h <;> simp [h]
  refine ⟨Int.natAbs_pos.mpr ht, ?_, ?_, ?_, ?_⟩
  · have h := hb t
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · apply Fintype.mem_piFinset.mpr
    intro j
    apply mem_Icc.mpr
    apply abs_le.mp
    change |uVec p t j| ≤ (p t).natAbs
    rw [Int.natCast_natAbs]
    obtain ⟨k, hk⟩ := branchFirstIndex_u (branchFirstPivot p) j
    simp only [uVec, Int.cast_id, abs_mul, hsU j, one_mul]
    change |p (puX (branchFirstIndex (branchFirstPivot p)) j)| ≤
      |p (branchFirstIndex (branchFirstPivot p))|
    rw [hk]
    exact branchFirstPivot_max p k
  · apply Fintype.mem_piFinset.mpr
    intro j
    apply mem_Icc.mpr
    apply abs_le.mp
    change |vVec p t j| ≤ X
    simpa only [vVec, Int.cast_id, abs_mul, hsV j, one_mul] using hb (pvX t j)
  · intro j
    change ((p t).natAbs : ℤ) ∣ (uVec p t ⨯₃ vVec p t) j
    rw [Int.natCast_natAbs]
    apply (abs_dvd _ _).mpr
    refine ⟨pwS t j * p (pwX t j), ?_⟩
    have h1 := hp t j
    have h2 := (sign_sq t j).2.2
    linear_combination (-pwS t j) * h1 - (uVec p t ⨯₃ vVec p t) j * h2

open Classical in
/-- A square-root saving for scaled four-label vertices gives the required
power saving for full minor patterns, including arbitrary common divisors. -/
theorem branch_full_pattern_count :
    ∃ K : ℝ, 0 < K ∧ ∀ (bad : (Fin 4 → ℤ) → Prop) (C : ℝ), 0 ≤ C →
      ∀ X : ℕ, 0 < X → ∀ S : Finset (Fin 10 → ℤ),
      (∀ p ∈ S, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ branchFirstVertex p ≠ 0 ∧
        bad (branchFirstVertex p)) →
      (∀ g R : ℕ, 0 < g → g ≤ 2 * X → 0 < R → R ≤ 2 * X →
        (((ibox4 R).filter fun x => bad (fun i => (g : ℤ) * x i)).card : ℝ) ≤
          C * (R : ℝ) ^ (7 / 2 : ℝ)) →
      (S.card : ℝ) ≤ K * C * (X : ℝ) ^ (9 / 2 : ℝ) * (Nat.log 2 X + 1 : ℕ) := by
  obtain ⟨K, hK, hchart⟩ := branch_chart_bad_count
  refine ⟨8 * K, by positivity, ?_⟩
  intro bad C hC X hX S hS hbad
  let key (p : Fin 10 → ℤ) : Fin 4 × Bool :=
    (branchFirstPivot p, decide (0 < p (branchFirstIndex (branchFirstPivot p))))
  have hfiber : ∀ z : Fin 4 × Bool,
      ((S.filter fun p => key p = z).card : ℝ) ≤
        K * C * (X : ℝ) ^ (9 / 2 : ℝ) * (Nat.log 2 X + 1 : ℕ) := by
    intro z
    let T := S.filter fun p => key p = z
    let U := T.image (branchPatternChartKey z.1)
    let bad' := fun x => bad (branchVertexFromChart z.1 z.2 x)
    have hTp p (hp : p ∈ T) : branchFirstPivot p = z.1 ∧
        decide (0 < p (branchFirstIndex z.1)) = z.2 := by
      have he := (mem_filter.mp hp).2
      have h1 : branchFirstPivot p = z.1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      exact ⟨h1, by simpa only [key, h1] using h2⟩
    have hTU : T.card = U.card := by
      symm
      apply card_image_of_injOn
      apply branchPatternChartKey_injOn z.1 z.2 T
      intro p hp
      have hh := hS p (mem_filter.mp hp).1
      obtain ⟨ht, hb⟩ := hTp p hp
      exact ⟨hh.2.1, by simpa only [ht] using branchFirstPivot_ne_zero hh.2.2.1, hb⟩
    rw [show (S.filter fun p => key p = z) = T from rfl, hTU]
    apply hchart bad' C hC X hX U
    · intro w hw
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hw
      obtain ⟨hb, hpl, hnz, hbadp⟩ := hS p (mem_filter.mp hp).1
      obtain ⟨ht, hsign⟩ := hTp p hp
      have hh := branchPatternChartKey_properties hb hpl hnz
      rw [ht] at hh
      obtain ⟨h1,h2,h3,h4,h5⟩ := hh
      refine ⟨h1,h2,h3,h4,h5,?_⟩
      change bad (branchVertexFromChart z.1 z.2
        (integerFirstVertex (p (branchFirstIndex z.1)).natAbs (uVec p (branchFirstIndex z.1))))
      rw [← hsign, branchFirstVertex_from_chart]
      exact hbadp
    · intro g R hg hgX hR hRX
      exact (branch_chart_scaled_vertex_count bad z.1 z.2 g R).trans (hbad g R hg hgX hR hRX)
  rw [card_eq_sum_card_fiberwise (f := key) (t := univ) (fun _ _ => mem_univ _), Nat.cast_sum]
  calc
    _ ≤ ∑ _z : Fin 4 × Bool,
        K * C * (X : ℝ) ^ (9 / 2 : ℝ) * (Nat.log 2 X + 1 : ℕ) := sum_le_sum fun z _ => hfiber z
    _ = _ := by simp; ring

end
end PierceLengthBound.FixedDividend
