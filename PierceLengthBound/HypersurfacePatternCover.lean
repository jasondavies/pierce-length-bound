/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternChart
public import PierceLengthBound.HypersurfacePatternCountPolynomial

/-! A finite cover of the integral Plücker vectors on a proper hypersurface by the
twenty signed rational charts (pivot index and pivot sign). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Finset
open scoped Matrix
noncomputable section

/-- The two possible signs of a nonzero pivot. -/
def minorChartSign (b : Bool) : ℚ := if b then 1 else -1

lemma minorChartSign_ne_zero (b : Bool) : minorChartSign b ≠ 0 := by
  cases b <;> norm_num [minorChartSign]

/-- Zeros of a chart polynomial at pivot `m` among the pairs `(u, v) ∈ crossSet m`
(coordinate box and cross-congruence modulo `m`). -/
def chartPolynomialZeros (B : HypersurfaceChartPolynomial) (m : ℕ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (crossSet m).filter fun uv =>
    eval (Sum.elim (fun i => (uv.2 i : ℚ)) (chartFirstVertex m uv.1)) B = 0

/-- Taking the integer part gives a total decoding map; it is exact on integral patterns. -/
def minorChartDecode (t : Fin 10) (b : Bool) (m : ℕ)
    (uv : (Fin 3 → ℤ) × (Fin 3 → ℤ)) (j : Fin 10) : ℤ :=
  ⌊minorChartPoint t (minorChartSign b * m)
    (fun i => (uv.1 i : ℚ)) (fun i => (uv.2 i : ℚ)) j⌋

lemma chartFirstVertex_eq_cons (m : ℕ) (u : Fin 3 → ℤ) :
    chartFirstVertex m u = Fin.cons (m : ℚ) (fun i => (u i : ℚ)) := by
  funext i
  fin_cases i <;> rfl

lemma pivot_signed_natAbs (p : Fin 10 → ℤ) :
    (p (piv p) : ℚ) = minorChartSign (decide (0 < p (piv p))) * (p (piv p)).natAbs := by
  by_cases h : 0 < p (piv p)
  · simp only [h, decide_true, minorChartSign, ite_true, one_mul]
    have he := Int.natCast_natAbs (p (piv p))
    rw [abs_of_pos h] at he
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he.symm
  · simp only [h, decide_false, minorChartSign, Bool.false_eq_true, ite_false, neg_mul,
      one_mul]
    have he := Int.natCast_natAbs (p (piv p))
    rw [abs_of_nonpos (by omega)] at he
    exact_mod_cast (by omega : p (piv p) = -((p (piv p)).natAbs : ℤ))

/-- The chart coordinates at the maximal pivot `t` lie in `crossSet |p t|`. -/
lemma pivot_chart_crossSet {p : Fin 10 → ℤ} (hp : PluckerRel p) :
    (uVec p (piv p), vVec p (piv p)) ∈ crossSet (p (piv p)).natAbs := by
  let t := piv p
  have hu : ∀ i, |uVec p t i| ≤ |p t| := by
    intro i
    have hs := (sign_sq t i).1
    have hs' : |puS t i| = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hs with h | h <;> simp [h]
    simpa [uVec, abs_mul, hs'] using piv_max p (puX t i)
  have hv : ∀ i, |vVec p t i| ≤ |p t| := by
    intro i
    have hs := (sign_sq t i).2.1
    have hs' : |pvS t i| = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hs with h | h <;> simp [h]
    simpa [vVec, abs_mul, hs'] using piv_max p (pvX t i)
  refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    apply mem_Icc.mpr
    rw [Int.natCast_natAbs]
    exact abs_le.mp (hu i)
  · apply Fintype.mem_piFinset.mpr
    intro i
    apply mem_Icc.mpr
    rw [Int.natCast_natAbs]
    exact abs_le.mp (hv i)
  · intro i
    rw [Int.natCast_natAbs]
    apply (abs_dvd _ _).mpr
    refine ⟨pwS t i * p (pwX t i), ?_⟩
    have h1 := hp t i
    have h2 := (sign_sq t i).2.2
    linear_combination (-pwS t i) * h1 - (uVec p t ⨯₃ vVec p t) i * h2

/-- Decoding the chart coordinates at the maximal pivot recovers `p`. -/
lemma minorChartDecode_pivot {p : Fin 10 → ℤ} (hp : PluckerRel p)
    (ht : p (piv p) ≠ 0) :
    minorChartDecode (piv p) (decide (0 < p (piv p))) (p (piv p)).natAbs
      (uVec p (piv p), vVec p (piv p)) = p := by
  have he := minorChartPoint_reconstruct (pluckerRel_intCast hp) (piv p)
    (by exact_mod_cast ht)
  have hu : (fun i => (uVec p (piv p) i : ℚ)) = uVec (fun j => (p j : ℚ)) (piv p) := by
    funext i
    simp [uVec]
  have hv : (fun i => (vVec p (piv p) i : ℚ)) = vVec (fun j => (p j : ℚ)) (piv p) := by
    funext i
    simp [vVec]
  funext j
  dsimp only [minorChartDecode, Prod.fst, Prod.snd]
  rw [← pivot_signed_natAbs, hu, hv, he]
  simp

/-- A proper polynomial has nonzero equations in all twenty signed pivot charts. -/
theorem exists_minorChart_equations {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) :
    ∃ B : Fin 10 → Bool → HypersurfaceChartPolynomial,
      (∀ t b, B t b ≠ 0) ∧
      ∀ p : Fin 10 → ℤ, PluckerRel p → p (piv p) ≠ 0 →
        eval (fun j => (p j : ℚ)) F = 0 →
        (uVec p (piv p), vVec p (piv p)) ∈
          chartPolynomialZeros (B (piv p) (decide (0 < p (piv p)))) (p (piv p)).natAbs := by
  have hx := fun t b => exists_minorChart_polynomial hF t (minorChartSign b)
    (minorChartSign_ne_zero b)
  choose B hB0 hB using hx
  refine ⟨B, hB0, ?_⟩
  intro p hp ht hFzero
  refine mem_filter.mpr ⟨pivot_chart_crossSet hp, ?_⟩
  rw [chartFirstVertex_eq_cons]
  exact hB (piv p) (decide (0 < p (piv p))) p hp ht hFzero _ (pivot_signed_natAbs p)

/-- Plücker vectors of height at most `X` whose chart coordinates at the maximal pivot
are zeros of the signed chart polynomials number at most the sum of the chart zero
counts over all pivots, both signs and `1 ≤ m ≤ X`. Non-primitive vectors are included. -/
theorem minor_patterns_card_le_chart_sum (B : Fin 10 → Bool → HypersurfaceChartPolynomial)
    {S : Finset (Fin 10 → ℤ)} {X : ℕ}
    (hS : ∀ p ∈ S, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0 ∧
      (uVec p (piv p), vVec p (piv p)) ∈
        chartPolynomialZeros (B (piv p) (decide (0 < p (piv p)))) (p (piv p)).natAbs) :
    (S.card : ℝ) ≤ ∑ t : Fin 10, ∑ b : Bool, ∑ m ∈ Icc 1 X,
      ((chartPolynomialZeros (B t b) m).card : ℝ) := by
  classical
  let U : Finset (Fin 10 → ℤ) := univ.biUnion fun t : Fin 10 =>
    univ.biUnion fun b : Bool => (Icc 1 X).biUnion fun m =>
      (chartPolynomialZeros (B t b) m).image (minorChartDecode t b m)
  have hcover : S ⊆ U := by
    intro p hp
    obtain ⟨hb, hpl, ht, hz⟩ := hS p hp
    have hm1 : 1 ≤ (p (piv p)).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ht)
    have hmX : (p (piv p)).natAbs ≤ X := by
      have h := hb (piv p)
      rw [← Int.natCast_natAbs] at h
      exact_mod_cast h
    refine mem_biUnion.mpr ⟨piv p, mem_univ _, mem_biUnion.mpr
      ⟨decide (0 < p (piv p)), mem_univ _, mem_biUnion.mpr
      ⟨(p (piv p)).natAbs, mem_Icc.mpr ⟨hm1, hmX⟩, ?_⟩⟩⟩
    exact mem_image.mpr ⟨(uVec p (piv p), vVec p (piv p)), hz,
      minorChartDecode_pivot hpl ht⟩
  have hcard : S.card ≤ ∑ t : Fin 10, ∑ b : Bool, ∑ m ∈ Icc 1 X,
      (chartPolynomialZeros (B t b) m).card := by
    apply (card_le_card hcover).trans
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro t _
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro b _
    apply card_biUnion_le.trans
    exact sum_le_sum fun m _ => card_image_le
  exact_mod_cast hcard

end
end PierceLengthBound.FixedDividend
