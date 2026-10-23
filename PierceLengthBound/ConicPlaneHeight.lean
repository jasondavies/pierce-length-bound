/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendHyperplaneDegree

/-! Explicit bounded-height integer planes through three bounded integer points.
The construction includes collinear triples. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset
open scoped Matrix
open Matrix (vec3_dotProduct)
noncomputable section

/-- A bounded nonzero integer normal perpendicular to two bounded vectors. -/
theorem bounded_common_normal {u v : Fin 3 → ℤ} {B : ℕ} (hB : 1 ≤ B) (hu : u ≠ 0)
    (hub : ∀ j, |u j| ≤ B) (hvb : ∀ j, |v j| ≤ B) :
    ∃ n : Fin 3 → ℤ, n ≠ 0 ∧ (∀ j, |n j| ≤ 2 * (B : ℤ) ^ 2) ∧
      n ⬝ᵥ u = 0 ∧ n ⬝ᵥ v = 0 := by
  by_cases hc : u ⨯₃ v = 0
  · have hc0 := congrFun hc 0
    have hc1 := congrFun hc 1
    have hc2 := congrFun hc 2
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two, Pi.zero_apply] at hc0 hc1 hc2
    have hsmall (j : Fin 3) : |u j| ≤ 2 * (B : ℤ) ^ 2 := by
      have hb : (1 : ℤ) ≤ B := by exact_mod_cast hB
      nlinarith [hub j]
    by_cases h0 : u 0 = 0
    · by_cases h1 : u 1 = 0
      · have h2 : u 2 ≠ 0 := by
          intro h2
          apply hu
          funext j
          fin_cases j <;> assumption
        refine ⟨![u 2, 0, 0], ?_, ?_, ?_, ?_⟩
        · intro he; exact h2 (congrFun he 0)
        · intro j; fin_cases j <;> norm_num; exact hsmall 2
        · rw [vec3_dotProduct]; simp [h0]
        · rw [vec3_dotProduct]; simpa [h0] using hc1
      · refine ⟨![0, -u 2, u 1], ?_, ?_, ?_, ?_⟩
        · intro he; exact h1 (congrFun he 2)
        · intro j; fin_cases j <;> norm_num <;> first | exact hsmall 1 | exact hsmall 2
        · rw [vec3_dotProduct]; simp; ring
        · rw [vec3_dotProduct]; simp; linear_combination hc0
    · refine ⟨![-u 1, u 0, 0], ?_, ?_, ?_, ?_⟩
      · intro he; exact h0 (congrFun he 1)
      · intro j; fin_cases j <;> norm_num <;> first | exact hsmall 0 | exact hsmall 1
      · rw [vec3_dotProduct]; simp; ring
      · rw [vec3_dotProduct]; simp; linear_combination hc2
  · refine ⟨u ⨯₃ v, hc, ?_, ?_, ?_⟩
    · intro j
      calc |(u ⨯₃ v) j| ≤ |u (j + 1) * v (j + 2)| + |u (j + 2) * v (j + 1)| := by
            simpa only [cross_apply_cyc, sub_zero, zero_sub, abs_neg] using
              abs_sub_le (u (j + 1) * v (j + 2)) 0 (u (j + 2) * v (j + 1))
        _ = |u (j + 1)| * |v (j + 2)| + |u (j + 2)| * |v (j + 1)| := by rw [abs_mul, abs_mul]
        _ ≤ (B : ℤ) * B + (B : ℤ) * B := by gcongr <;> first | exact hub _ | exact hvb _
        _ = _ := by ring
    · rw [dotProduct_comm, dot_self_cross]
    · rw [dotProduct_comm, dot_cross_self]

/-- Three bounded integer points, the first two distinct, admit an integer plane
with normal height at most `8H²` and constant coefficient at most `24H³`. -/
theorem three_points_integer_plane_height {z : Fin 3 → Fin 3 → ℤ} {H : ℕ}
    (hH : 1 ≤ H) (hz : z 1 ≠ z 0) (hb : ∀ i j, |z i j| ≤ H) :
    ∃ (n : Fin 3 → ℤ) (c : ℤ), n ≠ 0 ∧ (∀ j, |n j| ≤ 8 * (H : ℤ) ^ 2) ∧
      |c| ≤ 24 * (H : ℤ) ^ 3 ∧ ∀ i, n ⬝ᵥ z i + c = 0 := by
  let u := z 1 - z 0
  let v := z 2 - z 0
  have hu : u ≠ 0 := sub_ne_zero.mpr hz
  have huv (i : Fin 3) : ∀ j, |z i j - z 0 j| ≤ (2 * H : ℕ) := by
    intro j
    have ht := abs_sub_le (z i j) 0 (z 0 j)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    have hi := hb i j
    have h0 := hb 0 j
    push_cast
    linarith
  obtain ⟨n, hn, hnb, hnu, hnv⟩ := bounded_common_normal (by omega : 1 ≤ 2 * H) hu
    (huv 1) (huv 2)
  have hnH (j : Fin 3) : |n j| ≤ 8 * (H : ℤ) ^ 2 := by
    have h := hnb j
    push_cast at h
    nlinarith
  refine ⟨n, -(n ⬝ᵥ z 0), hn, hnH, ?_, ?_⟩
  · rw [abs_neg]
    have hs (j : Fin 3) : |n j * z 0 j| ≤ 8 * (H : ℤ) ^ 3 := by
      calc |n j * z 0 j| = |n j| * |z 0 j| := abs_mul ..
        _ ≤ (8 * (H : ℤ) ^ 2) * H := by gcongr; exacts [hnH j, hb 0 j]
        _ = _ := by ring
    have h1 := abs_add_le (n 0 * z 0 0 + n 1 * z 0 1) (n 2 * z 0 2)
    have h2 := abs_add_le (n 0 * z 0 0) (n 1 * z 0 1)
    rw [vec3_dotProduct]
    linarith [hs 0, hs 1, hs 2]
  · intro i
    fin_cases i
    · simp
    · change n ⬝ᵥ z 1 - n ⬝ᵥ z 0 = 0
      simp only [vec3_dotProduct, u, Pi.sub_apply] at hnu ⊢
      linear_combination hnu
    · change n ⬝ᵥ z 2 - n ⬝ᵥ z 0 = 0
      simp only [vec3_dotProduct] at hnv ⊢
      linear_combination hnv

/-- A plane with integer coefficients, viewed over the curve-counting field. -/
def integerPlanePolynomial (n : Fin 3 → ℤ) (c : ℤ) : MvPolynomial (Fin 3) ℚ :=
  MvPolynomial.C (c : ℚ) + ∑ j, MvPolynomial.C (n j : ℚ) * MvPolynomial.X j

lemma integerPlanePolynomial_degree_le (n : Fin 3 → ℤ) (c : ℤ) :
    (integerPlanePolynomial n c).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp only [MvPolynomial.totalDegree_C]; omega)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]; omega)

lemma integerPlanePolynomial_eval (n z : Fin 3 → ℤ) (c : ℤ) :
    MvPolynomial.eval (fun j => (z j : ℚ)) (integerPlanePolynomial n c) =
      (n ⬝ᵥ z + c : ℤ) := by
  simp [integerPlanePolynomial, vec3_dotProduct, Fin.sum_univ_three]
  ring

/-- An actual degree-two rational component with three bounded integer points
has a containing integer plane of polynomially bounded coefficient height. -/
theorem degree_two_integer_plane_height
    (p : Ideal (MvPolynomial (Fin 3) ℚ)) [p.IsPrime]
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace p m) : ℤ) = 2 * m + c)
    {z : Fin 3 → Fin 3 → ℤ} {H : ℕ} (hH : 1 ≤ H) (hz : Function.Injective z)
    (hb : ∀ i j, |z i j| ≤ H)
    (hzp : ∀ i, (fun j => (z i j : ℚ)) ∈ coordinateZeroLocus p) :
    ∃ (n : Fin 3 → ℤ) (c : ℤ), n ≠ 0 ∧ (∀ j, |n j| ≤ 8 * (H : ℤ) ^ 2) ∧
      |c| ≤ 24 * (H : ℤ) ^ 3 ∧ integerPlanePolynomial n c ∈ p := by
  obtain ⟨n, c, hn, hnb, hc, hp⟩ := three_points_integer_plane_height hH
    (fun he => (by decide : (1 : Fin 3) ≠ 0) (hz he)) hb
  refine ⟨n, c, hn, hnb, hc, ?_⟩
  have hzi : Function.Injective (fun i j => (z i j : ℚ)) := by
    intro i j he
    apply hz
    funext k
    have hk : (z i k : ℚ) = (z j k : ℚ) := congrFun he k
    exact_mod_cast hk
  apply degree_two_plane_mem_of_three_points p hdegree _ (integerPlanePolynomial_degree_le n c)
    (fun i j => (z i j : ℚ)) hzi hzp
  intro i
  rw [integerPlanePolynomial_eval, hp i, Int.cast_zero]

end
end PierceLengthBound.FixedDividend
