/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-!
# Reduced bases of lattices in `ℤ³`

Let `Λ ⊆ ℤ³` be a subgroup containing `mℤ³` for some `m ≥ 1`. Let `I` be the least nonzero
`|det(b₁, b₂, b₃)|` over triples in `Λ`. Every triple attaining `I` is a basis: every `w ∈ Λ`
has integer Cramer coordinates (`basis_of_min`). Among such bases, minimise `d₁ = |b₁|²` and
then `d₂ = |b₁|²|b₂|² - ⟨b₁, b₂⟩²`. Swapping and shearing the minimiser give `3d₁² ≤ 4d₂` and
`3d₂² ≤ 4d₁I²`, and size reduction then gives a basis with
`27 |b₁|²|b₂|²|b₃|² ≤ 64 I²` (`reduced_basis`). So every `w ∈ Λ` has coordinates with
`27 |bᵢ|² yᵢ² ≤ 64 |w|²` (`reduced_coords`).

Everything is integer arithmetic. No real numbers or geometry of numbers are needed.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- The dot product on `ℤ³`. -/
def dot3 (x y : Fin 3 → ℤ) : ℤ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- The squared length. -/
def nrm3 (x : Fin 3 → ℤ) : ℤ := dot3 x x

/-- The determinant of three vectors. -/
def det3 (x y z : Fin 3 → ℤ) : ℤ :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

/-- The Gram determinant of two vectors. -/
def gram2 (x y : Fin 3 → ℤ) : ℤ := nrm3 x * nrm3 y - dot3 x y ^ 2

lemma nrm3_nonneg (x : Fin 3 → ℤ) : 0 ≤ nrm3 x := by
  unfold nrm3 dot3; nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_self_nonneg (x 2)]

lemma nrm3_eq_zero {x : Fin 3 → ℤ} (h : nrm3 x = 0) : x = 0 := by
  unfold nrm3 dot3 at h
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  funext j; fin_cases j <;> simp [h0, h1, h2]

lemma det3_zero_left (y z : Fin 3 → ℤ) : det3 0 y z = 0 := by simp [det3]

/-- Lagrange: `|x|²|y|² - ⟨x,y⟩² = |x × y|² ≥ 0`. -/
lemma gram2_nonneg (x y : Fin 3 → ℤ) : 0 ≤ gram2 x y := by
  have : gram2 x y = (x 1 * y 2 - x 2 * y 1) ^ 2 + (x 2 * y 0 - x 0 * y 2) ^ 2 +
      (x 0 * y 1 - x 1 * y 0) ^ 2 := by unfold gram2 nrm3 dot3; ring
  rw [this]; positivity

/-- Hadamard's inequality in `ℤ³`. -/
lemma det3_sq_le (x y z : Fin 3 → ℤ) : det3 x y z ^ 2 ≤ nrm3 x * nrm3 y * nrm3 z := by
  set c0 := y 1 * z 2 - y 2 * z 1
  set c1 := y 2 * z 0 - y 0 * z 2
  set c2 := y 0 * z 1 - y 1 * z 0
  have hd : det3 x y z = x 0 * c0 + x 1 * c1 + x 2 * c2 := by simp only [det3, c0, c1, c2]; ring
  have hc : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = gram2 y z := by
    simp only [c0, c1, c2, gram2, nrm3, dot3]; ring
  have hcs : (x 0 * c0 + x 1 * c1 + x 2 * c2) ^ 2 ≤ nrm3 x * (c0 ^ 2 + c1 ^ 2 + c2 ^ 2) := by
    have : nrm3 x * (c0 ^ 2 + c1 ^ 2 + c2 ^ 2) - (x 0 * c0 + x 1 * c1 + x 2 * c2) ^ 2 =
        (x 1 * c2 - x 2 * c1) ^ 2 + (x 2 * c0 - x 0 * c2) ^ 2 + (x 0 * c1 - x 1 * c0) ^ 2 := by
      unfold nrm3 dot3; ring
    nlinarith [sq_nonneg (x 1 * c2 - x 2 * c1), sq_nonneg (x 2 * c0 - x 0 * c2),
      sq_nonneg (x 0 * c1 - x 1 * c0)]
  have hg : gram2 y z ≤ nrm3 y * nrm3 z := by unfold gram2; nlinarith [sq_nonneg (dot3 y z)]
  rw [hd]
  calc _ ≤ nrm3 x * (c0 ^ 2 + c1 ^ 2 + c2 ^ 2) := hcs
    _ = nrm3 x * gram2 y z := by rw [hc]
    _ ≤ nrm3 x * (nrm3 y * nrm3 z) := mul_le_mul_of_nonneg_left hg (nrm3_nonneg x)
    _ = _ := by ring

/-- Cramer's rule. -/
lemma cramer (b1 b2 b3 w : Fin 3 → ℤ) :
    det3 b1 b2 b3 • w = det3 w b2 b3 • b1 + det3 b1 w b3 • b2 + det3 b1 b2 w • b3 := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, det3]
  fin_cases j <;> simp <;> ring

/-- A determinant vanishes if the Gram determinant of two of its vectors does. -/
lemma det3_eq_zero_of_gram {x y z : Fin 3 → ℤ} (h : gram2 x y = 0) : det3 x y z = 0 := by
  have e : gram2 x y = (x 1 * y 2 - x 2 * y 1) ^ 2 + (x 2 * y 0 - x 0 * y 2) ^ 2 +
      (x 0 * y 1 - x 1 * y 0) ^ 2 := by unfold gram2 nrm3 dot3; ring
  rw [e] at h
  have h0 : x 1 * y 2 - x 2 * y 1 = 0 := by
    nlinarith [sq_nonneg (x 1 * y 2 - x 2 * y 1), sq_nonneg (x 2 * y 0 - x 0 * y 2),
      sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have h1 : x 2 * y 0 - x 0 * y 2 = 0 := by
    nlinarith [sq_nonneg (x 1 * y 2 - x 2 * y 1), sq_nonneg (x 2 * y 0 - x 0 * y 2),
      sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have h2 : x 0 * y 1 - x 1 * y 0 = 0 := by
    nlinarith [sq_nonneg (x 1 * y 2 - x 2 * y 1), sq_nonneg (x 2 * y 0 - x 0 * y 2),
      sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have : det3 x y z = z 0 * (x 1 * y 2 - x 2 * y 1) + z 1 * (x 2 * y 0 - x 0 * y 2) +
      z 2 * (x 0 * y 1 - x 1 * y 0) := by unfold det3; ring
  rw [this, h0, h1, h2]; ring

/-- Rounding: some `n` has `|2(s + n d)| ≤ d`. -/
lemma exists_round (s d : ℤ) (hd : 0 < d) : ∃ n : ℤ, (2 * (s + n * d)) ^ 2 ≤ d ^ 2 := by
  have e := Int.emod_add_mul_ediv s d
  have h0 := Int.emod_nonneg s hd.ne'
  have h1 := Int.emod_lt_of_pos s hd
  by_cases h : 2 * (s % d) ≤ d
  · refine ⟨-(s / d), ?_⟩
    have : s + -(s / d) * d = s % d := by linarith [mul_comm d (s / d)]
    rw [this]; nlinarith
  · refine ⟨-(s / d) - 1, ?_⟩
    have : s + (-(s / d) - 1) * d = s % d - d := by linarith [mul_comm d (s / d)]
    rw [this]; nlinarith

/-- Arithmetic for the second vector. -/
lemma red_arith2 {d1 d2 N t : ℤ} (hA : 3 * d1 ^ 2 ≤ 4 * d2) (i : d1 * N = d2 + t ^ 2)
    (ht : 4 * t ^ 2 ≤ d1 ^ 2) : 3 * (d1 * N) ≤ 4 * d2 := by
  linarith

/-- Arithmetic for the third vector. -/
lemma red_arith3 {d1 d2 D2 N G t u : ℤ} (hd1 : 0 < d1) (hd2 : 0 ≤ d2) (hA : 3 * d1 ^ 2 ≤ 4 * d2)
    (hB : 3 * d2 ^ 2 ≤ 4 * d1 * D2) (iC : d1 * N = G + u ^ 2) (iB : d2 * G = t ^ 2 + d1 * D2)
    (ht : 4 * t ^ 2 ≤ d2 ^ 2) (hu : 4 * u ^ 2 ≤ d1 ^ 2) : 9 * (d2 * N) ≤ 16 * D2 := by
  have h1 : d1 * (d2 * N) = t ^ 2 + d1 * D2 + d2 * u ^ 2 := by linear_combination d2 * iC + iB
  have h2 : d2 * (4 * u ^ 2) ≤ d2 * d1 ^ 2 := mul_le_mul_of_nonneg_left hu hd2
  have h3 : d2 * (3 * d1 ^ 2) ≤ d2 * (4 * d2) := mul_le_mul_of_nonneg_left hA hd2
  have h4 : d1 * (9 * (d2 * N)) ≤ d1 * (16 * D2) := by linarith
  exact le_of_mul_le_mul_left h4 hd1

/-- The product bound. -/
lemma red_arith_fin {d1 d2 D2 N2 N3 : ℤ} (hd2 : 0 < d2) (h3 : 0 ≤ N3)
    (L2 : 3 * (d1 * N2) ≤ 4 * d2) (L3 : 9 * (d2 * N3) ≤ 16 * D2) :
    27 * (d1 * N2 * N3) ≤ 64 * D2 := by
  have hdN : 0 ≤ d2 * N3 := mul_nonneg hd2.le h3
  have : (3 * (d1 * N2)) * (9 * (d2 * N3)) ≤ (4 * d2) * (16 * D2) :=
    mul_le_mul L2 L3 (by positivity) (by positivity)
  have : d2 * (27 * (d1 * N2 * N3)) ≤ d2 * (64 * D2) := by linarith
  exact le_of_mul_le_mul_left this hd2

section Lattice

variable (Λ : AddSubgroup (Fin 3 → ℤ))

/-- `Λ` has a triple of nonzero determinant of absolute value `n`. -/
def HasTri (n : ℕ) : Prop :=
  0 < n ∧ ∃ b1 ∈ Λ, ∃ b2 ∈ Λ, ∃ b3 ∈ Λ, (det3 b1 b2 b3).natAbs = n

lemma hasTri_of {m : ℕ} (hm : 0 < m) (hΛ : ∀ x : Fin 3 → ℤ, (∀ j, (m : ℤ) ∣ x j) → x ∈ Λ) :
    HasTri Λ (m ^ 3) := by
  refine ⟨by positivity, ![(m : ℤ), 0, 0], hΛ _ fun j => ?_, ![0, (m : ℤ), 0], hΛ _ fun j => ?_,
    ![0, 0, (m : ℤ)], hΛ _ fun j => ?_, ?_⟩
  · fin_cases j <;> simp
  · fin_cases j <;> simp
  · fin_cases j <;> simp
  · simp [det3]; ring_nf; simp [Int.natAbs_pow]

/-- The minimal determinant triples with a given value of `|b₁|²`. -/
def MinTri (I : ℕ) (b1 b2 b3 : Fin 3 → ℤ) : Prop :=
  b1 ∈ Λ ∧ b2 ∈ Λ ∧ b3 ∈ Λ ∧ (det3 b1 b2 b3).natAbs = I

variable {Λ}

/-- **Minimal triples are bases** (first slot). -/
lemma dvd_det_of_min {I : ℕ} (hI : ∀ n, n < I → ¬ HasTri Λ n) {b1 b2 b3 : Fin 3 → ℤ}
    (h1 : b1 ∈ Λ) (h2 : b2 ∈ Λ) (h3 : b3 ∈ Λ) (hdet : (det3 b1 b2 b3).natAbs = I) (hI0 : 0 < I)
    {w : Fin 3 → ℤ} (hw : w ∈ Λ) : det3 b1 b2 b3 ∣ det3 w b2 b3 := by
  set D := det3 b1 b2 b3
  have hD : D ≠ 0 := by intro h; rw [h] at hdet; simp at hdet; omega
  set c := det3 w b2 b3
  set q := c / D
  set r := c % D
  have hr0 : 0 ≤ r := Int.emod_nonneg c hD
  have hrl : r < |D| := by
    have := Int.emod_lt c hD; rwa [Int.natCast_natAbs] at this
  have hw' : w - q • b1 ∈ Λ := sub_mem hw (zsmul_mem h1 q)
  have hdr : det3 (w - q • b1) b2 b3 = r := by
    have e := Int.emod_add_mul_ediv c D
    have : det3 (w - q • b1) b2 b3 = c - q * D := by
      simp only [c, D, det3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; linarith [mul_comm D q]
  by_contra hndvd
  have hr : r ≠ 0 := fun h => hndvd (Int.dvd_of_emod_eq_zero h)
  apply hI r.natAbs (by
    have : (r.natAbs : ℤ) < (I : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg hr0, ← hdet, Int.natCast_natAbs]; exact hrl
    exact_mod_cast this)
  exact ⟨Int.natAbs_pos.mpr hr, _, hw', b2, h2, b3, h3, by rw [hdr]⟩

/-- **Minimal triples are bases.** -/
lemma basis_of_min {I : ℕ} (hI : ∀ n, n < I → ¬ HasTri Λ n) {b1 b2 b3 : Fin 3 → ℤ}
    (h1 : b1 ∈ Λ) (h2 : b2 ∈ Λ) (h3 : b3 ∈ Λ) (hdet : (det3 b1 b2 b3).natAbs = I) (hI0 : 0 < I)
    {w : Fin 3 → ℤ} (hw : w ∈ Λ) :
    det3 b1 b2 b3 ∣ det3 w b2 b3 ∧ det3 b1 b2 b3 ∣ det3 b1 w b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 b2 w := by
  refine ⟨dvd_det_of_min hI h1 h2 h3 hdet hI0 hw, ?_, ?_⟩
  · have e1 : det3 b2 b1 b3 = -det3 b1 b2 b3 := by unfold det3; ring
    have e2 : det3 w b1 b3 = -det3 b1 w b3 := by unfold det3; ring
    have := dvd_det_of_min hI h2 h1 h3 (by rw [e1, Int.natAbs_neg]; exact hdet) hI0 hw
    rw [e1, e2] at this
    exact dvd_neg.mp (neg_dvd.mp this)
  · have e1 : det3 b3 b2 b1 = -det3 b1 b2 b3 := by unfold det3; ring
    have e2 : det3 w b2 b1 = -det3 b1 b2 w := by unfold det3; ring
    have := dvd_det_of_min hI h3 h2 h1 (by rw [e1, Int.natAbs_neg]; exact hdet) hI0 hw
    rw [e1, e2] at this
    exact dvd_neg.mp (neg_dvd.mp this)

/-- **The reduced basis.** -/
theorem reduced_basis {m : ℕ} (hm : 0 < m)
    (hΛ : ∀ x : Fin 3 → ℤ, (∀ j, (m : ℤ) ∣ x j) → x ∈ Λ) :
    ∃ b1 b2 b3 : Fin 3 → ℤ, b1 ∈ Λ ∧ b2 ∈ Λ ∧ b3 ∈ Λ ∧ det3 b1 b2 b3 ≠ 0 ∧
      (det3 b1 b2 b3).natAbs ≤ m ^ 3 ∧
      (∀ w ∈ Λ, det3 b1 b2 b3 ∣ det3 w b2 b3 ∧ det3 b1 b2 b3 ∣ det3 b1 w b3 ∧
        det3 b1 b2 b3 ∣ det3 b1 b2 w) ∧
      27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2 := by
  classical
  have hex : ∃ n, HasTri Λ n := ⟨_, hasTri_of Λ hm hΛ⟩
  set I := Nat.find hex with hIdef
  have hIspec : HasTri Λ I := Nat.find_spec hex
  have hImin : ∀ n, n < I → ¬ HasTri Λ n := fun n hn => Nat.find_min hex hn
  have hIm : I ≤ m ^ 3 := Nat.find_min' hex (hasTri_of Λ hm hΛ)
  have hI0 : 0 < I := hIspec.1
  -- minimise `|b₁|²`
  have hex1 : ∃ n : ℕ, ∃ b1 b2 b3, MinTri Λ I b1 b2 b3 ∧ (nrm3 b1).toNat = n := by
    obtain ⟨-, b1, h1, b2, h2, b3, h3, hd⟩ := hIspec
    exact ⟨_, b1, b2, b3, ⟨h1, h2, h3, hd⟩, rfl⟩
  set d1n := Nat.find hex1
  obtain ⟨c1, c2, c3, hc, hcd⟩ := Nat.find_spec hex1
  have hd1min : ∀ b1 b2 b3, MinTri Λ I b1 b2 b3 → (d1n : ℤ) ≤ nrm3 b1 := by
    intro b1 b2 b3 hb
    have := Nat.find_min' hex1 ⟨b1, b2, b3, hb, rfl⟩
    have h0 := nrm3_nonneg b1
    omega
  -- then minimise the Gram determinant
  have hex2 : ∃ n : ℕ, ∃ b1 b2 b3, MinTri Λ I b1 b2 b3 ∧ (nrm3 b1).toNat = d1n ∧
      (gram2 b1 b2).toNat = n := ⟨_, c1, c2, c3, hc, hcd, rfl⟩
  set d2n := Nat.find hex2
  obtain ⟨b1, b2, b3, hb, hbd1, hbd2⟩ := Nat.find_spec hex2
  have hd2min : ∀ b2' b3', MinTri Λ I b1 b2' b3' → (d2n : ℤ) ≤ gram2 b1 b2' := by
    intro b2' b3' hb'
    have := Nat.find_min' hex2 ⟨b1, b2', b3', hb', hbd1, rfl⟩
    have h0 := gram2_nonneg b1 b2'
    omega
  obtain ⟨h1, h2, h3, hdet⟩ := hb
  set D := det3 b1 b2 b3 with hDdef
  have hD : D ≠ 0 := by intro h; rw [h] at hdet; simp at hdet; omega
  set d1 := nrm3 b1 with hd1def
  set d2 := gram2 b1 b2 with hd2def
  have e1 : (d1n : ℤ) = d1 := by rw [← hbd1]; exact Int.toNat_of_nonneg (nrm3_nonneg _)
  have e2 : (d2n : ℤ) = d2 := by
    rw [show d2n = d2.toNat from hbd2.symm]; exact Int.toNat_of_nonneg (gram2_nonneg _ _)
  have hd1pos : 0 < d1 := by
    rcases (nrm3_nonneg b1).lt_or_eq with h | h
    · exact h
    · exfalso; apply hD; rw [hDdef, nrm3_eq_zero h.symm, det3_zero_left]
  have hd2pos : 0 < d2 := by
    rcases (gram2_nonneg b1 b2).lt_or_eq with h | h
    · exact h
    · exfalso; exact hD (det3_eq_zero_of_gram h.symm)
  have hD2 : 0 < D ^ 2 := by positivity
  -- inequality A: swap after shearing
  set s := dot3 b1 b2
  obtain ⟨n, hn⟩ := exists_round s d1 hd1pos
  set b2' := b2 + n • b1
  have hb2' : b2' ∈ Λ := add_mem h2 (zsmul_mem h1 n)
  have iA : d1 * nrm3 b2' = d2 + (s + n * d1) ^ 2 := by
    simp only [b2', d1, d2, s, gram2, nrm3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hA0 : d1 ≤ nrm3 b2' := by
    have := hd1min b2' b1 b3 ⟨hb2', h1, h3, by
      rw [show det3 b2' b1 b3 = -D by
        simp only [b2', D, det3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring,
        Int.natAbs_neg]; exact hdet⟩
    rw [e1] at this; exact this
  have hA : 3 * d1 ^ 2 ≤ 4 * d2 := by nlinarith
  -- inequality B: shear the third vector, then swap
  set B23 := d1 * dot3 b2 b3 - s * dot3 b1 b3
  obtain ⟨n2, hn2⟩ := exists_round B23 d2 hd2pos
  set c := b3 + n2 • b2
  have hc : c ∈ Λ := add_mem h3 (zsmul_mem h2 n2)
  have iB : d2 * gram2 b1 c = (B23 + n2 * d2) ^ 2 + d1 * D ^ 2 := by
    simp only [c, B23, d1, d2, s, D, gram2, nrm3, dot3, det3, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]; ring
  have hB0 : d2 ≤ gram2 b1 c := by
    have := hd2min c b2 ⟨h1, hc, h2, by
      rw [show det3 b1 c b2 = -D by
        simp only [c, D, det3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring,
        Int.natAbs_neg]; exact hdet⟩
    rw [e2] at this; exact this
  have hB : 3 * d2 ^ 2 ≤ 4 * d1 * D ^ 2 := by
    have : d2 * d2 ≤ d2 * gram2 b1 c := mul_le_mul_of_nonneg_left hB0 hd2pos.le
    nlinarith
  -- size reduction of the third vector against `b₁`
  set s' := dot3 b1 c
  obtain ⟨n1, hn1⟩ := exists_round s' d1 hd1pos
  set b3' := c + n1 • b1
  have hb3' : b3' ∈ Λ := add_mem hc (zsmul_mem h1 n1)
  have iC : d1 * nrm3 b3' = gram2 b1 c + (s' + n1 * d1) ^ 2 := by
    simp only [b3', s', d1, gram2, nrm3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hdet' : det3 b1 b2' b3' = D := by
    simp only [b2', b3', c, D, det3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  -- the length bounds
  have L2 := red_arith2 hA iA (by linarith [hn,
      show (2 * (s + n * d1)) ^ 2 = 4 * (s + n * d1) ^ 2 by ring])
  have L3 := red_arith3 hd1pos hd2pos.le hA hB iC iB
    (by linarith [hn2, show (2 * (B23 + n2 * d2)) ^ 2 = 4 * (B23 + n2 * d2) ^ 2 by ring])
    (by linarith [hn1, show (2 * (s' + n1 * d1)) ^ 2 = 4 * (s' + n1 * d1) ^ 2 by ring])
  have hfin := red_arith_fin hd2pos (nrm3_nonneg b3') L2 L3
  have hdet'' : (det3 b1 b2' b3').natAbs = I := by rw [hdet']; exact hdet
  refine ⟨b1, b2', b3', h1, hb2', hb3', by rw [hdet']; exact hD, by rw [hdet'']; exact hIm,
    fun w hw => basis_of_min hImin h1 hb2' hb3' hdet'' hI0 hw, by rw [hdet']; exact hfin⟩

end Lattice

/-- **Coordinates in a reduced basis.** -/
theorem reduced_coords {b1 b2 b3 w : Fin 3 → ℤ} (hD : det3 b1 b2 b3 ≠ 0)
    (hdvd : det3 b1 b2 b3 ∣ det3 w b2 b3 ∧ det3 b1 b2 b3 ∣ det3 b1 w b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 b2 w)
    (hred : 27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2) :
    ∃ y : Fin 3 → ℤ, w = y 0 • b1 + y 1 • b2 + y 2 • b3 ∧
      27 * (nrm3 b1 * y 0 ^ 2) ≤ 64 * nrm3 w ∧ 27 * (nrm3 b2 * y 1 ^ 2) ≤ 64 * nrm3 w ∧
      27 * (nrm3 b3 * y 2 ^ 2) ≤ 64 * nrm3 w := by
  set D := det3 b1 b2 b3
  obtain ⟨⟨y0, hy0⟩, ⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ := hdvd
  have hD2 : 0 < D ^ 2 := by positivity
  have hcr := cramer b1 b2 b3 w
  rw [hy0, hy1, hy2] at hcr
  have n1 := nrm3_nonneg b1
  have n2 := nrm3_nonneg b2
  have n3 := nrm3_nonneg b3
  have nw := nrm3_nonneg w
  refine ⟨![y0, y1, y2], ?_, ?_, ?_, ?_⟩
  · funext j
    have := congrFun hcr j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    apply mul_left_cancel₀ hD
    linear_combination this
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  · have h := det3_sq_le w b2 b3
    rw [hy0] at h
    have : D ^ 2 * (27 * (nrm3 b1 * y0 ^ 2)) ≤ D ^ 2 * (64 * nrm3 w) := by
      have := mul_le_mul_of_nonneg_left h (show 0 ≤ 27 * nrm3 b1 by positivity)
      have := mul_le_mul_of_nonneg_left hred nw
      nlinarith
    exact le_of_mul_le_mul_left this hD2
  · have h := det3_sq_le w b1 b3
    have e : det3 w b1 b3 = -(D * y1) := by rw [← hy1]; unfold det3; ring
    rw [e, neg_sq] at h
    have : D ^ 2 * (27 * (nrm3 b2 * y1 ^ 2)) ≤ D ^ 2 * (64 * nrm3 w) := by
      have := mul_le_mul_of_nonneg_left h (show 0 ≤ 27 * nrm3 b2 by positivity)
      have := mul_le_mul_of_nonneg_left hred nw
      nlinarith
    exact le_of_mul_le_mul_left this hD2
  · have h := det3_sq_le w b1 b2
    have e : det3 w b1 b2 = D * y2 := by rw [← hy2]; unfold det3; ring
    rw [e] at h
    have : D ^ 2 * (27 * (nrm3 b3 * y2 ^ 2)) ≤ D ^ 2 * (64 * nrm3 w) := by
      have := mul_le_mul_of_nonneg_left h (show 0 ≤ 27 * nrm3 b3 by positivity)
      have := mul_le_mul_of_nonneg_left hred nw
      nlinarith
    exact le_of_mul_le_mul_left this hD2

end PierceLengthBound
