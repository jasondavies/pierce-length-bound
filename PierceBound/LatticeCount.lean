/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
import PierceBound.ShortVec
import PierceBound.TernComp
import PierceBound.ElevenCount
import PierceBound.EightMain

/-!
# Counting gap vectors of one minor vector through its lattice

Fix a minor vector `p` with pivot `τ` and a reduced basis `b₁, b₂, b₃` of `Λ_p`. A state with
minor vector `p` has pivot gaps `k' = ∑ yᵢ bᵢ`. Its five gaps are the matching combination of
the lifted basis vectors, and its gaps `(k₁, k₂, k₃)` are `B̂ y` for an integer matrix `B̂` with
`det B̂ ≠ 0`. So `y` is a zero of the ternary quadratic `F_θ ∘ B̂`, and the reduced basis gives
`λ₁ |yᵢ| ≤ 3H`. After a plane choice the slice count gives at most `(8 ⌊3H/λ₁⌋ + 3)(W + 4)`
gap vectors (`lattice_fiber_count`). Summing over minor vectors gives `pattern_count_lattice`.
-/

namespace PierceBound

open Finset Matrix

/-- The two non-pivot columns. -/
def restc : Fin 10 → Fin 2 → Fin 5 := ![![3, 4], ![2, 4], ![2, 3], ![1, 4], ![1, 3], ![1, 2],
  ![0, 4], ![0, 3], ![0, 2], ![0, 1]]

lemma Lrow_rest0 (p : Fin 10 → ℤ) (τ : Fin 10) : Lrow p τ (restc τ 0) = uVec p τ := by
  fin_cases τ <;> rfl

lemma Lrow_rest1 (p : Fin 10 → ℤ) (τ : Fin 10) : Lrow p τ (restc τ 1) = vVec p τ := by
  fin_cases τ <;> rfl

/-- Every entry of a lifting row is at most the pivot. -/
lemma Lrow_abs_le (p : Fin 10 → ℤ) (c : Fin 5) (a : Fin 3) :
    |Lrow p (piv p) c a| ≤ |p (piv p)| := by
  have hu : ∀ a, |uVec p (piv p) a| ≤ |p (piv p)| := fun a => by
    have hs := (sign_sq (piv p) a).1
    have : |puS (piv p) a| = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hs with h | h <;> simp [h]
    simp only [uVec, abs_mul, this, one_mul]; exact piv_max p _
  have hv : ∀ a, |vVec p (piv p) a| ≤ |p (piv p)| := fun a => by
    have hs := (sign_sq (piv p) a).2.1
    have : |pvS (piv p) a| = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hs with h | h <;> simp [h]
    simp only [vVec, abs_mul, this, one_mul]; exact piv_max p _
  unfold Lrow
  generalize role (piv p) c = r
  fin_cases r <;> fin_cases a <;> simp [hu, hv]

/-- The pivot divides every lifting row against a lattice vector. -/
lemma Lrow_dvd {p : Fin 10 → ℤ} {b : Fin 3 → ℤ} (hb : b ∈ pivLat p) (c : Fin 5) :
    p (piv p) ∣ dot3 (Lrow p (piv p) c) b := by
  obtain ⟨hu, hv⟩ := hb
  unfold Lrow
  generalize role (piv p) c = r
  fin_cases r
  · exact ⟨b 0, by simp [dot3]⟩
  · exact ⟨b 1, by simp [dot3]⟩
  · exact ⟨b 2, by simp [dot3]⟩
  · exact hu
  · exact hv

/-- The lift of a lattice vector to five coordinates. -/
noncomputable def liftv (p : Fin 10 → ℤ) (b : Fin 3 → ℤ) (c : Fin 5) : ℤ :=
  dot3 (Lrow p (piv p) c) b / p (piv p)

lemma liftv_spec {p : Fin 10 → ℤ} {b : Fin 3 → ℤ} (hb : b ∈ pivLat p) (c : Fin 5) :
    p (piv p) * liftv p b c = dot3 (Lrow p (piv p) c) b :=
  Int.mul_ediv_cancel' (Lrow_dvd hb c)

/-- `det(L B) = det L · det B`. -/
lemma det3_mul (l1 l2 l3 b1 b2 b3 : Fin 3 → ℤ) :
    (Matrix.of ![![dot3 l1 b1, dot3 l1 b2, dot3 l1 b3], ![dot3 l2 b1, dot3 l2 b2, dot3 l2 b3],
      ![dot3 l3 b1, dot3 l3 b2, dot3 l3 b3]]).det = det3 l1 l2 l3 * det3 b1 b2 b3 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, det_fin_three, Fin.isValue, of_apply, cons_val',
      cons_val_zero, cons_val_fin_one, cons_val_one, Matrix.cons_val]
  unfold det3 dot3; ring

lemma abs_mul_le' {a b A B : ℤ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma abs_add6 (a b c d e f : ℤ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_add_le (a + b + c + d) e
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b) c
  have h5 := abs_add_le a b
  linarith

lemma quadv_bound {c : Fin 10 → ℤ} {v : Fin 3 → ℤ} {K L : ℤ} (hc : ∀ t, |c t| ≤ K)
    (hv : ∀ i, |v i| ≤ L) : |quadv c v| ≤ 6 * K * L ^ 2 := by
  have t : ∀ s i j, |c s * v i * v j| ≤ K * L ^ 2 := fun s i j => by
    have := abs_mul_le' (abs_mul_le' (hc s) (hv i)) (hv j)
    linarith [show K * L * L = K * L ^ 2 by ring]
  have e : quadv c v = c 0 * v 0 * v 0 + c 1 * v 0 * v 1 + c 2 * v 1 * v 1 + c 3 * v 0 * v 2 +
      c 5 * v 1 * v 2 + c 7 * v 2 * v 2 := by unfold quadv; ring
  rw [e]
  have := abs_add6 (c 0 * v 0 * v 0) (c 1 * v 0 * v 1) (c 2 * v 1 * v 1) (c 3 * v 0 * v 2)
    (c 5 * v 1 * v 2) (c 7 * v 2 * v 2)
  linarith [t 0 0 0, t 1 0 1, t 2 1 1, t 3 0 2, t 5 1 2, t 7 2 2]

lemma bilv_bound {c : Fin 10 → ℤ} {v w : Fin 3 → ℤ} {K L : ℤ} (hc : ∀ t, |c t| ≤ K)
    (hv : ∀ i, |v i| ≤ L) (hw : ∀ i, |w i| ≤ L) : |bilv c v w| ≤ 12 * K * L ^ 2 := by
  have t : ∀ s i j, |c s * v i * w j| ≤ K * L ^ 2 := fun s i j => by
    have := abs_mul_le' (abs_mul_le' (hc s) (hv i)) (hw j)
    linarith [show K * L * L = K * L ^ 2 by ring]
  have e : bilv c v w = 2 * (c 0 * v 0 * w 0) + (c 1 * v 0 * w 1 + c 1 * v 1 * w 0) +
      2 * (c 2 * v 1 * w 1) + (c 3 * v 0 * w 2 + c 3 * v 2 * w 0) +
      (c 5 * v 1 * w 2 + c 5 * v 2 * w 1) + 2 * (c 7 * v 2 * w 2) := by unfold bilv; ring
  rw [e]
  have h6 := abs_add6 (2 * (c 0 * v 0 * w 0)) (c 1 * v 0 * w 1 + c 1 * v 1 * w 0)
    (2 * (c 2 * v 1 * w 1)) (c 3 * v 0 * w 2 + c 3 * v 2 * w 0)
    (c 5 * v 1 * w 2 + c 5 * v 2 * w 1) (2 * (c 7 * v 2 * w 2))
  have two : ∀ x : ℤ, |2 * x| = 2 * |x| := fun x => by rw [abs_mul]; norm_num
  rw [two, two, two] at h6
  linarith [t 0 0 0, t 2 1 1, t 7 2 2, abs_add_le (c 1 * v 0 * w 1) (c 1 * v 1 * w 0), t 1 0 1,
    t 1 1 0, abs_add_le (c 3 * v 0 * w 2) (c 3 * v 2 * w 0), t 3 0 2, t 3 2 0,
    abs_add_le (c 5 * v 1 * w 2) (c 5 * v 2 * w 1), t 5 1 2, t 5 2 1]

lemma linv_bound {c : Fin 10 → ℤ} {v : Fin 3 → ℤ} {K L : ℤ} (hc : ∀ t, |c t| ≤ K)
    (hv : ∀ i, |v i| ≤ L) : |linv c v| ≤ 3 * K * L := by
  unfold linv
  have := abs_add_three (c 4 * v 0) (c 6 * v 1) (c 8 * v 2)
  linarith [abs_mul_le' (hc 4) (hv 0), abs_mul_le' (hc 6) (hv 1), abs_mul_le' (hc 8) (hv 2)]

/-- Coefficient bound under substitution. -/
lemma tcomp_bound {c : Fin 10 → ℤ} {C : Matrix (Fin 3) (Fin 3) ℤ} {K L : ℤ}
    (hc : ∀ t, |c t| ≤ K) (hC : ∀ i j, |C i j| ≤ L) (hL : 1 ≤ L) (t : Fin 10) :
    |tcomp c C t| ≤ 12 * K * L ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hc 0)
  have col : ∀ j i, |(fun i => C i j) i| ≤ L := fun j i => hC i j
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have q : ∀ j, |quadv c (fun i => C i j)| ≤ 12 * K * L ^ 2 := fun j => by
    have := quadv_bound hc (col j); nlinarith
  have b : ∀ j k, |bilv c (fun i => C i j) (fun i => C i k)| ≤ 12 * K * L ^ 2 := fun j k =>
    bilv_bound hc (col j) (col k)
  have l : ∀ j, |linv c (fun i => C i j)| ≤ 12 * K * L ^ 2 := fun j => by
    have := linv_bound hc (col j)
    have : 3 * K * L ≤ 12 * K * L ^ 2 := by nlinarith
    linarith
  fin_cases t
  · exact q 0
  · exact b 0 1
  · exact q 1
  · exact b 0 2
  · exact l 0
  · exact b 1 2
  · exact l 1
  · exact q 2
  · exact l 2
  · change |c 9| ≤ _
    have := hc 9
    have : K ≤ 12 * K * L ^ 2 := by nlinarith
    linarith

/-- The coefficients of `F_θ`. -/
def thetaCoef (A A' A'' U V U' V' : ℤ) : Fin 10 → ℤ :=
  ![U * (U + A'), 2 * V * (U + A'), V * (V + A'), 2 * A * (U + A'), A * A'' - A' ^ 2,
    2 * A * (V + A'), A' * U - A * U', A * (A + A'), A' * V - A * V', 0]

lemma ternv_thetaCoef (A A' A'' U V U' V' : ℤ) (v : Fin 3 → ℤ) :
    ternv (thetaCoef A A' A'' U V U' V') v = ternθ A A' A'' U V U' V' (v 0) (v 1) (v 2) := by
  simp [ternv, thetaCoef, ternθ]

lemma disc3_thetaCoef {A A' A'' U V U' V' : ℤ} (hA : 0 < A) (hA' : 0 < A') (hU : 0 < U)
    (hV : V < 0) : disc3 (thetaCoef A A' A'' U V U' V') ≠ 0 := by
  intro h
  have e := lead_eq (thetaCoef A A' A'' U V U' V')
  have e2 : (thetaCoef A A' A'' U V U' V' 1 * thetaCoef A A' A'' U V U' V' 3 -
      2 * thetaCoef A A' A'' U V U' V' 0 * thetaCoef A A' A'' U V U' V' 5) ^ 2 +
      (thetaCoef A A' A'' U V U' V' 1 ^ 2 -
        4 * thetaCoef A A' A'' U V U' V' 0 * thetaCoef A A' A'' U V U' V' 2) *
      (4 * thetaCoef A A' A'' U V U' V' 0 * thetaCoef A A' A'' U V U' V' 7 -
        thetaCoef A A' A'' U V U' V' 3 ^ 2) =
      16 * A * A' ^ 2 * U * (A - V) * (A' + U) ^ 2 * (U - V) := by
    simp [thetaCoef]; ring
  rw [e2, h, mul_zero] at e
  have : 0 < 16 * A * A' ^ 2 * U * (A - V) * (A' + U) ^ 2 * (U - V) := by
    have : 0 < A - V := by linarith
    have : 0 < A' + U := by linarith
    have : 0 < U - V := by linarith
    positivity
  linarith

/-- An entry bound from a length bound. -/
lemma entry_bound {b : Fin 3 → ℤ} {M : ℤ} (hM : 0 ≤ M) (h : 27 * nrm3 b ≤ 64 * (M ^ 3) ^ 2)
    (a : Fin 3) : |b a| ≤ 2 * M ^ 3 := by
  have h1 : b a ^ 2 ≤ nrm3 b := by
    unfold nrm3 dot3
    fin_cases a <;> simp <;> nlinarith [mul_self_nonneg (b 0), mul_self_nonneg (b 1),
      mul_self_nonneg (b 2)]
  have h2 : b a ^ 2 ≤ (2 * M ^ 3) ^ 2 := by nlinarith
  have := sq_le_sq.mp h2
  rwa [abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * M ^ 3)] at this

/-- A bound on the lifted coordinates. -/
lemma liftv_bound {p : Fin 10 → ℤ} {b : Fin 3 → ℤ} (hb : b ∈ pivLat p) (hm : p (piv p) ≠ 0)
    {B : ℤ} (hB : ∀ a, |b a| ≤ B) (c : Fin 5) : |liftv p b c| ≤ 3 * B := by
  have e := liftv_spec hb c
  have hm0 : 0 < |p (piv p)| := abs_pos.mpr hm
  have t : ∀ a, |Lrow p (piv p) c a * b a| ≤ |p (piv p)| * B := fun a =>
    abs_mul_le' (Lrow_abs_le p c a) (hB a)
  have h : |p (piv p)| * |liftv p b c| ≤ |p (piv p)| * (3 * B) := by
    rw [← abs_mul, e]
    unfold dot3
    have := abs_add_three (Lrow p (piv p) c 0 * b 0) (Lrow p (piv p) c 1 * b 1)
      (Lrow p (piv p) c 2 * b 2)
    linarith [t 0, t 1, t 2]
  exact le_of_mul_le_mul_left h hm0

/-- The coordinates of `x` in the basis `b₁, b₂, b₃`, by Cramer's rule. -/
def ycoord (b1 b2 b3 x : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![det3 x b2 b3 / det3 b1 b2 b3, det3 b1 x b3 / det3 b1 b2 b3, det3 b1 b2 x / det3 b1 b2 b3]

/-- **Coordinates in a reduced basis.** If every basis vector has length `≥ R` and `|xₐ| ≤ H`,
then `R |yᵢ| ≤ 3H`. -/
lemma ycoord_spec {b1 b2 b3 x : Fin 3 → ℤ} {R H : ℕ} (hD : det3 b1 b2 b3 ≠ 0)
    (hdvd : det3 b1 b2 b3 ∣ det3 x b2 b3 ∧ det3 b1 b2 b3 ∣ det3 b1 x b3 ∧
      det3 b1 b2 b3 ∣ det3 b1 b2 x)
    (hred : 27 * (nrm3 b1 * nrm3 b2 * nrm3 b3) ≤ 64 * det3 b1 b2 b3 ^ 2) (hR : (0 : ℤ) < R)
    (n1 : (R : ℤ) ^ 2 ≤ nrm3 b1) (n2 : (R : ℤ) ^ 2 ≤ nrm3 b2) (n3 : (R : ℤ) ^ 2 ≤ nrm3 b3)
    (hx : ∀ a, |x a| ≤ H) :
    (∀ j, x j = ycoord b1 b2 b3 x 0 * b1 j + ycoord b1 b2 b3 x 1 * b2 j +
      ycoord b1 b2 b3 x 2 * b3 j) ∧ ∀ i, (R : ℤ) * |ycoord b1 b2 b3 x i| ≤ 3 * H := by
  obtain ⟨y, hy, hy0, hy1, hy2⟩ := reduced_coords hD hdvd hred
  have hyj : ∀ j, x j = y 0 * b1 j + y 1 * b2 j + y 2 * b3 j := fun j => by
    rw [hy]; simp [mul_comm]
  have hyc : ycoord b1 b2 b3 x = y := by
    have d0 : det3 x b2 b3 = y 0 * det3 b1 b2 b3 := by
      simp only [det3]; rw [hyj 0, hyj 1, hyj 2]; ring
    have d1 : det3 b1 x b3 = y 1 * det3 b1 b2 b3 := by
      simp only [det3]; rw [hyj 0, hyj 1, hyj 2]; ring
    have d2 : det3 b1 b2 x = y 2 * det3 b1 b2 b3 := by
      simp only [det3]; rw [hyj 0, hyj 1, hyj 2]; ring
    funext i
    fin_cases i
    · simp [ycoord, d0, Int.mul_ediv_cancel _ hD]
    · simp [ycoord, d1, Int.mul_ediv_cancel _ hD]
    · simp [ycoord, d2, Int.mul_ediv_cancel _ hD]
  rw [hyc]
  refine ⟨hyj, fun i => ?_⟩
  have hnk : nrm3 x ≤ 3 * (H : ℤ) ^ 2 := by
    have e : ∀ a, x a ^ 2 ≤ (H : ℤ) ^ 2 := fun a => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx a) 2
    have := e 0; have := e 1; have := e 2
    simp only [nrm3, dot3] at *
    nlinarith
  have key : 27 * ((R : ℤ) * y i) ^ 2 ≤ 27 * (3 * (H : ℤ)) ^ 2 := by
    have hb : 27 * (nrm3 (![b1, b2, b3] i) * y i ^ 2) ≤ 64 * nrm3 x := by
      fin_cases i
      · exact hy0
      · exact hy1
      · exact hy2
    have hnb : (R : ℤ) ^ 2 ≤ nrm3 (![b1, b2, b3] i) := by
      fin_cases i
      · exact n1
      · exact n2
      · exact n3
    have : (R : ℤ) ^ 2 * y i ^ 2 ≤ nrm3 (![b1, b2, b3] i) * y i ^ 2 :=
      mul_le_mul_of_nonneg_right hnb (sq_nonneg _)
    nlinarith
  have := sq_le_sq.mp (le_of_mul_le_mul_left key (by norm_num))
  rw [abs_mul, abs_of_pos hR, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 3 * H)] at this
  exact this

/-- In a basis with `27 |b₁|²|b₂|²|b₃|² ≤ 64 D²`, `D² ≤ B` and all `|bᵢ|² ≥ 1`, each
`27 |bᵢ|² ≤ 64 B`. -/
lemma basis_nrm_le {n1 n2 n3 D B : ℤ} (h1 : 1 ≤ n1) (h2 : 1 ≤ n2) (h3 : 1 ≤ n3)
    (hred : 27 * (n1 * n2 * n3) ≤ 64 * D ^ 2) (hD : D ^ 2 ≤ B) :
    27 * n1 ≤ 64 * B ∧ 27 * n2 ≤ 64 * B ∧ 27 * n3 ≤ 64 * B := by
  have e1 : n1 ≤ n1 * n2 * n3 := by
    have : 1 ≤ n2 * n3 := by nlinarith
    nlinarith
  have e2 : n2 ≤ n1 * n2 * n3 := by
    have : 1 ≤ n1 * n3 := by nlinarith
    nlinarith
  have e3 : n3 ≤ n1 * n2 * n3 := by
    have : 1 ≤ n1 * n2 := by nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The lifted basis: rows `1, 2, 3` of the five gaps of `b₁, b₂, b₃`. -/
noncomputable def liftM (p : Fin 10 → ℤ) (b1 b2 b3 : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![liftv p b1 1, liftv p b2 1, liftv p b3 1; liftv p b1 2, liftv p b2 2, liftv p b3 2;
    liftv p b1 3, liftv p b2 3, liftv p b3 3]

/-- `m · det B̂ = p₁₂₃ · det(b₁, b₂, b₃) ≠ 0`. -/
lemma liftM_det_ne {p : Fin 10 → ℤ} {Mx : Fin 3 → Fin 5 → ℤ} {b1 b2 b3 : Fin 3 → ℤ}
    (hMx : plk Mx = p) (hm : p (piv p) ≠ 0) (h6 : p 6 ≠ 0) (h1 : b1 ∈ pivLat p)
    (h2 : b2 ∈ pivLat p) (h3 : b3 ∈ pivLat p) (hD : det3 b1 b2 b3 ≠ 0) :
    (liftM p b1 b2 b3).det ≠ 0 := by
  set τ := piv p
  have hE : p τ • liftM p b1 b2 b3 = Matrix.of ![![dot3 (Lrow p τ 1) b1, dot3 (Lrow p τ 1) b2,
      dot3 (Lrow p τ 1) b3], ![dot3 (Lrow p τ 2) b1, dot3 (Lrow p τ 2) b2, dot3 (Lrow p τ 2) b3],
      ![dot3 (Lrow p τ 3) b1, dot3 (Lrow p τ 3) b2, dot3 (Lrow p τ 3) b3]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [liftM, liftv_spec h1, liftv_spec h2, liftv_spec h3, τ]
  have e := det3_mul (Lrow p τ 1) (Lrow p τ 2) (Lrow p τ 3) b1 b2 b3
  rw [← hE, Matrix.det_smul, Fintype.card_fin] at e
  have hL := lift_det Mx τ
  rw [hMx] at hL
  rw [hL] at e
  intro h0
  rw [h0, mul_zero] at e
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hm) h6) hD e.symm

/-- **The gap vectors of one minor vector.** -/
theorem lattice_fiber_count {p : Fin 10 → ℤ} {M H W : ℕ} (hM1 : 1 ≤ M) (hpM : ∀ t, |p t| ≤ M)
    (hA : 1 ≤ p 0) (hA' : 1 ≤ p 6) (hU : 0 < p 3) (hV : 0 < p 1)
    {Vs : Finset (Fin 5 → ℤ)}
    (hVs : ∀ k ∈ Vs, (∀ t, 1 ≤ k t ∧ k t ≤ H) ∧
      (∃ Mk : Fin 3 → Fin 5 → ℤ, plk Mk = p ∧ ∀ c, Mk 1 c = k c) ∧
      ternθ (p 0) (p 6) (p 9) (p 3) (-p 1) (p 8) (-p 7) (k 1) (k 2) (k 3) = 0)
    (hW : ∀ M' : ℤ, M' ≠ 0 →
      |M'| ≤ 116 * ((248832 * M ^ 8 : ℕ) : ℤ) ^ 4 * ((12 * H + 1 : ℕ) : ℤ) ^ 2 →
      2 * M'.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * (248832 * M ^ 8) ^ 2 * (12 * H + 1) *
        (3 * (248832 * M ^ 8) + 2)) ^ 2) + 1) ≤ W) :
    Vs.card ≤ (2 * (4 * (3 * H / shortR p) + 1) + 1) * (W + 4) := by
  classical
  rcases Vs.eq_empty_or_nonempty with hE | ⟨k0, hk0⟩
  · rw [hE]; simp
  obtain ⟨-, ⟨Mx, hMx, -⟩, -⟩ := hVs k0 hk0
  set τ := piv p with hτ
  set m := p τ with hmdef
  have hpl : PluckerRel p := hMx ▸ plucker Mx
  have hm6 : |p 6| ≤ |m| := piv_max p 6
  have hm : m ≠ 0 := by
    intro h; rw [h, abs_zero] at hm6; have := abs_nonneg (p 6); rw [abs_of_pos (by omega)] at hm6
    omega
  have hmM : |m| ≤ M := hpM τ
  have hM : (1 : ℤ) ≤ M := by exact_mod_cast hM1
  -- the reduced basis
  have hΛ : ∀ x : Fin 3 → ℤ, (∀ j, ((m.natAbs : ℕ) : ℤ) ∣ x j) → x ∈ pivLat p :=
    fun x h => pivLat_of_dvd fun j => Int.natAbs_dvd.mp (h j)
  obtain ⟨b1, b2, b3, h1, h2, h3, hD, hDm, hbas, hred⟩ :=
    reduced_basis (Λ := pivLat p) (Int.natAbs_pos.mpr hm) hΛ
  set D := det3 b1 b2 b3 with hDdef
  obtain ⟨hR1, -, hRlow⟩ := shortR_spec hm
  set R := shortR p with hRdef
  have hRpos : (0 : ℤ) < R := by exact_mod_cast hR1
  have hb10 : b1 ≠ 0 := by intro h0; apply hD; rw [hDdef, h0]; simp [det3]
  have hb20 : b2 ≠ 0 := by intro h0; apply hD; rw [hDdef, h0]; simp [det3]
  have hb30 : b3 ≠ 0 := by intro h0; apply hD; rw [hDdef, h0]; simp [det3]
  have n1 := hRlow b1 h1 hb10
  have n2 := hRlow b2 h2 hb20
  have n3 := hRlow b3 h3 hb30
  have hR2 : (1 : ℤ) ≤ (R : ℤ) ^ 2 := by nlinarith
  -- size of the basis
  have hD2 : D ^ 2 ≤ ((M : ℤ) ^ 3) ^ 2 := by
    have e1 : |D| ≤ |m| ^ 3 := by
      have : ((D.natAbs : ℕ) : ℤ) ≤ ((m.natAbs ^ 3 : ℕ) : ℤ) := by exact_mod_cast hDm
      push_cast at this; simpa [Int.natCast_natAbs] using this
    have e2 : |D| ≤ (M : ℤ) ^ 3 := e1.trans (pow_le_pow_left₀ (abs_nonneg _) hmM 3)
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e2 2
  have hM0 : (0 : ℤ) ≤ M := by linarith
  obtain ⟨l1, l2, l3⟩ := basis_nrm_le (by linarith) (by linarith) (by linarith) hred hD2
  -- the lifted basis
  set Bh := liftM p b1 b2 b3 with hBh
  have hBb : ∀ i j, |Bh i j| ≤ 6 * (M : ℤ) ^ 3 := by
    have q1 := liftv_bound h1 hm (entry_bound hM0 l1)
    have q2 := liftv_bound h2 hm (entry_bound hM0 l2)
    have q3 := liftv_bound h3 hm (entry_bound hM0 l3)
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Bh, liftM] <;>
        linarith [q1 1, q1 2, q1 3, q2 1, q2 2, q2 3,
      q3 1, q3 2, q3 3]
  have hdetB : Bh.det ≠ 0 := liftM_det_ne hMx hm (by omega) h1 h2 h3 hD
  -- the quadratic in basis coordinates
  set Fθ := thetaCoef (p 0) (p 6) (p 9) (p 3) (-p 1) (p 8) (-p 7)
  have hFD : disc3 Fθ ≠ 0 := disc3_thetaCoef (by omega) (by omega) hU (by linarith)
  set G := tcomp Fθ Bh
  have hGD : disc3 G ≠ 0 := by
    rw [disc3_tcomp]; exact mul_ne_zero hFD (pow_ne_zero 2 hdetB)
  obtain ⟨P, Pi, hPg, hPΔ⟩ := plane_one G hGD
  have hPdet := hPg.det_sq
  obtain ⟨hPP, hPi, hPb⟩ := hPg
  set G1 := tcomp G P
  obtain ⟨Q, Qi, hQg, hQα, hQΔ⟩ := plane_two G1 hPΔ
  have hQdet := hQg.det_sq
  obtain ⟨hQQ, hQi, hQb⟩ := hQg
  set G2 := tcomp G1 Q
  have hG2D : disc3 G2 ≠ 0 := by
    simp only [G2, G1, disc3_tcomp, hPdet, hQdet, mul_one]; exact hGD
  -- coefficient bounds
  have hFb : ∀ t, |Fθ t| ≤ 4 * (M : ℤ) ^ 2 := by
    have a0 := hpM 0; have a6 := hpM 6; have a9 := hpM 9; have a3 := hpM 3
    have a1 : |-p 1| ≤ M := by rw [abs_neg]; exact hpM 1
    have a8 := hpM 8
    have a7 : |-p 7| ≤ M := by rw [abs_neg]; exact hpM 7
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := tern_coef_le a0 a6 a9 a3 a1 a8 a7
    intro t
    fin_cases t
    exacts [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]
  have hG2b : ∀ t, |G2 t| ≤ ((248832 * M ^ 8 : ℕ) : ℤ) := by
    have g0 := tcomp_bound hFb hBb (by have : (1 : ℤ) ≤ (M : ℤ) ^ 3 := one_le_pow₀ hM; linarith)
    have g1 := tcomp_bound g0 hPb le_rfl
    have g2 := tcomp_bound g1 hQb le_rfl
    intro t
    have := g2 t
    push_cast
    calc |G2 t| ≤ 12 * (12 * (12 * (4 * (M : ℤ) ^ 2) * (6 * (M : ℤ) ^ 3) ^ 2) * 1 ^ 2) * 1 ^ 2 :=
          this
      _ = 248832 * (M : ℤ) ^ 8 := by ring
  -- coordinates of a gap vector
  set kp : (Fin 5 → ℤ) → Fin 3 → ℤ := fun k a => k (pcol τ a)
  set yc : (Fin 5 → ℤ) → Fin 3 → ℤ := fun k => ycoord b1 b2 b3 (kp k)
  have hlift : ∀ k ∈ Vs, ∀ c, m * k c = dot3 (Lrow p τ c) (kp k) := by
    intro k hk c
    obtain ⟨-, ⟨Mk, hMk, hrow⟩, -⟩ := hVs k hk
    have := lift_row Mk τ 1 c
    rw [hMk] at this
    simp only [hrow] at this
    exact this
  have hmem : ∀ k ∈ Vs, kp k ∈ pivLat p := by
    intro k hk
    refine ⟨⟨k (restc τ 0), ?_⟩, ⟨k (restc τ 1), ?_⟩⟩
    · have := hlift k hk (restc τ 0); rw [Lrow_rest0] at this; exact this.symm
    · have := hlift k hk (restc τ 1); rw [Lrow_rest1] at this; exact this.symm
  have hcoord : ∀ k ∈ Vs, (∀ j, kp k j = yc k 0 * b1 j + yc k 1 * b2 j + yc k 2 * b3 j) ∧
      ∀ i, (R : ℤ) * |yc k i| ≤ 3 * H := fun k hk =>
    ycoord_spec hD (hbas _ (hmem k hk)) hred hRpos n1 n2 n3 fun a => by
      have := (hVs k hk).1 (pcol τ a)
      exact abs_le.mpr ⟨by linarith, this.2⟩
  have hexp : ∀ k ∈ Vs, ∀ c, k c = yc k 0 * liftv p b1 c + yc k 1 * liftv p b2 c +
      yc k 2 * liftv p b3 c := by
    intro k hk c
    apply mul_left_cancel₀ hm
    rw [hlift k hk c]
    have hj := (hcoord k hk).1
    have e1 := liftv_spec h1 c
    have e2 := liftv_spec h2 c
    have e3 := liftv_spec h3 c
    simp only [dot3] at e1 e2 e3 ⊢
    rw [hj 0, hj 1, hj 2]
    linear_combination -(yc k 0 * e1 + yc k 1 * e2 + yc k 2 * e3)
  -- the substitution
  set Y0 := 3 * H / R
  set Y := 4 * Y0 + 1
  set f : (Fin 5 → ℤ) → Fin 3 → ℤ := fun k => Qi *ᵥ (Pi *ᵥ yc k)
  have hPQ : ∀ k, P *ᵥ (Q *ᵥ f k) = yc k := fun k => by
    simp only [f, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc Q Qi Pi, hQQ, Matrix.one_mul, hPP, Matrix.one_mulVec]
  have hmaps : ∀ k ∈ Vs, f k ∈ (Fintype.piFinset fun _ : Fin 3 => ibox Y).filter
      fun v => ternv G2 v = 0 := by
    intro k hk
    have hy : ∀ i, |yc k i| ≤ (Y0 : ℤ) := fun i => by
      have h := (hcoord k hk).2 i
      have : |yc k i| ≤ (3 * (H : ℤ)) / R := Int.le_ediv_of_mul_le hRpos (by linarith)
      simpa [Y0, Int.natCast_div] using this
    have hy1 := mulVec_abs_le hPi hy
    have hy2 := mulVec_abs_le hQi hy1
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => mem_Icc.mpr (abs_le.mp ?_), ?_⟩
    · have := hy2 i
      have e : ((Y : ℕ) : ℤ) = 4 * Y0 + 1 := by simp [Y]
      rw [e]; linarith
    · have hB : Bh *ᵥ yc k = ![k 1, k 2, k 3] := by
        have e1 := hexp k hk 1
        have e2 := hexp k hk 2
        have e3 := hexp k hk 3
        funext i
        fin_cases i <;> simp [Bh, liftM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
      simp only [G2, G1, ternv_tcomp]
      rw [hPQ, ternv_tcomp, hB]
      change ternv (thetaCoef _ _ _ _ _ _ _) _ = 0
      rw [ternv_thetaCoef]
      exact (hVs k hk).2.2
  have hinj : Set.InjOn f Vs := by
    intro k hk k' hk' h
    have hy : yc k = yc k' := by rw [← hPQ k, ← hPQ k', h]
    funext c
    rw [hexp k hk c, hexp k' hk' c, hy]
  refine (card_le_card_of_injOn f hmaps hinj).trans ?_
  refine slice_count_tv (by omega) hQα hQΔ hG2D hG2b fun M' hM' hb =>
      (hW M' hM' (hb.trans ?_)).trans'
    (Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log_mono_right ?_)))
  · have : (Y : ℤ) ≤ (12 * H + 1 : ℕ) := by
      have : Y0 * R ≤ 3 * H := Nat.div_mul_le_self _ _
      have : Y0 ≤ 3 * H := by nlinarith
      push_cast; simp only [Y]; push_cast; linarith [show (Y0 : ℤ) ≤ 3 * H by exact_mod_cast this]
    gcongr
  · have : Y ≤ 12 * H + 1 := by
      have : Y0 * R ≤ 3 * H := Nat.div_mul_le_self _ _
      have : Y0 ≤ 3 * H := by nlinarith
      omega
    gcongr

/-- **The counting lemma through the pattern lattices.** -/
theorem pattern_count_lattice {G : Finset ℕ} {θ : ℕ → Fin 7 → ℤ} {κ : ℕ → Fin 5 → ℤ}
    {pm : ℕ → Fin 10 → ℤ} {Q : ℕ → ℤ} {a : ℤ} {M H W : ℕ} (hM1 : 1 ≤ M)
    (hθ : ∀ i ∈ G, θ i = projθ (pm i))
    (hQ : Set.InjOn Q G)
    (hpm : ∀ i ∈ G, ∃ Mk : Fin 3 → Fin 5 → ℤ, plk Mk = pm i ∧ ∀ c, Mk 1 c = κ i c)
    (hpM : ∀ i ∈ G, ∀ t, |pm i t| ≤ M)
    (hκ : ∀ i ∈ G, ∀ t, 1 ≤ κ i t ∧ κ i t ≤ H)
    (h0 : ∀ i ∈ G, 1 ≤ θ i 0) (h1 : ∀ i ∈ G, 1 ≤ θ i 1)
    (e0 : ∀ i ∈ G, -θ i 1 * κ i 0 + θ i 3 * κ i 1 + θ i 4 * κ i 2 + θ i 0 * κ i 3 = 0)
    (e4 : ∀ i ∈ G, -θ i 2 * κ i 1 + θ i 5 * κ i 2 + θ i 6 * κ i 3 + θ i 1 * κ i 4 = 0)
    (e3 : ∀ i ∈ G, -θ i 1 * (κ i 0 ^ 2 + κ i 1) + θ i 3 * (κ i 1 * (2 * κ i 0 + κ i 1) + κ i 2) +
      θ i 4 * (κ i 2 * (2 * κ i 0 + 2 * κ i 1 + κ i 2) + κ i 3) +
      θ i 0 * (κ i 3 * (2 * κ i 0 + 2 * κ i 1 + 2 * κ i 2 + κ i 3) + κ i 4) = 0)
    (hm : ∀ i ∈ G, quart (-θ i 1) (θ i 3) (θ i 4) (θ i 0) (κ i 0) (κ i 1) (κ i 2) (Q i) =
      a * muH4 (κ i 0) (κ i 1) (κ i 2) (κ i 3) (κ i 4))
    (hW : ∀ M' : ℤ, M' ≠ 0 →
      |M'| ≤ 116 * ((248832 * M ^ 8 : ℕ) : ℤ) ^ 4 * ((12 * H + 1 : ℕ) : ℤ) ^ 2 →
      2 * M'.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * (248832 * M ^ 8) ^ 2 * (12 * H + 1) *
        (3 * (248832 * M ^ 8) + 2)) ^ 2) + 1) ≤ W) :
    G.card ≤ ∑ p ∈ G.image pm, 4 * ((2 * (4 * (3 * H / shortR p) + 1) + 1) * (W + 4)) := by
  classical
  set F : ℕ → (Fin 10 → ℤ) × (Fin 5 → ℤ) := fun i => (pm i, κ i)
  -- step 1: at most four states per `(p, κ)`
  have step1 : G.card ≤ 4 * (G.image F).card := by
    refine card_le_mul_card_image G 4 fun v hv => ?_
    set S := G.filter fun i => F i = v
    rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
    · rw [hS]; simp
    have hi₀' := mem_filter.mp hi₀
    rw [← card_image_of_injOn (hQ.mono (fun x hx => (mem_filter.mp hx).1))]
    have hlead : θ i₀ 0 ≠ 0 := by have := h0 i₀ hi₀'.1; omega
    refine card_le_four_of_quartic (c3 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0)
      (κ i₀ 1) (κ i₀ 2) 3) (c2 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0) (κ i₀ 1)
      (κ i₀ 2) 2) (c1 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) 1)
      (c0 := quartC (-θ i₀ 1) (θ i₀ 3) (θ i₀ 4) (θ i₀ 0) (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) 0 -
        a * muH4 (κ i₀ 0) (κ i₀ 1) (κ i₀ 2) (κ i₀ 3) (κ i₀ 4)) hlead fun z hz => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    obtain ⟨hiG, hFi⟩ := mem_filter.mp hi
    have hF : F i = F i₀ := hFi.trans hi₀'.2.symm
    simp only [F, Prod.mk.injEq] at hF
    have hθi : θ i = θ i₀ := by rw [hθ i hiG, hθ i₀ hi₀'.1, hF.1]
    have := hm i hiG
    rw [quart_eq, hθi, hF.2] at this
    linarith
  -- step 2: split by minor vector
  have step2 : (G.image F).card = ∑ p ∈ G.image pm, ((G.image F).filter fun v => v.1 = p).card :=
    card_eq_sum_card_fiberwise fun v hv => by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨i, hi, rfl⟩
  have step3 : ∀ p ∈ G.image pm, ((G.image F).filter fun v => v.1 = p).card ≤
      (2 * (4 * (3 * H / shortR p) + 1) + 1) * (W + 4) := by
    intro p hp
    obtain ⟨i0, hi0, hpi0⟩ := mem_image.mp hp
    set Vs := (G.filter fun i => pm i = p).image κ
    have hle : ((G.image F).filter fun v => v.1 = p).card ≤ Vs.card := by
      refine card_le_card_of_injOn Prod.snd (fun v hv => ?_) (fun v hv v' hv' h => ?_)
      · obtain ⟨hv1, hvp⟩ := mem_filter.mp (mem_coe.mp hv)
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hv1
        exact mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, hvp⟩, rfl⟩
      · exact Prod.ext ((mem_filter.mp (mem_coe.mp hv)).2.trans
          (mem_filter.mp (mem_coe.mp hv')).2.symm) h
    refine hle.trans (lattice_fiber_count hM1 (hpi0 ▸ hpM i0 hi0) ?_ ?_ ?_ ?_ ?_ hW)
    · have := h0 i0 hi0; rw [hθ i0 hi0, hpi0] at this; simpa [projθ] using this
    · have := h1 i0 hi0; rw [hθ i0 hi0, hpi0] at this; simpa [projθ] using this
    · have hk := fun t => (hκ i0 hi0 t).1
      have := (pattern_signs (h0 i0 hi0) (h1 i0 hi0) (hk 0) (hk 1) (hk 2) (hk 3) (hk 4)
        (e0 i0 hi0) (e3 i0 hi0)).1
      rw [hθ i0 hi0, hpi0] at this; simpa [projθ] using this
    · have hk := fun t => (hκ i0 hi0 t).1
      have := (pattern_signs (h0 i0 hi0) (h1 i0 hi0) (hk 0) (hk 1) (hk 2) (hk 3) (hk 4)
        (e0 i0 hi0) (e3 i0 hi0)).2
      rw [hθ i0 hi0, hpi0] at this; simp [projθ] at this; linarith
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
      obtain ⟨hiG, hpi⟩ := mem_filter.mp hi
      refine ⟨hκ i hiG, hpi ▸ hpm i hiG, ?_⟩
      have := tern_rel (by have := h1 i hiG; omega) (e0 i hiG) (e4 i hiG) (e3 i hiG)
      rw [hθ i hiG, hpi] at this
      simpa [projθ] using this
  calc G.card ≤ 4 * (G.image F).card := step1
    _ = 4 * ∑ p ∈ G.image pm, ((G.image F).filter fun v => v.1 = p).card := by rw [step2]
    _ ≤ 4 * ∑ p ∈ G.image pm, (2 * (4 * (3 * H / shortR p) + 1) + 1) * (W + 4) :=
        Nat.mul_le_mul_left _ (sum_le_sum step3)
    _ = _ := by rw [mul_sum]

end PierceBound
