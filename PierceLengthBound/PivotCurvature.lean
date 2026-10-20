/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftCurvatureHeight
public import PierceLengthBound.FixedDividendLatticeCoordinates
public import PierceLengthBound.PivotExterior

/-!
# Curvature coordinates in the exterior of the pattern lattice

Every curvature minor `d_j k_l - d_l k_j` of the five-column pattern matrix has the uniform
height `148 a H³ / q³`, using six future gaps (`orbit_curvature_minor_height_five`). The pivot
columns of the drop and gap rows lie in the pattern lattice, so the cross product `w` of their
pivot parts has integer coordinates `c` in the exterior of a reduced basis, with
`3 λ² |cᵢ| ≤ 8 S` (`wcoord_bound`). The old curvature vector `W` of columns `0, 1, 2` satisfies
`m² W = Cof · w` (Binet–Cauchy), so `c = G W` for a rational matrix `G` with nonzero determinant
that depends only on the pattern (`lattice_curvature_coordinates`).
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Matrix

/-! ### Heights of all ten curvature minors -/

theorem curvature_error_le_five {a b m : ℕ} (hba : b < a) (hm : m + 2 < P a b)
    {q H : ℝ} (hq : 0 < q) (hH : 1 ≤ H) (hqm : q ≤ qq a b m)
    (hs : (qq a b m : ℝ) - q ≤ 5 * H) (hk : kk a b m ≤ H) :
    curvatureError a b m q ≤ 37 * H ^ 2 / q ^ 3 := by
  have h := (curvature_reciprocal_expansion hba hm hq hqm).2.1
  rw [muF_shift_sq hba hm] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs0 : 0 ≤ (qq a b m : ℝ) - q := by linarith
  have hsq : ((qq a b m : ℝ) - q) ^ 2 ≤ (5 * H) ^ 2 := by gcongr
  nlinarith [sq_nonneg (H - 1)]

lemma curvature_drop_error_five {a b m : ℕ} (hba : b < a) (hm : m + 3 < P a b)
    {q H : ℝ} (hq : 0 < q) (hH : 1 ≤ H) (hqm : q ≤ qq a b m)
    (hs0 : (qq a b m : ℝ) - q ≤ 5 * H)
    (hs1 : (qq a b (m + 1) : ℝ) - q ≤ 5 * H)
    (hk0 : kk a b m ≤ H) (hk1 : kk a b (m + 1) ≤ H) :
    |(dq a b m : ℝ) - (a : ℝ) / q ^ 2 * kk a b m| ≤ 74 * a * H ^ 2 / q ^ 3 := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hqm1 : q ≤ qq a b (m + 1) := hqm.trans (by
    exact_mod_cast (qq_le_of_le (a := a) (b := b) (by omega : m ≤ m + 1) (by omega)))
  have h0 := curvature_reciprocal_expansion hba (by omega : m + 2 < P a b) hq hqm
  have h1 := curvature_reciprocal_expansion hba (by omega : m + 1 + 2 < P a b) hq hqm1
  have hb0 := curvature_error_le_five hba (by omega : m + 2 < P a b) hq hH hqm hs0 hk0
  have hb1 := curvature_error_le_five hba (by omega : m + 1 + 2 < P a b) hq hH hqm1 hs1 hk1
  have he0 := (div_eq_iff ha.ne').mp h0.2.2
  have he1 := (div_eq_iff ha.ne').mp h1.2.2
  have he : (dq a b m : ℝ) - (a : ℝ) / q ^ 2 * kk a b m =
      a * (curvatureError a b m q - curvatureError a b (m + 1) q) := by
    simp only [dq, Int.cast_sub, Int.cast_natCast, kk]
    rw [he0, he1]
    ring
  rw [he, abs_mul, abs_of_pos ha]
  calc (a : ℝ) * |curvatureError a b m q - curvatureError a b (m + 1) q| ≤
      a * (|curvatureError a b m q| + |curvatureError a b (m + 1) q|) := by
        gcongr
        exact abs_sub _ _
    _ = a * (curvatureError a b m q + curvatureError a b (m + 1) q) := by
      rw [abs_of_nonneg h0.1, abs_of_nonneg h1.1]
    _ ≤ a * (37 * H ^ 2 / q ^ 3 + 37 * H ^ 2 / q ^ 3) := by gcongr
    _ = _ := by ring

/-- Every one of the ten curvature minors has the uniform cubic height. Six future gaps are
used. -/
theorem orbit_curvature_minor_height_five {a b i H j l : ℕ}
    (hba : b < a) (hi : i + 8 < P a b) (hH : 1 ≤ H)
    (hk : ∀ t < 6, kq a b (i + t) ≤ H) (hj : j < 5) (hl : l < 5) :
    |(dq a b (i + j) : ℝ) * kq a b (i + l) - dq a b (i + l) * kq a b (i + j)| ≤
      148 * a * (H : ℝ) ^ 3 / (qq a b i : ℝ) ^ 3 := by
  have hq : (0 : ℝ) < qq a b i := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (qq_pos hba (by omega))
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hkr (t : ℕ) (ht : t < 6) : kk a b (i + t) ≤ H := by
    have h := hk t ht
    have h' : (kq a b (i + t) : ℝ) ≤ H := by exact_mod_cast h
    simpa only [kk, kq, Int.cast_sub, Int.cast_natCast] using h'
  have hqr (t : ℕ) (ht : t < 6) : (qq a b i : ℝ) ≤ qq a b (i + t) := by
    exact_mod_cast (qq_le_of_le (by omega : i ≤ i + t) (by omega : i + t < P a b))
  have hs (t : ℕ) (ht : t < 6) : (qq a b (i + t) : ℝ) - qq a b i ≤ 5 * H := by
    rw [qq_eq_add_pt, add_sub_cancel_right, pt_eq_sum]
    calc (∑ m ∈ range t, kk a b (i + m)) ≤ ∑ _m ∈ range t, (H : ℝ) := by
          exact sum_le_sum (fun m hm => hkr m (by have := mem_range.mp hm; omega))
      _ = (t : ℝ) * H := by simp
      _ ≤ 5 * H := by gcongr; exact_mod_cast (show t ≤ 5 by omega)
  have hd (t : ℕ) (ht : t < 5) :
      |(dq a b (i + t) : ℝ) - (a : ℝ) / (qq a b i : ℝ)^2 * (kq a b (i + t) : ℝ)| ≤
        74 * a * (H : ℝ)^2 / (qq a b i : ℝ)^3 := by
    have h := curvature_drop_error_five hba (by omega : i + t + 3 < P a b) hq hHR
      (hqr t (by omega)) (hs t (by omega))
      (by simpa only [Nat.add_assoc] using hs (t + 1) (by omega))
      (hkr t (by omega)) (by simpa only [Nat.add_assoc] using hkr (t + 1) (by omega))
    simpa only [kk, kq, Int.cast_sub, Int.cast_natCast] using h
  have hab (t : ℕ) (ht : t < 5) : |(kq a b (i + t) : ℝ)| ≤ H := by
    have hp : (0 : ℝ) ≤ kq a b (i + t) := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1) (kq_pos (by omega : i + t + 1 < P a b)))
    rw [abs_of_nonneg hp]
    exact_mod_cast hk t (by omega)
  have h := curvature_minor_error_bound (hd j hj) (hd l hl) (hab j hj) (hab l hl)
  convert h using 1
  ring

/-- The common height of all ten curvature minors at a selected start. -/
def selectedPivotCurvatureHeight (a A T : ℕ) : ℕ :=
  9472 * A ^ 3 * selectedGapHeight a A T ^ 3 / a ^ 2

/-- All ten curvature minors at a selected start lie in the common box. -/
theorem selected_curvature_minor_bound {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) {j l : ℕ}
    (hj : j < 5) (hl : l < 5) :
    |dq a b (i + j) * kq a b (i + l) - dq a b (i + l) * kq a b (i + j)| ≤
      (selectedPivotCurvatureHeight a A T : ℕ) := by
  obtain ⟨hP, hk, hA⟩ := selectedStart_spec hmem hsT hi
  have hq : (0 : ℝ) < qq a b i := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (qq_pos hba (by omega))
  have hr := (le_div_iff₀ (pow_pos hq 3)).mp (orbit_curvature_minor_height_five hba hP
    (show 1 ≤ selectedGapHeight a A T from Nat.le_add_left 1 _)
    (fun t ht => (hk t (by omega)).2) hj hl)
  have hh : |dq a b (i + j) * kq a b (i + l) - dq a b (i + l) * kq a b (i + j)| *
      (qq a b i : ℤ) ^ 3 ≤ 148 * (a : ℤ) * selectedGapHeight a A T ^ 3 := by
    exact_mod_cast hr
  have hqw := window_quotient_lower hba (by omega : i < P a b) hA
  have hqZ : (a : ℤ) ≤ 4 * A * qq a b i := by exact_mod_cast hqw
  set e := |dq a b (i + j) * kq a b (i + l) - dq a b (i + l) * kq a b (i + j)|
  have he : 0 ≤ e := abs_nonneg _
  have hb : e * (a : ℤ) ^ 3 ≤ 9472 * (a : ℤ) * A ^ 3 * (selectedGapHeight a A T : ℤ) ^ 3 := by
    calc _ ≤ e * (4 * (A : ℤ) * qq a b i) ^ 3 := by gcongr
      _ = (64 * (A : ℤ) ^ 3) * (e * (qq a b i : ℤ) ^ 3) := by ring
      _ ≤ (64 * (A : ℤ) ^ 3) * (148 * (a : ℤ) * (selectedGapHeight a A T : ℤ) ^ 3) := by
        gcongr
      _ = _ := by ring
  have ha : (0 : ℤ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb' : e * (a : ℤ) ^ 2 ≤ 9472 * (A : ℤ) ^ 3 * (selectedGapHeight a A T : ℤ) ^ 3 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    convert hb using 1 <;> ring
  have hd := Int.le_ediv_of_mul_le (by positivity : (0 : ℤ) < (a : ℤ) ^ 2) hb'
  simpa only [selectedPivotCurvatureHeight, Int.natCast_div, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat] using hd

/-! ### Transport from the exterior coordinates to the old curvature vector -/

/-- Binet–Cauchy in `ℤ³`. -/
lemma binet_cauchy3 (a b x y : Fin 3 → ℤ) :
    dot3 a x * dot3 b y - dot3 b x * dot3 a y = dot3 (cross3 a b) (cross3 x y) := by
  simp only [dot3, cross3_zero, cross3_one, cross3_two]; ring

/-- The matrix of cofactor rows `l₁ × l₂, l₂ × l₀, l₀ × l₁`. -/
def cofRows (l0 l1 l2 : Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![cross3 l1 l2, cross3 l2 l0, cross3 l0 l1]

lemma cofRows_det (l0 l1 l2 : Fin 3 → ℤ) : (cofRows l0 l1 l2).det = det3 l0 l1 l2 ^ 2 := by
  rw [det_fin_three]
  simp [cofRows, cross3_zero, cross3_one, cross3_two, det3]
  ring

lemma rows_det (b1 b2 b3 : Fin 3 → ℤ) :
    (Matrix.of ![b1, b2, b3]).det = det3 b1 b2 b3 := by
  rw [det_fin_three]
  simp [det3]
  ring

/-- The first three columns of a matrix with pattern `p`. -/
def firstThree (x : Fin 5 → ℤ) : Fin 3 → ℤ := fun j => x (Fin.castLE (by decide) j)

/-- **Curvature coordinates for a fixed pattern.** There is a rational matrix `G` with nonzero
determinant, depending only on `p`, and integer coordinates `c(d, k)` such that every matrix
with pattern `p` and rows `d, k` has `c = G W`, where `W` is the old curvature vector of the
first three columns, and `3 λ² |cᵢ| ≤ 8 S` when all ten curvature minors are at most `S`. -/
theorem lattice_curvature_coordinates {p : Fin 10 → ℤ} (h0 : p 0 ≠ 0)
    (hp : ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℚ, G.det ≠ 0 ∧
      ∃ c : (Fin 5 → ℤ) → (Fin 5 → ℤ) → Fin 3 → ℤ,
        ∀ M : Fin 3 → Fin 5 → ℤ, plk M = p →
          (fun t => (c (M 0) (M 1) t : ℚ)) =
            G *ᵥ (fun t => ((curvatureVector (firstThree (M 0)) (firstThree (M 1)) t : ℤ) : ℚ)) ∧
          ∀ S : ℕ, (∀ j l, |M 0 j * M 1 l - M 0 l * M 1 j| ≤ S) →
            ∀ t, 3 * (shortR p : ℤ) ^ 2 * |c (M 0) (M 1) t| ≤ 8 * S := by
  classical
  have hm : p (piv p) ≠ 0 := by
    intro hz
    have := piv_max p 0
    rw [hz, abs_zero] at this
    exact h0 (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))
  set τ := piv p
  set m := p τ
  have hΛ : ∀ x : Fin 3 → ℤ, (∀ j, ((m.natAbs : ℕ) : ℤ) ∣ x j) → x ∈ pivLat p :=
    fun x h => pivLat_of_dvd fun j => Int.natAbs_dvd.mp (h j)
  obtain ⟨b1, b2, b3, h1, h2, h3, hD, _, hbas, hred⟩ :=
    reduced_basis (Λ := pivLat p) (Int.natAbs_pos.mpr hm) hΛ
  obtain ⟨hR1, _, hRlow⟩ := shortR_spec hm
  have hb10 : b1 ≠ 0 := by intro h; apply hD; rw [h]; simp [det3]
  have hb20 : b2 ≠ 0 := by intro h; apply hD; rw [h]; simp [det3]
  have hb30 : b3 ≠ 0 := by intro h; apply hD; rw [h]; simp [det3]
  have n1 := hRlow b1 h1 hb10
  have n2 := hRlow b2 h2 hb20
  have n3 := hRlow b3 h3 hb30
  have hRpos : (0 : ℤ) < shortR p := by exact_mod_cast hR1
  let piv3 := fun x : Fin 5 → ℤ => fun a => x (pcol τ a)
  let c := fun d k : Fin 5 → ℤ => wcoord b1 b2 b3 (piv3 d) (piv3 k)
  let Cm := cofRows (Lrow p τ 0) (Lrow p τ 1) (Lrow p τ 2)
  let Bt : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of ![b1, b2, b3]
  let N := Bt * Cm.adjugate
  set Δ := det3 b1 b2 b3
  set κ := Cm.det
  obtain ⟨M0, hM0⟩ := hp
  have hL : det3 (Lrow p τ 0) (Lrow p τ 1) (Lrow p τ 2) = m ^ 2 * p 0 := by
    have := lift_first_det M0 τ
    rw [hM0] at this
    exact this
  have hκ : κ ≠ 0 := by
    simp only [κ, Cm, cofRows_det, hL]
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hm) h0)
  have hN : N.det = Δ * κ ^ 2 := by
    change (Matrix.of ![b1, b2, b3] * Cm.adjugate).det = _
    rw [det_mul, rows_det, det_adjugate, Fintype.card_fin]
  have hNq : (N.map (Int.cast : ℤ → ℚ)).det = (N.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det N).symm
  let r : ℚ := (m : ℚ) ^ 2 / ((Δ : ℚ) * κ)
  have hr : r ≠ 0 := by
    have : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have : (Δ : ℚ) ≠ 0 := by exact_mod_cast hD
    have : (κ : ℚ) ≠ 0 := by exact_mod_cast hκ
    positivity
  refine ⟨r • N.map (Int.cast : ℤ → ℚ), ?_, c, fun M hM => ?_⟩
  · rw [det_smul, hNq, hN]
    have : (Δ : ℚ) ≠ 0 := by exact_mod_cast hD
    have : (κ : ℚ) ≠ 0 := by exact_mod_cast hκ
    push_cast
    positivity
  have hlift (row : Fin 3) (j : Fin 5) : m * M row j = dot3 (Lrow p τ j) (piv3 (M row)) := by
    have h := lift_row M τ row j
    rw [hM] at h
    exact h
  have hmem (row : Fin 3) : piv3 (M row) ∈ pivLat p := by
    refine ⟨⟨M row (restc τ 0), ?_⟩, ⟨M row (restc τ 1), ?_⟩⟩
    · have h := hlift row (restc τ 0)
      rw [Lrow_rest0] at h
      exact h.symm
    · have h := hlift row (restc τ 1)
      rw [Lrow_rest1] at h
      exact h.symm
  have spec := wcoord_spec hD (hbas _ (hmem 0)) (hbas _ (hmem 1)) hred hRpos n1 n2 n3
  refine ⟨?_, fun S hS t => ?_⟩
  · set w := cross3 (piv3 (M 0)) (piv3 (M 1))
    set W := curvatureVector (firstThree (M 0)) (firstThree (M 1))
    have hW : W = ![M 0 1 * M 1 2 - M 0 2 * M 1 1, -(M 0 0 * M 1 2 - M 0 2 * M 1 0),
        M 0 0 * M 1 1 - M 0 1 * M 1 0] := by
      funext t; fin_cases t <;> rfl
    have hdot (x y : Fin 3 → ℤ) : x ⬝ᵥ y = dot3 x y := by
      simp [dotProduct, Fin.sum_univ_three, dot3]
    -- `Cof · w = m² W`, by Binet–Cauchy
    have hCw : Cm *ᵥ w = m ^ 2 • W := by
      have l0 := hlift 0 0; have l1 := hlift 0 1; have l2 := hlift 0 2
      have k0 := hlift 1 0; have k1 := hlift 1 1; have k2 := hlift 1 2
      funext t
      simp only [Cm, cofRows, mulVec, of_apply, hdot, hW, Pi.smul_apply, smul_eq_mul]
      fin_cases t
      · simp only [Fin.zero_eta, cons_val_zero, w, ← binet_cauchy3, ← l1, ← l2, ← k1, ← k2]
        ring
      · simp only [Fin.mk_one, cons_val_one, cons_val_zero, w, ← binet_cauchy3, ← l0, ← l2,
          ← k0, ← k2]
        ring
      · simp only [Fin.reduceFinMk, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
          Matrix.tail_cons, Matrix.head_cons, w, ← binet_cauchy3, ← l0, ← l1, ← k0, ← k1]
        ring
    -- `Bᵀ w = Δ c`
    have hBw : Bt *ᵥ w = Δ • c (M 0) (M 1) := by
      obtain ⟨_, ⟨e0, e1, e2⟩, _⟩ := spec
      funext t
      simp only [Bt, mulVec, of_apply, hdot, Pi.smul_apply, smul_eq_mul]
      fin_cases t
      · exact e0
      · exact e1
      · exact e2
    have hint : (Δ * κ) • c (M 0) (M 1) = m ^ 2 • (N *ᵥ W) := by
      have hadj : Cm.adjugate *ᵥ (Cm *ᵥ w) = κ • w := by
        rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
      rw [hCw, mulVec_smul] at hadj
      rw [mul_comm, mul_smul, ← hBw, ← mulVec_smul, ← hadj, ← mulVec_smul, mulVec_mulVec,
        mulVec_smul]
    funext t
    have ht := congrFun hint t
    simp only [Pi.smul_apply, smul_eq_mul] at ht
    have hmap := (Int.castRingHom ℚ).map_mulVec N W t
    simp only [smul_mulVec, Pi.smul_apply, smul_eq_mul]
    change (c (M 0) (M 1) t : ℚ) = r * (N.map (Int.castRingHom ℚ) *ᵥ (fun s => (W s : ℚ))) t
    rw [← show (Int.castRingHom ℚ) ∘ W = fun s => (W s : ℚ) from rfl, ← hmap]
    have : (Δ : ℚ) ≠ 0 := by exact_mod_cast hD
    have : (κ : ℚ) ≠ 0 := by exact_mod_cast hκ
    have htq : ((Δ : ℚ) * κ) * c (M 0) (M 1) t = (m : ℚ) ^ 2 * ((N *ᵥ W) t : ℤ) := by
      exact_mod_cast ht
    simp only [r, eq_intCast]
    field_simp
    linear_combination htq
  · exact wcoord_bound hD (hbas _ (hmem 0)) (hbas _ (hmem 1)) hred hRpos n1 n2 n3
      (fun a => hS (pcol τ (a + 1)) (pcol τ (a + 2))) t

end
end PierceLengthBound.FixedDividend
