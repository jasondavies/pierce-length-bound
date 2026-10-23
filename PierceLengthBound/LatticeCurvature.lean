/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftCurvatureHeight
public import PierceLengthBound.FixedDividendLatticeCoordinates
public import PierceLengthBound.LatticeExterior

/-!
# Curvature coordinates in the exterior of the pattern lattice

Every curvature minor `d_j k_l - d_l k_j` of the five-column pattern matrix has the uniform
height `148 a H³ / q³`, using six future gaps (`orbit_curvature_minor_height 5`). The pivot
columns of the drop and gap rows lie in the pattern lattice, so the cross product `w` of their
pivot parts has integer coordinates `c` in the exterior of a reduced basis, with
`3 λ² |cᵢ| ≤ 8 S` (`wcoord_bound`). The old curvature vector `W` of columns `0, 1, 2` satisfies
`m² W = Cof · w` (Binet–Cauchy), so `c = G W` for a rational matrix `G` with nonzero determinant
that depends only on the pattern (`lattice_curvature_coordinates`, paper `lem:latticecoords`).
Here `m` is the pivot entry, which the paper writes `p_π`, and `Δ` is the lattice determinant,
which the paper writes `V`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Matrix

/-! ### Heights of all ten curvature minors -/

/-- The common height `S'` of all ten curvature minors at a selected start (paper,
`lem:allcurv`): `148 = 4 · 37` is the constant of `orbit_curvature_minor_height 5`, and
`64 = 4³` comes from `a ≤ 4 A q`. -/
def selectedAllMinorHeight (a A T : ℕ) : ℕ :=
  9472 * A ^ 3 * selectedGapHeight a A T ^ 3 / a ^ 2

/-- All ten curvature minors at a selected start lie in the common box. -/
theorem selected_curvature_minor_bound {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) {j l : ℕ}
    (hj : j < 5) (hl : l < 5) :
    |dq a b (i + j) * kq a b (i + l) - dq a b (i + l) * kq a b (i + j)| ≤
      (selectedAllMinorHeight a A T : ℕ) := by
  obtain ⟨hP, hk, hA⟩ := selectedStart_spec hmem hsT hi
  have hq : (0 : ℝ) < qq a b i := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (qq_pos hba (by omega))
  have hr := (le_div_iff₀ (pow_pos hq 3)).mp ((orbit_curvature_minor_height 5 hba
    (by omega) (show 1 ≤ selectedGapHeight a A T from Nat.le_add_left 1 _)
    (fun t ht => (hk t (by omega)).2) hj hl).trans_eq (by push_cast; ring) :
      _ ≤ 148 * (a : ℝ) * (selectedGapHeight a A T : ℝ) ^ 3 / (qq a b i : ℝ) ^ 3)
  have hh : |dq a b (i + j) * kq a b (i + l) - dq a b (i + l) * kq a b (i + j)| *
      (qq a b i : ℤ) ^ 3 ≤ 148 * (a : ℤ) * selectedGapHeight a A T ^ 3 := by
    exact_mod_cast hr
  exact le_cubic_height_div (abs_nonneg _) (by omega)
    (window_quotient_lower hba (by omega : i < P a b) hA) hh (by norm_num)

/-! ### Transport from the exterior coordinates to the old curvature vector -/

/-- The first three entries of a row of five gaps or drops. -/
def firstThree (x : Fin 5 → ℤ) : Fin 3 → ℤ := fun j => x (Fin.castLE (by decide) j)

/-- The first three columns of an orbit's pattern matrix give its curvature vector. -/
lemma firstThree_Mi (a b l : ℕ) :
    curvatureVector (firstThree (Mi a b l 0)) (firstThree (Mi a b l 1)) =
      orbitCurvatureVector a b l := by
  funext t
  fin_cases t <;> rfl

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
  have hm := piv_ne_zero h0
  set τ := piv p
  set m := p τ
  obtain ⟨b1, b2, b3, -, -, -, hD, -, hbas, hred, hRpos, n1, n2, n3⟩ := pattern_reduced_basis hm
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
    rw [det_mul, det_adjugate, Fintype.card_fin]; rfl
  have hNq : (N.map (Int.cast : ℤ → ℚ)).det = (N.det : ℚ) :=
    ((Int.castRingHom ℚ).map_det N).symm
  let r : ℚ := (m : ℚ) ^ 2 / ((Δ : ℚ) * κ)
  have hΔq : (Δ : ℚ) ≠ 0 := by exact_mod_cast hD
  have hκq : (κ : ℚ) ≠ 0 := by exact_mod_cast hκ
  have hr : r ≠ 0 := by
    have : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    positivity
  refine ⟨r • N.map (Int.cast : ℤ → ℚ), ?_, c, fun M hM => ?_⟩
  · rw [det_smul, hNq, hN]
    push_cast
    positivity
  have hlift (row : Fin 3) (j : Fin 5) : m * M row j = Lrow p τ j ⬝ᵥ piv3 (M row) := by
    have h := lift_row M τ row j
    rw [hM] at h
    exact h
  have hmem (row : Fin 3) : piv3 (M row) ∈ pivLat p := pivotPart_mem_pivLat hM row
  have spec := wcoord_spec hD (hbas _ (hmem 0)) (hbas _ (hmem 1)) hred hRpos n1 n2 n3
  refine ⟨?_, fun S hS t => ?_⟩
  · set w := piv3 (M 0) ⨯₃ piv3 (M 1)
    set W := curvatureVector (firstThree (M 0)) (firstThree (M 1))
    have hW : W = ![M 0 1 * M 1 2 - M 0 2 * M 1 1, -(M 0 0 * M 1 2 - M 0 2 * M 1 0),
        M 0 0 * M 1 1 - M 0 1 * M 1 0] := by
      funext t; fin_cases t <;> rfl
    -- `Cof · w = m² W`, by Binet–Cauchy
    have hCw : Cm *ᵥ w = m ^ 2 • W := by
      have l0 := hlift 0 0; have l1 := hlift 0 1; have l2 := hlift 0 2
      have k0 := hlift 1 0; have k1 := hlift 1 1; have k2 := hlift 1 2
      funext t
      simp only [Cm, cofRows, mulVec, of_apply, hW, Pi.smul_apply, smul_eq_mul]
      fin_cases t <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val_zero, cons_val_one,
          cons_val_two, head_cons, tail_cons, w, cross_dot_cross, ← l0, ← l1, ← l2, ← k0, ← k1,
          ← k2] <;>
        ring
    -- `Bᵀ w = Δ c`
    have hBw : Bt *ᵥ w = Δ • c (M 0) (M 1) := by
      obtain ⟨_, ⟨e0, e1, e2⟩, _⟩ := spec
      funext t
      simp only [Bt, mulVec, of_apply, Pi.smul_apply, smul_eq_mul]
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
    have htq : ((Δ : ℚ) * κ) * c (M 0) (M 1) t = (m : ℚ) ^ 2 * ((N *ᵥ W) t : ℤ) := by
      exact_mod_cast ht
    simp only [r, eq_intCast]
    field_simp
    linear_combination htq
  · exact wcoord_bound spec.2.2 (fun a => by rw [cross_apply_cyc]; exact hS _ _) t

end
end PierceLengthBound.FixedDividend
