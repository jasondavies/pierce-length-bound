/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountCoordinates
public import PierceLengthBound.HypersurfacePatternCountGrid
public import PierceLengthBound.HypersurfacePatternCountLattice
public import PierceLengthBound.LatticeExterior

/-!
# Polynomial zeros in cross-congruence fibers

The fiber estimate of the hypersurface-pattern count: for `X ≥ n`, a nonzero ternary
rational polynomial of degree `D` has at most `243 D X² / (n μ)` zeros in the box
`[-X, X]³` of the lattice `ℤu + nℤ³`, where `μ = normalShortR n u`. The sum of
`1 / μ` over the chart fibers is bounded in `HypersurfacePatternCountWeights`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Matrix

open Classical in
/-- For every `u` and `X ≥ n`, a nonzero polynomial of degree `D` vanishes at most
`243 D X² / (n μ)` times on the box `[-X, X]³` of `ℤu + nℤ³`. -/
theorem crossSpanLattice_polynomial_fiber_count {n X : ℕ} (hn : 0 < n) (hX : n ≤ X)
    (u : Fin 3 → ℤ) {f : MvPolynomial (Fin 3) ℚ} (hf : f ≠ 0) :
    (((ibox3 X).filter fun v => v ∈ crossSpanLattice n u ∧
      eval (fun i => (v i : ℚ)) f = 0).card : ℝ) ≤
      243 * f.totalDegree * (X : ℝ) ^ 2 / (n * (normalShortR n u : ℝ)) := by
  classical
  have hΛ : ∀ x : Fin 3 → ℤ, (∀ j, (n : ℤ) ∣ x j) → x ∈ crossSpanLattice n u :=
    fun _ hx => mem_crossSpanLattice_of_dvd u hx
  obtain ⟨b1, b2, b3, h1, h2, h3, hD, _, hdvd, hred⟩ :=
    reduced_basis (Λ := crossSpanLattice n u) hn hΛ
  have hD2 : det3 b2 b3 b1 ≠ 0 := by rwa [det3_cyclic]
  have hD3 : det3 b3 b1 b2 ≠ 0 := by rwa [det3_cyclic, det3_cyclic]
  have nb1 : 0 < nrm3 b1 := by
    have h := nrm3_nonneg b1
    by_contra hnot
    have : b1 = 0 := nrm3_eq_zero (by omega)
    apply hD
    simp [this, det3_apply]
  have nb2 : 0 < nrm3 b2 := by
    have h := nrm3_nonneg b2
    by_contra hnot
    have : b2 = 0 := nrm3_eq_zero (by omega)
    apply hD
    simp [this, det3_apply]
  have nb3 : 0 < nrm3 b3 := by
    have h := nrm3_nonneg b3
    by_contra hnot
    have : b3 = 0 := nrm3_eq_zero (by omega)
    apply hD
    simp [this, det3_apply]
  let ℓ : Fin 3 → ℝ := fun i => Real.sqrt (nrm3 (![b1, b2, b3] i) : ℝ)
  have hℓ : ∀ i, 0 < ℓ i := by
    intro i
    apply Real.sqrt_pos.mpr
    fin_cases i
    · exact_mod_cast nb1
    · exact_mod_cast nb2
    · exact_mod_cast nb3
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hXR : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le hn hX)
  have hμR : (0 : ℝ) < normalShortR n u := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (normalShortR_spec hn u).1)
  have hsmall : ∀ i, ℓ i ≤ 3 * (X : ℝ) := by
    obtain ⟨hn1, hn2, hn3⟩ := reduced_basis_norm_le hn hΛ hD hdvd hred
    have small (b : Fin 3 → ℤ) (hb : 27 * nrm3 b ≤ 64 * (n : ℤ) ^ 2) :
        Real.sqrt (nrm3 b : ℝ) ≤ 3 * (X : ℝ) := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ nrm3 b by exact_mod_cast nrm3_nonneg b)
      have hbR : 27 * (nrm3 b : ℝ) ≤ 64 * (n : ℝ) ^ 2 := by exact_mod_cast hb
      have hnX : (n : ℝ) ≤ X := by exact_mod_cast hX
      have hnX2 : (n : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 :=
        pow_le_pow_left₀ hnR.le hnX 2
      nlinarith [Real.sqrt_nonneg (nrm3 b : ℝ), sq_nonneg (X : ℝ)]
    intro i
    fin_cases i
    · exact small b1 hn1
    · exact small b2 hn2
    · exact small b3 hn3
  have pair (x y : Fin 3 → ℤ) (hx : x ∈ crossSpanLattice n u)
      (hy : y ∈ crossSpanLattice n u) (hxy : x ⨯₃ y ≠ 0) :
      (n : ℝ) * normalShortR n u ≤ Real.sqrt (nrm3 x : ℝ) * Real.sqrt (nrm3 y : ℝ) := by
    have hp := crossSpanLattice_pair_norm_bound hn hx hy hxy
    have hx0 : (0 : ℝ) ≤ nrm3 x := by exact_mod_cast nrm3_nonneg x
    have hy0 : (0 : ℝ) ≤ nrm3 y := by exact_mod_cast nrm3_nonneg y
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt hy0]
    exact_mod_cast hp
  have hp01 : (n : ℝ) * normalShortR n u ≤ ℓ 0 * ℓ 1 :=
    pair b1 b2 h1 h2 (cross_ne_zero_of_det3 hD3)
  have hp12 : (n : ℝ) * normalShortR n u ≤ ℓ 1 * ℓ 2 :=
    pair b2 b3 h2 h3 (cross_ne_zero_of_det3 hD)
  have hp20 : (n : ℝ) * normalShortR n u ≤ ℓ 2 * ℓ 0 :=
    pair b3 b1 h3 h1 (cross_ne_zero_of_det3 hD2)
  have hpair : ∀ i j, i ≠ j → (n : ℝ) * normalShortR n u ≤ ℓ i * ℓ j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at *
    · exact False.elim (hij rfl)
    · exact hp01
    · convert hp20 using 1
      ring
    · convert hp01 using 1
      ring
    · exact False.elim (hij rfl)
    · exact hp12
    · exact hp20
    · convert hp12 using 1
      ring
    · exact False.elim (hij rfl)
  let C : Matrix (Fin 3) (Fin 3) ℚ := fun j i => ((![b1, b2, b3] i) j : ℚ)
  have hdet : C.det = (det3 b1 b2 b3 : ℚ) := by
    rw [Matrix.det_fin_three]
    simp [C, det3_apply]
    ring
  have hC : C.det ≠ 0 := by rw [hdet]; exact_mod_cast hD
  let T := (ibox3 X).filter fun v => v ∈ crossSpanLattice n u
  have hcoord : ∀ w ∈ T, ∃ y : Fin 3 → ℤ,
      C *ᵥ (fun i => (y i : ℚ)) = (fun i => (w i : ℚ)) ∧
      ∀ i, ℓ i * |(y i : ℝ)| ≤ 3 * (X : ℝ) := by
    intro w hw
    obtain ⟨hwbox, hwΛ⟩ := Finset.mem_filter.mp hw
    refine ⟨ycoord b1 b2 b3 w, ?_, ?_⟩
    · funext j
      have hr := ycoord_repr hD (hdvd w hwΛ) j
      dsimp only [C]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      norm_num only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero]
      exact_mod_cast (by nlinarith [hr] :
        b1 j * ycoord b1 b2 b3 w 0 + (b2 j * ycoord b1 b2 b3 w 1 +
        b3 j * ycoord b1 b2 b3 w 2) = w j)
    · exact fun i => reduced_ycoord_real_bound hD (hdvd w hwΛ) hred
        (fun j => by
          have hj := (Fintype.mem_piFinset.mp hwbox) j
          exact abs_le.mpr (Finset.mem_Icc.mp hj)) i
  have hc := polynomial_integer_set_count_of_coordinates hf T C hC hXR
    (mul_pos hnR hμR) ℓ hℓ hsmall hpair hcoord
  simpa only [T, Finset.filter_filter] using hc

/-- For `u` primitive modulo `n`, `ℤu + nℤ³` is the solution set of `u × v ≡ 0 (mod n)`,
so the same bound counts the zeros of `f` among these solutions. -/
theorem primitive_cross_congruence_polynomial_fiber_count {n X : ℕ}
    (hn : 0 < n) (hX : n ≤ X) (u : Fin 3 → ℤ) (hu : gcd4 n u = 1)
    {f : MvPolynomial (Fin 3) ℚ} (hf : f ≠ 0) :
    (((ibox3 X).filter fun v => (∀ j, (n : ℤ) ∣ (u ⨯₃ v) j) ∧
      eval (fun i => (v i : ℚ)) f = 0).card : ℝ) ≤
      243 * f.totalDegree * (X : ℝ) ^ 2 / (n * (normalShortR n u : ℝ)) := by
  classical
  simpa only [← primitive_cross_congruence_iff hn hu] using
    crossSpanLattice_polynomial_fiber_count hn hX u hf

end
end PierceLengthBound.FixedDividend
