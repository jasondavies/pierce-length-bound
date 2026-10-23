/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendFilteredIntersection
public import PierceLengthBound.FixedDividendComponents

/-!
# Hyperplane sections and affine Hilbert degree

Separators at distinct points, multiplied by powers of a hyperplane equation,
produce independent classes. Their growth bounds the number of points in a
proper hyperplane section by the affine Hilbert degree.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Powers of a nonzero element times point separators are jointly independent
when that element vanishes under all point evaluations. -/
theorem separator_powers_independent {K A ι : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Finite ι] [DecidableEq ι]
    (φ : ι → A →ₐ[K] K) (h : ι → A) (l : A) (hl : l ≠ 0)
    (hzero : ∀ i, φ i l = 0)
    (hsep : ∀ i j, φ i (h j) = if i = j then 1 else 0) (N : ℕ) :
    LinearIndependent K (fun t : ι × Fin N => h t.1 * l ^ t.2.val) := by
  classical
  cases nonempty_fintype ι
  induction N with
  | zero => exact linearIndependent_empty_type
  | succ N ih =>
    rw [Fintype.linearIndependent_iff]
    intro a ha t
    have hconst (i : ι) : a (i, 0) = 0 := by
      have he := congrArg (φ i) ha
      simpa [Fintype.sum_prod_type, Fin.sum_univ_succ, hzero, hsep, eq_comm] using he
    have htail : ∑ t : ι × Fin N, a (t.1, t.2.succ) • (h t.1 * l ^ t.2.val) = 0 := by
      apply (mul_left_cancel₀ hl)
      rw [mul_zero, Finset.mul_sum]
      have he : (∑ t : ι × Fin (N + 1), a t • (h t.1 * l ^ t.2.val)) =
          ∑ t : ι × Fin N, l * (a (t.1, t.2.succ) • (h t.1 * l ^ t.2.val)) := by
        simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, hconst, zero_smul, zero_add]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        simp only [Fin.val_succ, pow_succ, Algebra.smul_def]
        ring
      rw [← he]
      exact ha
    have hcoeff := Fintype.linearIndependent_iff.mp ih
      (fun t => a (t.1, t.2.succ)) htail
    obtain ⟨i, k⟩ := t
    refine Fin.cases (hconst i) (fun k => hcoeff (i, k)) k

/-- Explicit polynomial interpolation at a finite family of distinct affine points. -/
theorem exists_point_separators {K σ ι : Type*} [Field K] [Finite ι] [DecidableEq ι]
    (z : ι → σ → K) (hz : Function.Injective z) :
    ∃ h : ι → MvPolynomial σ K, ∀ i j,
      MvPolynomial.eval (z i) (h j) = if i = j then 1 else 0 := by
  classical
  cases nonempty_fintype ι
  have hex (i : ι) : ∃ h : MvPolynomial σ K,
      MvPolynomial.eval (z i) h = 1 ∧
      ∀ j, j ≠ i → MvPolynomial.eval (z j) h = 0 := by
    have hcoords (j : {j : ι // j ≠ i}) : ∃ k, z i k ≠ z j.val k :=
      Function.ne_iff.mp (fun he => j.property (hz he).symm)
    choose k hk using hcoords
    let factor (j : {j : ι // j ≠ i}) : MvPolynomial σ K :=
      MvPolynomial.C ((z i (k j) - z j.val (k j))⁻¹) *
        (MvPolynomial.X (k j) - MvPolynomial.C (z j.val (k j)))
    refine ⟨∏ j, factor j, ?_, ?_⟩
    · rw [MvPolynomial.eval_prod]
      apply Finset.prod_eq_one
      intro j _
      simp only [factor, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_sub, MvPolynomial.eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hk j))
    · intro j hji
      rw [MvPolynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {j : ι // j ≠ i}))
      simp [factor]
  choose h hon hoff using hex
  refine ⟨h, ?_⟩
  intro i j
  by_cases he : i = j
  · subst j
    simpa using hon i
  · simpa [he] using hoff j i he

/-- Distinct points in a proper hyperplane section force a corresponding lower
bound for the filtered coordinate-space growth. -/
theorem hyperplane_points_filtered_lower {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (l : MvPolynomial σ K) (hl : l ∉ p) (hld : l.totalDegree ≤ 1)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ coordinateZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    ∃ D : ℕ, ∀ N : ℕ,
      Fintype.card ι * (N + 1) ≤ Module.finrank K (filteredCoordinateSpace p (D + N)) := by
  classical
  obtain ⟨h, hsep⟩ := exists_point_separators z hz
  let φ : ι → (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
    fun i => Ideal.Quotient.liftₐ p (MvPolynomial.aeval (z i)) (by
      intro f hf
      simpa only [MvPolynomial.aeval_eq_eval] using hzp i f hf)
  have hφ (i : ι) (f : MvPolynomial σ K) :
      φ i ((Ideal.Quotient.mk p) f) = MvPolynomial.eval (z i) f := by
    simp [φ, Ideal.Quotient.liftₐ_apply]
  let D := Finset.univ.sup (fun i => (h i).totalDegree)
  refine ⟨D, ?_⟩
  intro N
  have hlin := separator_powers_independent φ (fun i => (Ideal.Quotient.mk p) (h i))
    ((Ideal.Quotient.mk p) l) (fun hzero => hl (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
    (fun i => by rw [hφ]; exact hzl i)
    (fun i j => by rw [hφ]; exact hsep i j) (N + 1)
  have hmem (t : ι × Fin (N + 1)) :
      (Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val ∈
        filteredCoordinateSpace p (D + N) := by
    apply Submodule.mem_map.mpr
    refine ⟨h t.1 * l ^ t.2.val, ?_, by simp⟩
    rw [MvPolynomial.mem_restrictTotalDegree]
    have hh : (h t.1).totalDegree ≤ D  :=
      Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ t.1)
    have hp : (l ^ t.2.val).totalDegree ≤ N :=
      (MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left _ hld).trans (by simp; omega))
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hh hp)
  let v : ι × Fin (N + 1) → filteredCoordinateSpace p (D + N) :=
    fun t => ⟨(Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val, hmem t⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace p (D + N)).subtype hlin
  simpa using hv.fintype_card_le_finrank

/-- A proper hyperplane section of a prime curve contains at most its affine
Hilbert degree many distinct rational points. -/
theorem hyperplane_section_card_le_degree {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (d : ℕ)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c)
    (l : MvPolynomial σ K) (hl : l ∉ p) (hld : l.totalDegree ≤ 1)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ coordinateZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    Fintype.card ι ≤ d := by
  obtain ⟨D, hD⟩ := hyperplane_points_filtered_lower p l hl hld z hz hzp hzl
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  by_contra h
  have hcard : d + 1 ≤ Fintype.card ι := by omega
  let N := d * D + c.natAbs + N₀ + 1
  have hlow := hD N
  have he := hN₀ (D + N) (by dsimp [N]; omega)
  push_cast at he
  have hlo : ((Fintype.card ι : ℕ) : ℤ) * (N + 1) ≤ (d : ℤ) * (D + N) + c := by
    rw [← he]
    exact_mod_cast hlow
  have hmul : (d + 1 : ℤ) * (N + 1) ≤ (Fintype.card ι : ℤ) * (N + 1) := by
    exact_mod_cast Nat.mul_le_mul_right (N + 1) hcard
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = d * D + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith

/-- Any affine plane through three distinct points of a degree-two prime curve
contains the entire curve. This form applies directly to three actual gap points. -/
theorem degree_two_plane_mem_of_three_points {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime]
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = 2 * n + c)
    (l : MvPolynomial (Fin 3) K) (hld : l.totalDegree ≤ 1)
    (z : Fin 3 → Fin 3 → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ coordinateZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    l ∈ p := by
  by_contra hl
  have h := hyperplane_section_card_le_degree p 2 (by simpa using hdegree) l hl hld z hz hzp hzl
  norm_num at h

end
end PierceLengthBound.FixedDividend
