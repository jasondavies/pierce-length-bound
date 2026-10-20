/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendHyperplaneDegree

/-! Bounded polynomial sections of prime curves, using their filtered Hilbert degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Distinct points in a proper polynomial section force a corresponding lower
bound for the filtered coordinate-space growth. -/
theorem polynomial_points_filtered_lower {K σ ι : Type*} [Field K] [Finite σ]
    [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ coordinateZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    ∃ D : ℕ, ∀ N : ℕ,
      Fintype.card ι * (N + 1) ≤ Module.finrank K (filteredCoordinateSpace p (D + m * N)) := by
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
        filteredCoordinateSpace p (D + m * N) := by
    apply Submodule.mem_map.mpr
    refine ⟨h t.1 * l ^ t.2.val, ?_, by simp⟩
    rw [MvPolynomial.mem_restrictTotalDegree]
    have hh : (h t.1).totalDegree ≤ D  :=
      Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ t.1)
    have hp : (l ^ t.2.val).totalDegree ≤ m * N :=
      (MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left _ hld).trans (by nlinarith [t.2.isLt]))
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hh hp)
  let v : ι × Fin (N + 1) → filteredCoordinateSpace p (D + m * N) :=
    fun t => ⟨(Ideal.Quotient.mk p) (h t.1) * ((Ideal.Quotient.mk p) l) ^ t.2.val, hmem t⟩
  have hv : LinearIndependent K v :=
    LinearIndependent.of_comp (filteredCoordinateSpace p (D + m * N)).subtype hlin
  simpa using hv.fintype_card_le_finrank

/-- A proper polynomial section of a prime curve contains at most the product
of the polynomial degree and its affine Hilbert degree many distinct points. -/
theorem polynomial_section_card_le_degree {K σ ι : Type*} [Field K] [Finite σ]
    [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (d : ℕ)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c)
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ coordinateZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    Fintype.card ι ≤ m * d := by
  obtain ⟨D, hD⟩ := polynomial_points_filtered_lower p l hl m hld z hz hzp hzl
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  by_contra h
  have hcard : m * d + 1 ≤ Fintype.card ι := by omega
  let N := d * D + c.natAbs + N₀ + 1
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hm0 ▸ hld))
    have hi : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i⟩ := hi
    have hz0 := hzl i
    rw [he, MvPolynomial.eval_C] at hz0
    exact hl (by rw [he, hz0, map_zero]; exact p.zero_mem)
  have hlow := hD N
  have hlevel : N₀ ≤ D + m * N := by
    have hmul := Nat.mul_le_mul_right N hm
    have hN : N₀ ≤ N := by dsimp [N]; omega
    omega
  have he := hN₀ (D + m * N) hlevel
  push_cast at he
  have hlo : ((Fintype.card ι : ℕ) : ℤ) * (N + 1) ≤ (d : ℤ) * (D + m * N) + c := by
    rw [← he]
    exact_mod_cast hlow
  have hmul : ((m : ℤ) * d + 1) * (N + 1) ≤ (Fintype.card ι : ℤ) * (N + 1) := by
    exact_mod_cast Nat.mul_le_mul_right (N + 1) hcard
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = d * D + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith


end
end PierceLengthBound.FixedDividend
