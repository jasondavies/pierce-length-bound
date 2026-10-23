/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.GraphFunctionField
public import PierceLengthBound.JointLiftGraphDegree

/-! Powered graphs: the graph coordinates `P j / D` are raised to individually chosen integer
powers `e j ≤ N`, with the base coordinates kept and the common denominator `D ^ N`. The powered
graph is prime with degree between `d` and `(N C + 1) d`. The orbit instance is the powered joint
graph `(nodes, Wᵐ, Jⁿ)` (paper, `Γ_{m,n}`). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Numerators for powers of coordinates with common denominator `D ^ N`. -/
def poweredGraphNumerators {K σ τ : Type*} [Field K]
    (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K) (e : τ → ℕ) (N : ℕ) :
    τ → MvPolynomial σ K := fun j => P j ^ e j * D ^ (N - e j)

lemma powered_fraction {F : Type*} [Field F] (p d : F) (hd : d ≠ 0)
    {e N : ℕ} (he : e ≤ N) : p ^ e * d ^ (N - e) / d ^ N = (p / d) ^ e := by
  have hpow : d ^ N = d ^ e * d ^ (N - e) := by
    rw [← pow_add, Nat.add_sub_of_le he]
  rw [hpow, mul_div_mul_right _ _ (pow_ne_zero _ hd), div_pow]

lemma poweredGraphNumerators_field {K σ τ F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : MvPolynomial σ K →ₐ[K] F) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (e : τ → ℕ) (N : ℕ) (he : ∀ j, e j ≤ N) (hD : φ D ≠ 0) (j : τ) :
    φ (poweredGraphNumerators P D e N j) / φ (D ^ N) = (φ (P j) / φ D) ^ e j := by
  simp only [poweredGraphNumerators, map_mul, map_pow]
  exact powered_fraction _ _ hD (he j)

/-- In the function field of `I`, the base coordinates are unchanged and each graph coordinate
is raised to its power `e j`. -/
lemma powered_jointGraphFieldCoordinates {K σ τ F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K)
    (e : τ → ℕ) (N : ℕ) (he : ∀ j, e j ≤ N)
    (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F) (hD : ι (Ideal.Quotient.mk I D) ≠ 0) :
    jointGraphFieldCoordinates I (poweredGraphNumerators P D e N) (D ^ N) ι =
      Sum.elim (fun j => jointGraphFieldCoordinates I P D ι (Sum.inl j))
        (fun j => jointGraphFieldCoordinates I P D ι (Sum.inr j) ^ e j) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j =>
    exact poweredGraphNumerators_field (ι.comp (Ideal.Quotient.mkₐ K I)) P D e N he hD j

lemma poweredGraphNumerators_totalDegree {K σ τ : Type*} [Field K]
    (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K) (e : τ → ℕ) (N C : ℕ)
    (he : ∀ j, e j ≤ N) (hP : ∀ j, (P j).totalDegree ≤ C) (hD : D.totalDegree ≤ C)
    (j : τ) : (poweredGraphNumerators P D e N j).totalDegree ≤ N * C := by
  have hp := (totalDegree_pow (P j) (e j)).trans (Nat.mul_le_mul_left _ (hP j))
  have hd := (totalDegree_pow D (N - e j)).trans (Nat.mul_le_mul_left _ hD)
  have h := (totalDegree_mul (P j ^ e j) (D ^ (N - e j))).trans (Nat.add_le_add hp hd)
  change _ ≤ N * C
  apply h.trans
  rw [← Nat.add_mul, Nat.add_sub_of_le (he j)]

/-- The powered graph over a prime curve of degree `d` is prime, of degree `δ` with
`d ≤ δ ≤ (N C + 1) d`, where `C` bounds the degrees of the numerators and the denominator. -/
theorem powered_jointGraph_degree_bounds {K σ τ : Type*} [Field K] [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (P : τ → MvPolynomial σ K) (D : MvPolynomial σ K) (hD : D ∉ I)
    (e : τ → ℕ) (N C : ℕ) (he : ∀ j, e j ≤ N)
    (hP : ∀ j, (P j).totalDegree ≤ C) (hDC : D.totalDegree ≤ C) {d : ℕ}
    (hd : ∃ M : ℕ, ∃ c : ℤ, ∀ k ≥ M,
      (Module.finrank K (filteredCoordinateSpace I k) : ℤ) = (d : ℤ) * k + c) :
    (jointGraphIdeal I (poweredGraphNumerators P D e N) (D ^ N)).IsPrime ∧
    ∃ δ : ℕ, d ≤ δ ∧ δ ≤ (N * C + 1) * d ∧ ∃ M : ℕ, ∃ c : ℤ, ∀ k ≥ M,
      (Module.finrank K
        (filteredCoordinateSpace (jointGraphIdeal I (poweredGraphNumerators P D e N) (D ^ N)) k)
        : ℤ) = (δ : ℤ) * k + c := by
  have hDN : D ^ N ∉ I := by
    intro h
    have hD0 : Ideal.Quotient.mk I D ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hD
    have : (Ideal.Quotient.mk I D) ^ N = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact h
    exact pow_ne_zero N hD0 this
  refine ⟨jointGraphIdeal_isPrime I _ _ hDN, ?_⟩
  apply jointGraph_degree_bounds I _ _ hDN (D := N * C + 1) _ _ hd
  · exact Nat.add_le_add_right
      ((totalDegree_pow D N).trans (Nat.mul_le_mul_left _ hDC)) 1
  · intro j
    exact (poweredGraphNumerators_totalDegree P D e N C he hP hDC j).trans (by omega)

/-- The three curvature coordinates use `m`; the rank-five coordinate uses `n`. -/
def jointCoordinatePowers (m n : ℕ) : Fin 4 → ℕ := ![m, m, m, n]

@[simp] lemma jointCoordinatePowers_castSucc (m n : ℕ) (j : Fin 3) :
    jointCoordinatePowers m n j.castSucc = m := by
  fin_cases j <;> rfl

lemma jointCoordinatePowers_le (m n : ℕ) (j : Fin 4) :
    jointCoordinatePowers m n j ≤ m + n := by
  fin_cases j <;> simp [jointCoordinatePowers]

/-- The powered numerators of the orbit graph `(nodes, Wᵐ, Jⁿ)`. -/
def orbitPoweredJointNumerators (a b i m n : ℕ) : Fin 4 → MvPolynomial (Fin 3) ℚ :=
  poweredGraphNumerators (orbitJointNumerators a b i) (orbitJointDenominator a b i)
    (jointCoordinatePowers m n) (m + n)

/-- The ideal of the powered orbit graph `(nodes, Wᵐ, Jⁿ)` (paper, `Γ_{m,n}`) over the
component `I`. -/
def orbitPoweredJointGraphIdeal (a b i m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    Ideal (MvPolynomial (Fin 3 ⊕ Fin 4) ℚ) :=
  jointGraphIdeal I (orbitPoweredJointNumerators a b i m n)
    (orbitJointDenominator a b i ^ (m + n))

end
end PierceLengthBound.FixedDividend
