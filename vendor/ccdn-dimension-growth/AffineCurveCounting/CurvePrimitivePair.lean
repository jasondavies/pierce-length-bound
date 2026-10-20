module

public import AffineCurveCounting.BoundedPrimitiveElement

/-! Actual bounded linear coordinates generating an affine curve's function
field. Degree preservation and control of exceptional fibers are separate
projection obligations; this module proves the quantified birational input. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The bounded integer moment-curve linear form. -/
def momentCoordinate (K : Type*) [CommRing K] (n k : ℕ) : MvPolynomial (Fin n) K :=
  ∑ j : Fin n, C ((k : K) ^ j.val) * X j

lemma momentCoordinate_degree (K : Type*) [CommRing K] [Nontrivial K] (n k : ℕ) :
    (momentCoordinate K n k).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])

lemma momentCoordinate_fraction {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F] (k : ℕ) :
    algebraMap (MvPolynomial (Fin n) K ⧸ I) F
      ((Ideal.Quotient.mk I) (momentCoordinate K n k)) =
      ∑ j : Fin n, algebraMap (MvPolynomial (Fin n) K ⧸ I) F
        ((Ideal.Quotient.mk I) (X j)) * (k : F) ^ j.val := by
  simp only [momentCoordinate, map_sum, map_mul, map_pow, map_natCast]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Positive-degree curves have an actual coordinate and a bounded integer
linear form generating the function field as a field over K. The field over
the first coordinate has finite degree at most d. -/
theorem exists_bounded_curve_primitive_pair {K F : Type*} [Field K] [CharZero K] [Field F]
    [Algebra K F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (d : ℕ) (hd : 0 < d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) :
    ∃ (j : Fin n) (φ : RatFunc K →ₐ[K] F) (k : ℕ),
      φ RatFunc.X = algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) (X j)) ∧
      k ≤ n * d ^ 2 ∧
      let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
      Module.Finite (RatFunc K) F ∧ Module.finrank (RatFunc K) F ≤ d ∧
      IntermediateField.adjoin (RatFunc K)
        {algebraMap (MvPolynomial (Fin n) K ⧸ I) F
          ((Ideal.Quotient.mk I) (momentCoordinate K n k))} = ⊤ := by
  obtain ⟨j, φ, hφ, hf⟩ := exists_curve_rational_parameter (F := F) I d hd hdegree
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algHom φ
  let : Module.Finite (RatFunc K) F := hf.1
  obtain ⟨k, hk, hprim⟩ := exists_bounded_curve_primitive_element (R := RatFunc K) (F := F) I
  refine ⟨j, φ, k, hφ, hk.trans (Nat.mul_le_mul_left n (Nat.pow_le_pow_left hf.2 2)), hf.1, hf.2, ?_⟩
  rwa [momentCoordinate_fraction]

end
end AffineCurveCounting
