module

public import AffineCurveCounting.CurveRationalInverse

/-! An actual bounded integral plane projection of every prime affine curve
admits polynomial reconstruction of all original coordinates. The common
reconstruction denominator is proper, but has no uniform degree bound here. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Construct bounded integer linear projection coordinates and polynomial
identities giving a rational inverse on a nonempty open part of the curve. -/
theorem exists_bounded_curve_reconstruction {K F : Type*}
    [Field K] [CharZero K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (d : ℕ) (hd : 0 < d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) :
    ∃ (j : Fin n) (k : ℕ) (Q : MvPolynomial (Fin 2) K)
      (P : Fin n → MvPolynomial (Fin 2) K), k ≤ n * d ^ 2 ∧
      let a : Fin 2 → MvPolynomial (Fin n) K := ![X j, momentCoordinate K n k]
      aeval a Q ∉ I ∧ ∀ i, aeval a Q * X i - aeval a (P i) ∈ I := by
  obtain ⟨j, φ, k, hφ, hk, hfinite⟩ := exists_bounded_curve_primitive_pair (F := F) I d hd hdegree
  let q := IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F
  let a : Fin 2 → MvPolynomial (Fin n) K := ![X j, momentCoordinate K n k]
  have heq : (fun t => q ((Ideal.Quotient.mk I) (a t))) =
      (![φ RatFunc.X, q ((Ideal.Quotient.mk I) (momentCoordinate K n k))] : Fin 2 → F) := by
    funext t
    fin_cases t
    · exact hφ.symm
    · rfl
  have hgen : IntermediateField.adjoin K
      (Set.range (fun t => q ((Ideal.Quotient.mk I) (a t)))) = ⊤ := by
    rw [heq]
    exact primitive_ratFunc_pair_adjoin_top φ _ hfinite.2.2
  obtain ⟨Q, P, hQ, hP⟩ := exists_curve_reconstruction_identities I q
    (IsFractionRing.injective (MvPolynomial (Fin n) K ⧸ I) F) a hgen
  exact ⟨j, k, Q, P, hk, hQ, hP⟩

end
end AffineCurveCounting
