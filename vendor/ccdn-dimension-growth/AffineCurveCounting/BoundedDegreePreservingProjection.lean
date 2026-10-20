module

public import AffineCurveCounting.BoundedInfinityParameter
public import AffineCurveCounting.InfinityAvoidingProjection
public import AffineCurveCounting.DegreePreservingProjectionCount
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Every positive-degree prime affine curve in characteristic zero admits
an explicitly bounded integral linear plane projection preserving its degree.
The first coordinate is constructed by infinity avoidance and the second by
the quantitative primitive-element theorem. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- An unconditional bounded degree-preserving plane projection. Neither
geometric integrality nor a supplied function-field embedding is required. -/
theorem exists_bounded_degree_preserving_projection {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      Transcendental K ((Ideal.Quotient.mk I) (momentCoordinate K n k₀)) ∧
      ∀ g, aeval (![momentCoordinate K n k₀, momentCoordinate K n k₁]) g ∈ I ↔ f ∣ g := by
  obtain ⟨k₀, hk₀, havoid⟩ := exists_bounded_infinity_parameter (L := AlgebraicClosure K) I d hdegree
  obtain ⟨N, hrec⟩ := filtration_recurrence_of_infinity_avoidance I
    (momentCoordinate K n k₀) (momentCoordinate_homogeneous K n k₀) havoid
  have htrans := recurrence_parameter_transcendental I d hd hdegree _ N hrec
  obtain ⟨k₁, f, hk₁, hf, hfd, hker⟩ :=
    exists_degree_preserving_projection_of_infinity_avoidance
      (F := FractionRing (MvPolynomial (Fin n) K ⧸ I)) I d hd hdegree
      (momentCoordinate K n k₀) (momentCoordinate_homogeneous K n k₀) havoid
  exact ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, htrans, hker⟩

/-- The same bounded projection controls the loss of points on every finite
subset of the actual source curve by d(d-1). -/
theorem exists_bounded_projection_card_le {K : Type*} [Field K] [CharZero K]
    [DecidableEq (Fin 2 → K)] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) :
    ∃ (k₀ k₁ : ℕ) (f : MvPolynomial (Fin 2) K),
      k₀ ≤ n ^ 2 * d ∧ k₁ ≤ n * d ^ 2 ∧ Irreducible f ∧ f.totalDegree = d ∧
      (∀ g, aeval (![momentCoordinate K n k₀, momentCoordinate K n k₁]) g ∈ I ↔ f ∣ g) ∧
      ∀ S : Finset (Fin n → K), (∀ z ∈ S, ∀ g ∈ I, eval z g = 0) →
        S.card ≤ (S.image (fun z =>
          ![eval z (momentCoordinate K n k₀), eval z (momentCoordinate K n k₁)])).card +
            d * (d - 1) := by
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hu, hker⟩ :=
    exists_bounded_degree_preserving_projection I d hd hdegree
  refine ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, ?_⟩
  intro S hS
  let a := ![momentCoordinate K n k₀, momentCoordinate K n k₁]
  have ha (j : Fin 2) : (a j).totalDegree ≤ 1 := by
    fin_cases j <;> exact momentCoordinate_degree _ _ _
  have hc := degree_preserving_projection_card_le I a ha d hdegree hu f hf.ne_zero hfd hker S hS
  convert hc using 1
  congr 3
  funext z j
  fin_cases j <;> rfl

end
end AffineCurveCounting
