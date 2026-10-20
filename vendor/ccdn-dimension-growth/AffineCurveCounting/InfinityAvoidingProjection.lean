module

public import AffineCurveCounting.BoundedInfinityAvoidance
public import AffineCurveCounting.RecurrenceParameterTranscendence
public import AffineCurveCounting.FullDegreePrimitiveProjection

/-! An infinity-avoiding linear form gives a degree-preserving plane
projection. The parameter field and the second coordinate are constructed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- No function-field degree or parameter embedding is assumed: avoiding
infinity and the certified affine Hilbert degree suffice. -/
theorem exists_degree_preserving_projection_of_infinity_avoidance {K L F : Type*}
    [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (d : ℕ) (hd : 0 < d) (hdegree : ∃ M : ℕ, ∃ c : ℤ, ∀ m ≥ M,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (l : MvPolynomial (Fin n) K) (hl : l.IsHomogeneous 1)
    (hzero : ∀ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I ⊔ Ideal.span {l}), z = 0) :
    ∃ (k : ℕ) (f : MvPolynomial (Fin 2) K), k ≤ n * d ^ 2 ∧
      Irreducible f ∧ f.totalDegree = d ∧
      ∀ g, aeval (![l, momentCoordinate K n k]) g ∈ I ↔ f ∣ g := by
  obtain ⟨N, hrec⟩ := filtration_recurrence_of_infinity_avoidance I l hl hzero
  have hu := recurrence_parameter_transcendental I d hd hdegree l N hrec
  let u := algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l)
  have huF : Transcendental K u := by
    intro h
    exact hu ((isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F)
      (IsFractionRing.injective _ _)).mp h)
  let φ := transcendentalRatFuncMap u huF
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algHom φ
  apply exists_full_degree_primitive_projection (F := F) I d hdegree l hl.totalDegree_le
    _ N hrec
  exact (transcendentalRatFuncMap_X u huF).symm

end
end AffineCurveCounting
