module

public import AffineCurveCounting.CoordinatePowerGeneration

/-! Once a linear parameter generates the degree filtration, a bounded moment
coordinate produces an actual degree-preserving plane equation. This combines
full function-field degree with the quantitative primitive-element theorem. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Build the bounded second projection coordinate and a plane equation of
exactly degree d from a parameter satisfying eventual filtered generation. -/
theorem exists_full_degree_primitive_projection {K F : Type*}
    [Field K] [CharZero K] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (d : ℕ) (hdegree : ∃ M : ℕ, ∃ c : ℤ, ∀ m ≥ M,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (l : MvPolynomial (Fin n) K) (hl : l.totalDegree ≤ 1)
    (he : algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l) =
      algebraMap (RatFunc K) F RatFunc.X)
    (N : ℕ) (hrec : ∀ m ≥ N, filteredCoordinateSpace I (m + 1) =
      filteredCoordinateSpace I m ⊔ (filteredCoordinateSpace I m).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l))) :
    ∃ (k : ℕ) (f : MvPolynomial (Fin 2) K), k ≤ n * d ^ 2 ∧
      Irreducible f ∧ f.totalDegree = d ∧
      ∀ g, aeval (![l, momentCoordinate K n k]) g ∈ I ↔ f ∣ g := by
  obtain ⟨hfinite, hfull⟩ := curve_parameter_full_degree_of_recurrence I d hdegree l hl he N hrec
  let : Module.Finite (RatFunc K) F := hfinite
  let φ := IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I) F
  have hu : Transcendental K ((Ideal.Quotient.mk I) l) := by
    intro h
    have hh := (isAlgebraic_algHom_iff φ (IsFractionRing.injective _ _)).mpr h
    change IsAlgebraic K (algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) l)) at hh
    rw [he] at hh
    exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom K (RatFunc K) F) (algebraMap (RatFunc K) F).injective).mp hh)
  obtain ⟨k, hk, hprim⟩ := exists_bounded_curve_primitive_element (R := RatFunc K) (F := F) I
  let a : Fin 2 → MvPolynomial (Fin n) K := ![l, momentCoordinate K n k]
  have ha (i : Fin 2) : (a i).totalDegree ≤ 1 := by
    fin_cases i
    · exact hl
    · exact momentCoordinate_degree K n k
  obtain ⟨f, hf, hker⟩ := exists_plane_projection_equation I a ha d hdegree 0 hu
  have hp : IntermediateField.adjoin (RatFunc K) {φ ((Ideal.Quotient.mk I) (a 1))} = ⊤ := by
    change IntermediateField.adjoin (RatFunc K)
      {algebraMap (MvPolynomial (Fin n) K ⧸ I) F ((Ideal.Quotient.mk I) (momentCoordinate K n k))} = ⊤
    rwa [momentCoordinate_fraction]
  have hfd := plane_projection_degree_eq_of_full_parameter I a ha d hdegree φ f hf.ne_zero hker
    0 1 RatFunc.X RatFunc.transcendental_X he hp hfull
  refine ⟨k, f, by simpa only [hfull] using hk, hf, hfd, ?_⟩
  intro g
  have hg : aeval a g ∈ I ↔ g ∈ RingHom.ker (projectionCoordinateMap I a) := by
    change _ ↔ (Ideal.Quotient.mk I) (aeval a g) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  rw [hg, hker, Ideal.mem_span_singleton]

end
end AffineCurveCounting
