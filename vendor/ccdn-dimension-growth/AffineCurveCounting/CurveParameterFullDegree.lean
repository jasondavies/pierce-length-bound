module

public import AffineCurveCounting.ParameterRecurrenceGrowth

/-! Eventual generation of the affine degree filtration by a linear parameter
forces the actual function-field extension to have the full Hilbert degree. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- A linear parameter generating the filtration in large degrees has full
function-field degree d, not merely the previously proved upper bound. -/
theorem curve_parameter_full_degree_of_recurrence {K F σ : Type*}
    [Field K] [Field F] [Fintype σ] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ) (hdegree : ∃ M : ℕ, ∃ c : ℤ, ∀ n ≥ M,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1)
    (he : algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) l) =
      algebraMap (RatFunc K) F RatFunc.X)
    (N : ℕ) (hrec : ∀ n ≥ N, filteredCoordinateSpace I (n + 1) =
      filteredCoordinateSpace I n ⊔ (filteredCoordinateSpace I n).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l))) :
    Module.Finite (RatFunc K) F ∧ Module.finrank (RatFunc K) F = d := by
  obtain ⟨hfinite, hupper⟩ := curve_functionField_finite_rank_le I d hdegree l hl
    RatFunc.X RatFunc.transcendental_X he
  let : Module.Finite (RatFunc K) F := hfinite
  let φ := IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F
  have hcomm (x : MvPolynomial σ K ⧸ I) :
      φ.toLinearMap ((LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) x) =
        algebraMap (RatFunc K) F RatFunc.X * φ.toLinearMap x := by
    change φ (((Ideal.Quotient.mk I) l) * x) = _
    rw [map_mul]
    exact congrArg (fun y => y * φ x) he
  have hlower := parameter_recurrence_slope_le (filteredCoordinateSpace I)
    (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l)) φ.toLinearMap
    (IsFractionRing.injective _ _) hcomm N hrec d hdegree
  exact ⟨hfinite, Nat.le_antisymm hupper hlower⟩

end
end AffineCurveCounting
