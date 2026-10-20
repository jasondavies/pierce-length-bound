module

public import AffineCurveCounting.ScalarSpanDimension
public import AffineCurveCounting.InfinityParameterReduction

/-! Evaluating homogeneous polynomials at geometric infinity points has
L-linear rank at most the corresponding actual infinity Hilbert piece. The
source curve and its Hilbert function remain over the original field K. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def homogeneousPointEvaluation {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] (z : ι → σ → L) (m : ℕ) :
    homogeneousSubmodule σ K m →ₗ[K] (ι → L) :=
  LinearMap.pi (fun i => (aeval (z i)).toLinearMap.comp (homogeneousSubmodule σ K m).subtype)

/-- The L-span of evaluations of K-polynomials is controlled by the actual
infinity quotient; no geometric base-change degree assumption is needed. -/
theorem infinity_evaluation_span_finrank_le {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (z : ι → σ → L) (hz : ∀ i, z i ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I))
    (m : ℕ) :
    Module.finrank L (Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z (m + 1)))) ≤
      Module.finrank K (infinityGradedSpace I m) := by
  let V := homogeneousSubmodule σ K (m + 1)
  let : Module.Finite K V := Module.Finite.of_fg (homogeneousSubmodule_fg σ K (m + 1))
  let f := (infinityCoordinateMap I).toLinearMap.comp V.subtype
  let g := homogeneousPointEvaluation (K := K) z (m + 1)
  have hker : f.ker ≤ g.ker := by
    intro p hp
    have hpI : (p : MvPolynomial σ K) ∈ leadingInfinityIdeal I := hp
    apply LinearMap.mem_ker.mpr
    funext i
    exact hz i _ hpI
  have hrange : f.range ≤ infinityGradedSpace I m := by
    rintro _ ⟨p, rfl⟩
    refine ⟨⟨(Ideal.Quotient.mk I) p,
      ⟨p, (mem_restrictTotalDegree _ _ _).mpr p.property.totalDegree_le, rfl⟩⟩, ?_⟩
    change Ideal.Quotient.mk (projectiveInfinityIdeal I) (projectiveMonomialMap I (m + 1) _) =
      infinityCoordinateMap I p
    change _ = Ideal.Quotient.mk (projectiveInfinityIdeal I) (quotientRadialMap I p)
    rw [quotientRadialMap_homogeneous I p (m + 1) p.property]
  exact (finrank_scalar_span_range_le_of_ker_le f g hker).trans (Submodule.finrank_mono hrange)

/-- In stable degrees the same evaluation span has dimension at most d. -/
theorem infinity_evaluation_span_finrank_le_degree {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (z : ι → σ → L) (hz : ∀ i, z i ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I))
    {d N : ℕ} {b : ℤ} (hdegree : ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + b)
    (m : ℕ) (hm : N ≤ m) :
    Module.finrank L (Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z (m + 1)))) ≤ d := by
  exact (infinity_evaluation_span_finrank_le I z hz m).trans_eq
    (infinityGradedSpace_eventually_degree I hdegree m hm)

end
end AffineCurveCounting
