module

public import AffineCurveCounting.CurveFunctionField
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! A positive affine Hilbert degree supplies an actual transcendental
coordinate. This constructs the parameter needed for the function-field bound. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma quotient_finite_of_algebraic_coordinates {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K))
    (ha : ∀ j, IsAlgebraic K ((Ideal.Quotient.mk I) (X j))) :
    Module.Finite K (MvPolynomial σ K ⧸ I) := by
  have hi (f : MvPolynomial σ K) : IsIntegral K ((Ideal.Quotient.mk I) f) := by
    induction f using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap
    | add f g hf hg => simpa only [map_add] using hf.add hg
    | mul_X f j hf => simpa only [map_mul] using hf.mul (ha j).isIntegral
  let : Algebra.IsIntegral K (MvPolynomial σ K ⧸ I) := ⟨fun a => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hi f⟩
  exact Algebra.IsIntegral.finite

/-- A positive linear Hilbert function excludes an algebraic coordinate ring. -/
theorem affine_degree_has_transcendental_coordinate {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (d : ℕ) (hd : 0 < d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ j, Transcendental K ((Ideal.Quotient.mk I) (X j)) := by
  classical
  by_contra! hn
  have ha (j : σ) : IsAlgebraic K ((Ideal.Quotient.mk I) (X j)) := by
    simpa only [Transcendental, not_not] using hn j
  let : Module.Finite K (MvPolynomial σ K ⧸ I) := quotient_finite_of_algebraic_coordinates I ha
  obtain ⟨N₀, c, hN₀⟩ := hdegree
  let r := Module.finrank K (MvPolynomial σ K ⧸ I)
  let N := r + c.natAbs + N₀ + 1
  have hN : N₀ ≤ N := by dsimp [N]; omega
  have he := hN₀ N hN
  have hbound := Submodule.finrank_le (filteredCoordinateSpace I N)
  have hb : (d : ℤ) * N + c ≤ r := by rw [← he]; exact_mod_cast hbound
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have habs : -(c.natAbs : ℤ) ≤ c := by
    have hh : -c ≤ ((-c).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at hh
    omega
  have hNeq : (N : ℤ) = r + c.natAbs + N₀ + 1 := by simp [N]
  nlinarith

/-- The same coordinate stays transcendental in the actual fraction field. -/
theorem affine_degree_fraction_transcendental_coordinate {K F σ : Type*}
    [Field K] [Field F] [Fintype σ] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ) (hd : 0 < d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ j, Transcendental K
      (algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (X j))) := by
  obtain ⟨j, hj⟩ := affine_degree_has_transcendental_coordinate I d hd hdegree
  refine ⟨j, ?_⟩
  exact fun h => hj ((isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ I) F)
    (IsFractionRing.injective _ _)).mp h)

end
end AffineCurveCounting
