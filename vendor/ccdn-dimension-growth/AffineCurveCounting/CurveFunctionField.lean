module

public import AffineCurveCounting.FunctionFieldRank
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-! A fraction field of an affine curve is finite over the field of a
transcendental linear parameter, of degree at most its affine Hilbert degree.
Common denominators transfer arbitrary field elements to polynomial classes. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

lemma field_common_multiple_independent {R F ι : Type*} [Field R] [Field F]
    [Algebra R F] [Fintype ι] [DecidableEq ι]
    (v : ι → F) (hv : LinearIndependent R v) (b : F) (hb : b ≠ 0) :
    LinearIndependent R (fun i => b * v i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : ∑ j, c j • v j = 0 := by
    apply mul_left_cancel₀ hb
    rw [mul_zero, Finset.mul_sum]
    simpa only [mul_smul_comm] using hc
  exact Fintype.linearIndependent_iff.mp hv c hz i

/-- Clearing a common denominator extends the polynomial rank bound to
arbitrary elements of the fraction field. -/
theorem fraction_parameter_rank_le {K R F σ ι : Type*} [Field K] [Field R] [Field F]
    [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F]
    [Fintype σ] [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1)
    (u : R) (hu : Transcendental K u)
    (he : algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) l) = algebraMap R F u)
    (v : ι → F) (hv : LinearIndependent R v) : Fintype.card ι ≤ d := by
  classical
  let A := MvPolynomial σ K ⧸ I
  let φ := IsScalarTower.toAlgHom K A F
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) v
  choose a ha using hb
  have hrep (i : ι) : ∃ h : MvPolynomial σ K, (Ideal.Quotient.mk I) h = a i :=
    Ideal.Quotient.mk_surjective (a i)
  choose h hh using hrep
  have hbne : algebraMap A F b.val ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  have hli := field_common_multiple_independent v hv (algebraMap A F b.val) hbne
  have hlin : LinearIndependent R (fun i => φ ((Ideal.Quotient.mk I) (h i))) := by
    convert hli using 1
    funext i
    rw [hh]
    exact (ha i).trans (Algebra.smul_def _ _)
  exact polynomial_parameter_rank_le I d hdegree φ l hl u hu he h hlin

/-- The genuine function-field extension is finite and has degree at most d. -/
theorem curve_functionField_finite_rank_le {K R F σ : Type*} [Field K] [Field R] [Field F]
    [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1)
    (u : R) (hu : Transcendental K u)
    (he : algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) l) = algebraMap R F u) :
    Module.Finite R F ∧ Module.finrank R F ≤ d := by
  have hrank : Module.rank R F ≤ (d : Cardinal) := by
    by_contra! hbad
    have hs : ((d + 1 : ℕ) : Cardinal) ≤ Module.rank R F := by
      simpa only [Nat.cast_add, Nat.cast_one] using Cardinal.add_one_le_of_lt hbad
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hs
    have hh := fraction_parameter_rank_le I d hdegree l hl u hu he v hv
    simp only [Fintype.card_fin] at hh
    omega
  let : Module.Finite R F := Module.rank_lt_aleph0_iff.mp
    (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  refine ⟨inferInstance, ?_⟩
  have hh := fraction_parameter_rank_le I d hdegree l hl u hu he
    (Module.finBasis R F) (Module.finBasis R F).linearIndependent
  simpa only [Fintype.card_fin] using hh

end
end AffineCurveCounting
