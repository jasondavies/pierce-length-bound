module

public import AffineCurveCounting.AffinePlaneAssembly

/-! Rational equations and the coefficient-uniform affine plane bound.
The sharp finite-field estimate is stated as a proposition, not an axiom. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Real

/-- The remaining finite-field counting obligation, with one absolute constant.
`SharpPlaneCount.sharpPlaneResidueBound` discharges this input with constant 161. -/
def SharpPlaneResidueBound (C : ℝ) : Prop :=
  ∀ f : MvPolynomial (Fin 2) ℤ, 0 < f.totalDegree →
    ∀ p : ℕ, p.Prime → 27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) f) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p

lemma rational_scalar_model_irreducible_charZero {F σ : Type*} [Field F] [CharZero F]
    {f : MvPolynomial σ ℚ} {g : MvPolynomial σ ℤ} {a : ℚ} (ha : a ≠ 0)
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f)
    (hf : Irreducible (MvPolynomial.map (algebraMap ℚ F) f)) :
    Irreducible (MvPolynomial.map (Int.castRingHom F) g) := by
  have hh := congrArg (MvPolynomial.map (algebraMap ℚ F)) he
  rw [map_map, map_mul, map_C] at hh
  have hc : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by ext; simp
  rw [hc] at hh
  rw [hh]
  have hu : IsUnit (C ((algebraMap ℚ F) a) : MvPolynomial σ F) :=
    ((isUnit_iff_ne_zero.mpr ha).map (algebraMap ℚ F)).map C
  exact (irreducible_isUnit_mul hu).mpr hf

/-- A rational absolutely irreducible equation has the affine bound for every
real B>=1. Primitive normalization and every analytic reduction are proved;
the sharp finite-field bound is the one explicit counting hypothesis. -/
theorem count_rational_plane_of_sharp_residue_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f : MvPolynomial (Fin 2) ℚ)
    (hir : Irreducible (MvPolynomial.map (algebraMap ℚ F) f)) (hd : 0 < f.totalDegree)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) (hres : SharpPlaneResidueBound C) :
    (count (zeroLocus f) B : ℝ) ≤
      (2 * Real.exp 1 * affineNonzeroConstantBound C) * curveBound f.totalDegree B := by
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨g, a, hg, ha, he⟩ := exists_primitive_integer_model f hf0
  have hdeg := rational_scalar_model_degree ha hf0 he
  have hgi := rational_scalar_model_irreducible_charZero ha he hir
  have hgd : 0 < g.totalDegree := by rwa [hdeg]
  have hzero : zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) g) = zeroLocus f := by
    ext x
    exact rational_scalar_model_zero_iff ha he x
  have h := count_plane_of_sharp_residue_bound g hg hgi hgd hB hC (hres g hgd)
  rwa [hzero, hdeg] at h

/-- The finite-field input implies one constant uniform in all rational
absolutely irreducible plane equations, degrees, coefficients and box radii. -/
theorem absolute_plane_bound_of_sharp_residue_bound
    (F : Type*) [Field F] [CharZero F] [IsAlgClosed F]
    {C : ℝ} (hC : 0 ≤ C) (hres : SharpPlaneResidueBound C) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : MvPolynomial (Fin 2) ℚ,
      Irreducible (MvPolynomial.map (algebraMap ℚ F) f) → 0 < f.totalDegree →
      ∀ B : ℝ, 1 ≤ B → (count (zeroLocus f) B : ℝ) ≤ K * curveBound f.totalDegree B := by
  refine ⟨2 * Real.exp 1 * affineNonzeroConstantBound C, ?_, ?_⟩
  · exact mul_pos (by positivity) (affineNonzeroConstantBound_pos C)
  · intro f hir hd B hB
    exact count_rational_plane_of_sharp_residue_bound f hir hd hB hC hres

end
end AffineCurveCounting
