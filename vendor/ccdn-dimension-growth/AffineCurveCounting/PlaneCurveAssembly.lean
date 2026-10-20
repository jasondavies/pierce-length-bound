module

public import AffineCurveCounting.NonabsolutePlaneCount
public import AffineCurveCounting.RationalPlaneAssembly

/-! The complete rational plane reduction to sharp finite-field counting.
The non-absolutely-irreducible case is bounded unconditionally by d². -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Real

/-- Every box on a rational irreducible plane curve which splits over a field
extension has at most d² integer points, independently of the radius. -/
theorem count_nonabsolute_plane_le {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 2) ℚ) (hf : Irreducible f) (hd : 0 < f.totalDegree)
    (hred : ¬ Irreducible (MvPolynomial.map (algebraMap ℚ F) f)) (B : ℝ) :
    count (zeroLocus f) B ≤ f.totalDegree ^ 2 := by
  classical
  let S := integralPoints (zeroLocus f) B
  let z : S → Fin 2 → ℚ := fun i => rationalPoint i.val
  have hi : Function.Injective z := by
    intro i j he
    apply Subtype.ext
    funext k
    exact Int.cast_injective (congrFun he k)
  have hz : ∀ i, eval (z i) f = 0 := fun i => (mem_integralPoints.mp i.property).2
  have h := nonabsolute_plane_points_card_le f hf hd hred z hi hz
  simpa only [Fintype.card_coe, S, count] using h

/-- The exact PlaneCurveBound target follows from the one remaining sharp
finite-field estimate. The rational nonabsolute case is fully discharged. -/
theorem planeCurveBound_of_sharp_residue_bound {C : ℝ}
    (hC : 0 ≤ C) (hres : SharpPlaneResidueBound C) : PlaneCurveBound := by
  let K := 2 * Real.exp 1 * affineNonzeroConstantBound C
  have hK : 0 < K := mul_pos (by positivity) (affineNonzeroConstantBound_pos C)
  refine ⟨K + 1, by linarith, ?_⟩
  intro f hf hd B hB
  have hG : 0 ≤ curveBound f.totalDegree B := by
    have h := degree_four_le_curveBound hd hB
    exact (by positivity : (0 : ℝ) ≤ (f.totalDegree : ℝ) ^ 4).trans h
  by_cases habs : Irreducible (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)) f)
  · exact (count_rational_plane_of_sharp_residue_bound f habs hd hB hC hres).trans
      (mul_le_mul_of_nonneg_right (by linarith) hG)
  · have hh := count_nonabsolute_plane_le f hf hd habs B
    have ht : (count (zeroLocus f) B : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by exact_mod_cast hh
    have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
    have hpow : (f.totalDegree : ℝ) ^ 2 ≤ (f.totalDegree : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
    have hb := ht.trans (hpow.trans (degree_four_le_curveBound hd hB))
    exact hb.trans (by nlinarith)

end
end AffineCurveCounting
