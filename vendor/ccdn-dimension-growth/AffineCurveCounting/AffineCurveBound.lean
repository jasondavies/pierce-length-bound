module

public import AffineCurveCounting.AffineProjectionCount
public import AffineCurveCounting.ProjectionScaleAbsorption

/-! The full coefficient-uniform affine curve counting theorem, with constants
depending only on ambient dimension and with the exact degree dependence in
CCDN Theorem 3. All projection and plane-counting inputs are proved. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- The full affine counting target is unconditional. -/
theorem affineCurveBound : AffineCurveBound := by
  obtain ⟨C, hC, hplane⟩ := planeCurveBound
  intro n _hn
  let K := Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)
  have hK : 0 < K := by
    have := projectionLogConstant_nonneg n
    dsimp [K]
    positivity
  refine ⟨C * K + 1, by positivity, ?_⟩
  intro I hI d hd hdegree B hB
  let : I.IsPrime := hI
  obtain ⟨f, hf, hfd, hred⟩ := exists_plane_count_reduction I d hd hdegree
  have hbox : 1 ≤ projectionBoxFactor n d * B :=
    one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le n d) hB
  have hp := hplane f hf (hfd.symm ▸ hd) _ hbox
  rw [hfd] at hp
  have hredR : (count (idealZeroLocus I) B : ℝ) ≤
      count (zeroLocus f) (projectionBoxFactor n d * B) + (d * (d - 1) : ℕ) := by
    exact_mod_cast hred B hB
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have herr : ((d * (d - 1) : ℕ) : ℝ) ≤ curveBound d B := by
    calc
      _ ≤ (d : ℝ) ^ 2 := by
        exact_mod_cast (show d * (d - 1) ≤ d ^ 2 by
          simpa only [pow_two] using Nat.mul_le_mul_left d (Nat.sub_le d 1))
      _ ≤ (d : ℝ) ^ 4 := by nlinarith [one_le_pow₀ hd1 (n := 2), sq_nonneg ((d : ℝ) ^ 2 - 1)]
      _ ≤ _ := degree_four_le_curveBound hd hB
  calc
    _ ≤ (count (zeroLocus f) (projectionBoxFactor n d * B) : ℝ) + (d * (d - 1) : ℕ) := hredR
    _ ≤ C * curveBound d (projectionBoxFactor n d * B) + curveBound d B := add_le_add hp herr
    _ ≤ C * (K * curveBound d B) + curveBound d B := by
      exact add_le_add (mul_le_mul_of_nonneg_left (projection_curveBound_scale n hd hB) hC.le) le_rfl
    _ = _ := by ring

end
end AffineCurveCounting
