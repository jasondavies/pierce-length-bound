module

public import AffineCurveCounting.HeightDeterminant
public import AffineCurveCounting.PlaneChartDeterminant

/-! The actual affine-chart determinant comparison with coefficient-controlled
bad reduction. Only the sharp residue-point count remains an arithmetic input. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix Real

theorem plane_chart_no_auxiliary_height_comparison
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    (hdchart : 0 < (planeAffineChart f).totalDegree)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (Fin.cons 1 (z i)) g = 0) → f ∣ g)
    (hcount : ∀ p : ℕ, p.Prime → 27 * ((planeAffineChart f).totalDegree : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * ((planeAffineChart f).totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    ∃ s : ℕ, 0 < s ∧ s + (2 + (M - d)).choose (M - d) = (2 + M).choose M ∧
      2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log (planeAffineChart f).totalDegree -
        Real.log (1 + Real.log H / ((planeAffineChart f).totalDegree : ℝ) ^ 2) -
          heightDeterminantError C) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  have hz' : ∀ i, eval (Fin.cons 1 (z i)) f = 0 := by
    intro i
    rw [← planeAffineChart_eval]
    exact hz i
  have hbox' : ∀ (i : Fin t) (j : Fin 3),
      |(((Fin.cons (1 : ℤ) (z i) : Fin 3 → ℤ) j) : ℝ)| ≤ B := by
    intro i j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using hB
    · simpa using hbox i k
  obtain ⟨s, a, ha, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM
      (fun i => Fin.cons 1 (z i)) hz' hB hbox' hrel
  have hs := (plane_homogeneous_rank_bounds hd hdM hr).1
  refine ⟨s, hs, hr, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let g := fun k => planeAffineChart (monomial (homogeneousMonomials 2 M k) 1)
  have he := planeAffineChart_evaluation_matrix (M := M) (z ∘ a)
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i k => eval ((z ∘ a) i) (g k)).map ((↑) : ℤ → ℚ)).row := by
    rw [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he]
    exact hi
  have hlower := singular_determinant_log_lower_height hs (planeAffineChart f) hdchart hir H hH hcoeff
    g (z ∘ a) (fun i => hz (a i)) hi' hC hcount
  rw [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he] at hlower
  exact hlower.trans hupper

end
end AffineCurveCounting
