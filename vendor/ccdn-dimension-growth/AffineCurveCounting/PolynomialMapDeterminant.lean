module

public import AffineCurveCounting.PlaneAuxiliarySelection

/-! The determinant comparison for polynomial homogeneous-coordinate maps of
actual integer plane-curve points. The residue geometry is supplied by the
original plane equation, so coordinates such as (H,x,y) need no rational rows. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix Real

lemma eval_polynomial_coordinate_map {R : Type*} [CommRing R] {n m : ℕ}
    (τ : Fin m → MvPolynomial (Fin n) R) (g : MvPolynomial (Fin m) R) (z : Fin n → R) :
    eval z (aeval τ g) = eval (fun j => eval z (τ j)) g := by
  change eval z (eval₂ C τ g) = _
  rw [← eval_assoc]
  rfl

lemma polynomial_coordinate_evaluation_matrix {M s : ℕ}
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ) :
    (Matrix.of fun i k => eval (z i) (aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ)))) =
      evaluationMatrix (homogeneousMonomials 2 M) (fun i j => eval (z i) (τ j)) := by
  ext i k
  change eval (z i) (aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ))) =
    (homogeneousMonomials 2 M k).prod (fun j e => eval (z i) (τ j) ^ e)
  have h := eval_polynomial_coordinate_map τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ)) (z i)
  simpa only [eval_monomial, one_mul] using h

/-- The complete comparison on the image of any polynomial coordinate map.
Bad-prime estimates are proved; the sharp finite-field count stays explicit. -/
theorem polynomial_map_no_auxiliary_height_comparison
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    (q : MvPolynomial (Fin 2) ℤ) (hqdegree : q.totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) q))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(q.coeff m : ℝ)| ≤ H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, eval (z i) q = 0)
    (himage : ∀ i, eval (fun j => eval (z i) (τ j)) f = 0)
    {B C : ℝ} (hB : 1 ≤ B)
    (hbox : ∀ i j, |(eval (z i) (τ j) : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (fun j => eval (z i) (τ j)) g = 0) → f ∣ g)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) q) →
      (Nat.card (PlaneResidue q p) : ℝ) ≤ p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ s : ℕ, 0 < s ∧ s + (2 + (M - d)).choose (M - d) = (2 + M).choose M ∧
      2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
        Real.log (1 + Real.log H / (d : ℝ) ^ 2) - heightDeterminantError C) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM
      (fun i j => eval (z i) (τ j)) himage hB hbox hrel
  have hs := (plane_homogeneous_rank_bounds hd hdM hr).1
  refine ⟨s, hs, hr, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let g := fun k => aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ))
  have he := polynomial_coordinate_evaluation_matrix (M := M) τ (z ∘ a)
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i k => eval ((z ∘ a) i) (g k)).map ((↑) : ℤ → ℚ)).row := by
    rw [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he]
    exact hi
  have hqpos : 0 < q.totalDegree := by simpa only [hqdegree] using hd
  have hcount' := hcount
  rw [← hqdegree] at hcount'
  have hlower := singular_determinant_log_lower_height hs q hqpos hir H hH hcoeff
    g (z ∘ a) (fun i => hz (a i)) hi' hC hcount'
  rw [hqdegree, show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he] at hlower
  exact hlower.trans hupper

end
end AffineCurveCounting
