module

public import AffineCurveCounting.HomogeneousDeterminantComparison
public import AffineCurveCounting.SingularDeterminantCutoff

/-! Assemble the upper and lower determinant estimates on an actual affine
chart of a homogeneous plane equation. No finite-field point bound or
bad-prime estimate is asserted here. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

/-- Restrict a ternary homogeneous equation to the chart x₀=1. -/
def planeAffineChart : MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 2) ℤ :=
  eval₂Hom C (Fin.cons 1 X)

lemma planeAffineChart_eval (f : MvPolynomial (Fin 3) ℤ) (z : Fin 2 → ℤ) :
    eval z (planeAffineChart f) = eval (Fin.cons 1 z) f := by
  change eval z (eval₂ C (Fin.cons 1 X) f) = _
  rw [← eval_assoc]
  have he : (eval z) ∘ Fin.cons (1 : MvPolynomial (Fin 2) ℤ) X = Fin.cons 1 z := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  rw [he]

lemma planeAffineChart_evaluation_matrix {M s : ℕ} (z : Fin s → Fin 2 → ℤ) :
    (Matrix.of fun i k => eval (z i)
      (planeAffineChart (monomial (homogeneousMonomials 2 M k) 1))) =
    evaluationMatrix (homogeneousMonomials 2 M) (fun i => Fin.cons 1 (z i)) := by
  ext i k
  rw [Matrix.of_apply, planeAffineChart_eval, eval_monomial]
  simp [evaluationMatrix]

/-- Exact finite determinant comparison for bounded affine points on a plane
curve. All local divisibility and the exact selected-row rank are derived.
The finite set of good primes is explicit, and the actual residue-point counts
are retained rather than replaced by an unproved estimate. -/
theorem plane_chart_no_auxiliary_determinant_comparison {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, eval (z i) (planeAffineChart f) = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (Fin.cons 1 (z i)) g = 0) → f ∣ g)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hred : ∀ p ∈ P, Irreducible (map (Int.castRingHom (ZMod p)) (planeAffineChart f)))
    (hchar : ∀ p ∈ P, (planeAffineChart f).totalDegree < p) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ 0 < s ∧
      s + (2 + (M - d)).choose (M - d) = (2 + M).choose M ∧
      2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (∑ p ∈ P, Real.log p /
        (Nat.card (PlaneResidue (planeAffineChart f) p) +
          (planeAffineChart f).totalDegree ^ 2 * ((planeAffineChart f).totalDegree - 1) : ℕ)) -
        s * (∑ p ∈ P, Real.log p) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  have hz' : ∀ i, eval (Fin.cons 1 (z i)) f = 0 := by
    intro i
    rw [← planeAffineChart_eval]
    exact hz i
  have hbox' : ∀ (i : Fin t) (j : Fin 3), |(((Fin.cons (1 : ℤ) (z i) : Fin 3 → ℤ) j) : ℝ)| ≤ B := by
    intro i j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa using hB
    · simpa using hbox i k
  obtain ⟨s, a, ha, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM
      (fun i => Fin.cons 1 (z i)) hz' hB hbox' hrel
  have hs := (plane_homogeneous_rank_bounds hd hdM hr).1
  refine ⟨s, a, ha, hs, hr, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let g := fun k => planeAffineChart (monomial (homogeneousMonomials 2 M k) 1)
  have he := planeAffineChart_evaluation_matrix (M := M) (z ∘ a)
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i k => eval ((z ∘ a) i) (g k)).map ((↑) : ℤ → ℚ)).row := by
    rw [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he]
    exact hi
  have hlower := singular_determinant_log_lower_exact hs (planeAffineChart f) g (z ∘ a)
    (fun i => hz (a i)) hi' P hP hred hchar
  change _ ≤ Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval ((z ∘ a) i) (g k))) at hlower
  rw [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he] at hlower
  exact hlower.trans hupper

/-- The plane determinant-method inequality with the fourth-power cutoff.
Its remaining arithmetic inputs are the actual finite-field point estimate and
a finite excluded-prime set; all matrix, rank, singular, and prime-tail steps
are proved in this development. -/
theorem plane_chart_no_auxiliary_degree_four_comparison {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    (hdchart : 0 < (planeAffineChart f).totalDegree)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (Fin.cons 1 (z i)) g = 0) → f ∣ g)
    (bad : Finset ℕ)
    (hred : ∀ p : ℕ, p.Prime → p ∉ bad →
      27 * ((planeAffineChart f).totalDegree : ℝ) ^ 4 < p →
      Irreducible (map (Int.castRingHom (ZMod p)) (planeAffineChart f)))
    (hcount : ∀ p : ℕ, p.Prime → p ∉ bad →
      27 * ((planeAffineChart f).totalDegree : ℝ) ^ 4 < p →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * ((planeAffineChart f).totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    ∃ s : ℕ, 0 < s ∧ s + (2 + (M - d)).choose (M - d) = (2 + M).choose M ∧
      2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log (planeAffineChart f).totalDegree -
        Real.log 27 - 2 * mertensError - (∑ p ∈ bad, Real.log p / p) -
        2 * primeBlockMass * (C + 1)) - s * ((Real.log 4 + 4) * s) ≤
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
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
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
  have hlower := singular_determinant_log_lower_degree_four hs (planeAffineChart f) hdchart
    g (z ∘ a) (fun i => hz (a i)) hi' (x := (s : ℝ))
    (by exact_mod_cast hs) hC bad
    (fun p hp hcut => hred p (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
      (Finset.mem_sdiff.mp hp).2 hcut)
    (fun p hp hcut => hcount p (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
      (Finset.mem_sdiff.mp hp).2 hcut)
  change _ ≤ Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval ((z ∘ a) i) (g k))) at hlower
  rw [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he] at hlower
  exact hlower.trans hupper

end
end AffineCurveCounting
