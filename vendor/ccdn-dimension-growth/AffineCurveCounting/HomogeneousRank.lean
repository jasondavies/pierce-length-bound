module

public import AffineCurveCounting.HomogeneousHilbert
public import AffineCurveCounting.HomogeneousEvaluation

/-! The homogeneous Hilbert count bounds actual evaluation-matrix ranks.
The deficit includes every degree-allowed multiple of the defining equation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

def homogeneousCoefficientMap (K : Type*) [Field K] (n M : ℕ) :
    MvPolynomial (Fin (n + 1)) K →ₗ[K] (Fin ((n + M).choose M) → K) :=
  LinearMap.pi fun j => lcoeff K (homogeneousMonomials n M j)

def homogeneousEvaluationMatrix (K : Type*) [Field K] (n M : ℕ) {t : ℕ}
    (points : Fin t → (Fin (n + 1) → K)) : Matrix (Fin t) (Fin ((n + M).choose M)) K :=
  fun i j => (homogeneousMonomials n M j).prod fun k e => points i k ^ e

lemma homogeneous_evaluation_mulVec {K : Type*} [Field K] {n M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M)
    (points : Fin t → (Fin (n + 1) → K)) (i : Fin t) :
    (homogeneousEvaluationMatrix K n M points *ᵥ homogeneousCoefficientMap K n M f) i =
      eval (points i) f := by
  symm
  calc
    eval (points i) f = eval (points i)
        (∑ j, monomial (homogeneousMonomials n M j) (f.coeff (homogeneousMonomials n M j))) :=
        congrArg (eval (points i)) (homogeneous_eq_sum_coeff f hf)
    _ = _ := by
      simp [homogeneousEvaluationMatrix, homogeneousCoefficientMap, mulVec, dotProduct, eval_monomial, mul_comm]

/-- Every finite set of zeros obeys the projective Hilbert rank bound. -/
theorem homogeneous_evaluation_rank_bound {K : Type*} [Field K] {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → K)) (hzero : ∀ i, eval (points i) f = 0) :
    (homogeneousEvaluationMatrix K n M points).rank + (n + (M - d)).choose (M - d) ≤
      (n + M).choose M := by
  let A := homogeneousEvaluationMatrix K n M points
  let φ := homogeneousCoefficientMap K n M
  let U := homogeneousMultiples f d M
  let _ : Module.Finite K (homogeneousSubmodule (Fin (n + 1)) K (M - d)) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  let _ : Module.Finite K U := Module.Finite.of_fg
    ((homogeneousSubmodule_fg _ _ _).map (LinearMap.mulLeft K f))
  have hhom : ∀ u ∈ U, u.IsHomogeneous M := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    change (f * v).IsHomogeneous M
    simpa only [Nat.add_sub_of_le hdM] using hf.mul hv
  have hinj : Function.Injective (φ.domRestrict U) := by
    intro u v huv
    apply Subtype.ext
    have he : ∀ j, u.val.coeff (homogeneousMonomials n M j) =
        v.val.coeff (homogeneousMonomials n M j) := fun j => congrFun huv j
    rw [homogeneous_eq_sum_coeff u.val (hhom _ u.property),
      homogeneous_eq_sum_coeff v.val (hhom _ v.property)]
    simp only [he]
  have hdim := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_domRestrict] at hdim
  have hker : U.map φ ≤ A.mulVecLin.ker := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    change A *ᵥ φ u = 0
    ext i
    rw [homogeneous_evaluation_mulVec u (hhom _ hu)]
    obtain ⟨w, _, rfl⟩ := Submodule.mem_map.mp hu
    simp only [LinearMap.mulLeft_apply, eval_mul, hzero i, zero_mul, Pi.zero_apply]
  have hbound := finrank_map_add_kernel_subspace_le A.mulVecLin ⊤ (U.map φ) le_top hker
  rw [Submodule.map_top, hdim] at hbound
  change A.rank + Module.finrank K U ≤ Module.finrank K ↥(⊤ : Submodule K _) at hbound
  simpa only [U, homogeneousMultiples_finrank f hf0, finrank_homogeneousSubmodule,
    finrank_top, Module.finrank_pi, Module.finrank_self, mul_one, Fintype.card_fin] using hbound

/-- For independent evaluation rows the row count satisfies the same sharp deficit. -/
theorem homogeneous_independent_rows_hilbert_bound {K : Type*} [Field K] {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → K)) (hzero : ∀ i, eval (points i) f = 0)
    (hli : LinearIndependent K (homogeneousEvaluationMatrix K n M points).row) :
    t + (n + (M - d)).choose (M - d) ≤ (n + M).choose M := by
  have h := homogeneous_evaluation_rank_bound f hf hf0 hdM points hzero
  simpa only [hli.rank_matrix, Fintype.card_fin] using h

lemma homogeneousEvaluationMatrix_intCast {n M t : ℕ}
    (points : Fin t → (Fin (n + 1) → ℤ)) :
    homogeneousEvaluationMatrix ℚ n M (fun i j => (points i j : ℚ)) =
      (evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ) := by
  ext i j
  simp [homogeneousEvaluationMatrix, evaluationMatrix]

/-- The exact Hilbert deficit for independent integer evaluation rows. -/
theorem integer_homogeneous_rows_hilbert_bound {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0)
    (hli : LinearIndependent ℚ
      ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)).row) :
    t + (n + (M - d)).choose (M - d) ≤ (n + M).choose M := by
  have hfQ : map (Int.castRingHom ℚ) f ≠ 0 := by
    intro h
    apply hf0
    exact (map_injective (Int.castRingHom ℚ) Int.cast_injective) (h.trans (map_zero _).symm)
  have hzQ : ∀ i, eval (fun j => (points i j : ℚ)) (map (Int.castRingHom ℚ) f) = 0 := by
    intro i
    rw [eval_map]
    simpa only [Function.comp_def, Int.coe_castRingHom, hzero i, map_zero] using
      (eval₂_comp (Int.castRingHom ℚ) (points i) f).symm
  apply homogeneous_independent_rows_hilbert_bound _ (hf.map (Int.castRingHom ℚ)) hfQ hdM
    (fun i j => (points i j : ℚ)) hzQ
  simpa only [homogeneousEvaluationMatrix_intCast] using hli

end
end AffineCurveCounting
