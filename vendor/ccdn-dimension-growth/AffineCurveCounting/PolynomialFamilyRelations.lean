module

public import AffineCurveCounting.PolynomialCoefficientLinearMap

/-! Relations among a finite family of algebra-valued polynomials can be
encoded by a finite scalar polynomial matrix. Persistent dependence therefore
gives a polynomial relation nonzero at the origin, even when the target
algebra is infinite-dimensional over the scalar field. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

lemma exists_finite_detecting_functionals {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (S : Submodule K V) [Module.Finite K S] :
    ∃ φ : Fin (Module.finrank K S) → V →ₗ[K] K,
      ∀ x ∈ S, (∀ i, φ i x = 0) → x = 0 := by
  obtain ⟨T, hT⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  let b := Module.finBasis K S
  refine ⟨fun i => (b.coord i).comp T, ?_⟩
  intro x hx hzero
  have hTx : T x = (⟨x, hx⟩ : S) := congrArg (fun f : S →ₗ[K] S => f ⟨x, hx⟩) hT
  have ht : T x = 0 := by
    apply b.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply, LinearMap.comp_apply, Module.Basis.coord_apply] using hzero i
  have hz : (⟨x, hx⟩ : S) = 0 := hTx.symm.trans ht
  exact congrArg Subtype.val hz

/-- If the evaluations of a polynomial family are dependent over K at every
integer parameter, the family has a polynomial relation whose coefficient
vector does not vanish at zero. -/
theorem polynomial_family_relation_nonzero_at_zero {K A κ : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A] [Fintype κ] [DecidableEq κ]
    (g : κ → Polynomial A)
    (hdep : ∀ k : ℕ, ∃ c : κ → K, c ≠ 0 ∧ ∑ j, c j • (g j).eval (k : A) = 0) :
    ∃ v : κ → Polynomial K,
      (∑ j, (v j).map (algebraMap K A) * g j) = 0 ∧ ∃ j, (v j).eval 0 ≠ 0 := by
  classical
  let s := Finset.univ.biUnion (fun j => (g j).support.image (fun n => (g j).coeff n))
  let S := Submodule.span K (s : Set A)
  let : Module.Finite K S := Module.Finite.span_of_finite K s.finite_toSet
  have hmem (j : κ) (n : ℕ) : (g j).coeff n ∈ S := by
    by_cases hn : n ∈ (g j).support
    · apply Submodule.subset_span
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact S.zero_mem
  obtain ⟨φ, hφ⟩ := exists_finite_detecting_functionals S
  let M : Matrix (Fin (Module.finrank K S)) κ (Polynomial K) :=
    fun i j => coefficientLinearUnivariate (φ i) (g j)
  have hM (k : ℕ) : ¬ Function.Injective (M.map (Polynomial.evalRingHom (k : K))).mulVecLin := by
    intro hi
    obtain ⟨c, hc, hrel⟩ := hdep k
    apply hc
    apply hi
    rw [map_zero]
    funext i
    change ∑ j, (coefficientLinearUnivariate (φ i) (g j)).eval (k : K) * c j = 0
    simp only [coefficientLinearUnivariate_eval, map_natCast]
    calc
      _ = φ i (∑ j, c j • (g j).eval (k : A)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_smul, smul_eq_mul, mul_comm]
      _ = 0 := by rw [hrel, map_zero]
  obtain ⟨v, hv, hv0⟩ := polynomial_matrix_kernel_nonzero_at_zero M hM
  refine ⟨v, ?_, hv0⟩
  let P := ∑ j, (v j).map (algebraMap K A) * g j
  have hcoeff (n : ℕ) : P.coeff n ∈ S := by
    simp only [P, Polynomial.finsetSum_coeff, coeff_mul, coeff_map]
    apply S.sum_mem
    intro j _
    apply S.sum_mem
    intro t _
    simpa only [Algebra.smul_def] using S.smul_mem ((v j).coeff t.1) (hmem j t.2)
  have hfun (i : Fin (Module.finrank K S)) : coefficientLinearUnivariate (φ i) P = 0 := by
    change coefficientLinearUnivariateMap (φ i) (∑ j, (v j).map (algebraMap K A) * g j) = 0
    rw [map_sum]
    change ∑ j, coefficientLinearUnivariate (φ i) ((v j).map (algebraMap K A) * g j) = 0
    simp only [coefficientLinearUnivariate_scalar_mul]
    have hh := congrFun hv i
    change ∑ j, coefficientLinearUnivariate (φ i) (g j) * v j = 0 at hh
    simpa only [mul_comm] using hh
  change P = 0
  ext n
  apply hφ _ (hcoeff n)
  intro i
  have hh := congrArg (fun p : Polynomial K => p.coeff n) (hfun i)
  simpa only [coefficientLinearUnivariate_coeff, coeff_zero] using hh

end
end AffineCurveCounting
