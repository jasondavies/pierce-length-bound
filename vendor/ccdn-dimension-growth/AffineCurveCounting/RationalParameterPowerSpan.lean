module

public import AffineCurveCounting.ParameterPowerSpan

/-! Any finite family in a finite extension of K(t) fits in a bounded power
block after multiplication by one nonzero rational-function denominator. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

lemma ratFunc_polynomial_eval {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    (p : Polynomial K) :
    algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p) =
      Polynomial.aeval (algebraMap (RatFunc K) F RatFunc.X) p := by
  let φ := (IsScalarTower.toAlgHom K (RatFunc K) F).comp
    (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
  have he : φ = Polynomial.aeval (algebraMap (RatFunc K) F RatFunc.X) := by
    apply Polynomial.algHom_ext
    simp [φ, RatFunc.algebraMap_X]
  exact congrArg (fun f => f p) he

/-- A common parameter denominator makes every supplied vector a bounded
polynomial combination of a fixed function-field basis. -/
theorem finite_family_parameter_power_span {K F ι : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Module.Finite (RatFunc K) F] [Fintype ι]
    (w : ι → F) :
    ∃ q : F, q ≠ 0 ∧ ∃ D : ℕ, ∀ j,
      q * w j ∈ parameterPowerSpan K (algebraMap (RatFunc K) F RatFunc.X)
        (Module.finBasis (RatFunc K) F) D := by
  classical
  let b := Module.finBasis (RatFunc K) F
  let r := Module.finrank (RatFunc K) F
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun t : ι × Fin r => b.repr (w t.1) t.2)
  choose p hp using hq
  let D := Finset.univ.sup (fun t : ι × Fin r => (p t).natDegree)
  let qF := algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) q.val)
  have hqn : q.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp q.property
  have hqF : qF ≠ 0 := (map_ne_zero_iff (algebraMap (RatFunc K) F)
    (algebraMap (RatFunc K) F).injective).mpr (RatFunc.algebraMap_ne_zero hqn)
  refine ⟨qF, hqF, D, ?_⟩
  intro j
  rw [← b.sum_repr (w j), Finset.mul_sum]
  apply (parameterPowerSpan K (algebraMap (RatFunc K) F RatFunc.X) b D).sum_mem
  intro i _
  have he : qF * (b.repr (w j) i • b i) =
      Polynomial.aeval (algebraMap (RatFunc K) F RatFunc.X) (p (j,i)) * b i := by
    have hp' : algebraMap (Polynomial K) (RatFunc K) (p (j,i)) =
        algebraMap (Polynomial K) (RatFunc K) q.val * b.repr (w j) i :=
      (hp (j,i)).trans (Algebra.smul_def _ _)
    rw [Algebra.smul_def, ← mul_assoc]
    change (algebraMap (RatFunc K) F _ * algebraMap (RatFunc K) F _) * _ = _
    rw [← map_mul, ← hp', ratFunc_polynomial_eval]
  rw [he]
  exact polynomial_parameter_mul_mem _ b i (p (j,i)) D
    (Finset.le_sup (f := fun t : ι × Fin r => (p t).natDegree) (Finset.mem_univ (j,i)))

end
end AffineCurveCounting
