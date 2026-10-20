module

public import AffineCurveCounting.HomogeneousScalarExtension
public import AffineCurveCounting.HomogeneousChartInterpolation
public import Mathlib.Data.Set.Card

/-! The certified affine Hilbert degree bounds the number of geometric
infinity points in each normalized projective chart. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma homogeneous_chart_evaluation_span_eq_top {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype ι] (z : ι → σ → L) (hz : Function.Injective z)
    (j : σ) (hj : ∀ i, z i j = 1) (m : ℕ) (hm : Fintype.card ι ≤ m) :
    Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m)) = ⊤ := by
  classical
  let W := Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m))
  let b := Pi.basisFun L ι
  have hb (i : ι) : b i ∈ W := by
    obtain ⟨p, hp, he⟩ := exists_homogeneous_chart_delta z hz j hj m hm i
    have hv := homogeneous_extension_evaluation_mem (K := K) z m p hp
    have heq : (fun k => MvPolynomial.eval (z k) p) = b i := by
      funext k
      simp [he, b, Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rwa [heq] at hv
  apply top_unique
  intro v _
  rw [← b.sum_repr v]
  exact W.sum_mem (fun i _ => W.smul_mem _ (hb i))

/-- Every finite family of distinct normalized infinity points has size at
most the original affine Hilbert degree, over any extension field. -/
theorem infinity_chart_card_le_degree {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (z : ι → σ → L) (hz : ∀ i, z i ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I))
    (hinj : Function.Injective z) (j : σ) (hj : ∀ i, z i j = 1) :
    Fintype.card ι ≤ d := by
  obtain ⟨N, c, hN⟩ := hdegree
  let m := N + Fintype.card ι
  have hb := infinity_evaluation_span_finrank_le_degree I z hz hN m (by dsimp [m]; omega)
  rw [homogeneous_chart_evaluation_span_eq_top z hinj j hj (m + 1) (by dsimp [m]; omega)] at hb
  simpa only [finrank_top, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] using hb

/-- Each normalized infinity chart is an actual finite set with at most d
points, not merely a bound for already finite subsets. -/
theorem exists_finite_infinity_chart {K L σ : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype σ] (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (j : σ) :
    ∃ S : Finset (σ → L), S.card ≤ d ∧ ∀ z,
      z ∈ S ↔ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I) ∧ z j = 1 := by
  classical
  let T := {z : σ → L | z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I) ∧ z j = 1}
  have hT : T.Finite := by
    by_contra hn
    obtain ⟨S, hS, hc⟩ := Set.Infinite.exists_subset_card_eq hn (d + 1)
    have hb := infinity_chart_card_le_degree I d hdegree (fun z : S => z.val)
      (fun z => (hS z.property).1) Subtype.val_injective j (fun z => (hS z.property).2)
    rw [Fintype.card_coe, hc] at hb
    omega
  refine ⟨hT.toFinset, ?_, fun z => hT.mem_toFinset⟩
  have hb := infinity_chart_card_le_degree I d hdegree (fun z : hT.toFinset => z.val)
    (fun z => (hT.mem_toFinset.mp z.property).1) Subtype.val_injective j
    (fun z => (hT.mem_toFinset.mp z.property).2)
  simpa only [Fintype.card_coe] using hb

end
end AffineCurveCounting
