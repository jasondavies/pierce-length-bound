module

public import AffineCurveCounting.RadialHomogeneousMap
public import Mathlib.RingTheory.Nullstellensatz

/-! Vanishing only at the origin on the infinity section supplies balanced
coordinate-power reductions. The Nullstellensatz is used on the actual kernel
of the map to the infinity quotient, over any algebraically closed extension. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def infinityCoordinateMap {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial σ K →ₐ[K] projectiveCoordinateAlgebra I ⧸ projectiveInfinityIdeal I :=
  (Ideal.Quotient.mkₐ K (projectiveInfinityIdeal I)).comp (quotientRadialMap I)

def leadingInfinityIdeal {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ K) := RingHom.ker (infinityCoordinateMap I)

lemma leadingInfinityIdeal_component_mem {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) (hf : f ∈ leadingInfinityIdeal I)
    (n : ℕ) : (Ideal.Quotient.mk I) (homogeneousComponent (n + 1) f) ∈ filteredCoordinateSpace I n := by
  have hm : quotientRadialMap I f ∈ projectiveInfinityIdeal I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hf
  rw [projectiveInfinityIdeal,
    Ideal.mem_span_singleton (α := projectiveCoordinateAlgebra I)] at hm
  obtain ⟨g, hg⟩ := hm
  have he := congrArg (fun h : projectiveCoordinateAlgebra I =>
    (h : Polynomial (MvPolynomial σ K ⧸ I)).coeff (n + 1)) hg
  change ((quotientRadialMap I f : projectiveCoordinateAlgebra I) :
      Polynomial (MvPolynomial σ K ⧸ I)).coeff (n + 1) =
      (Polynomial.X * (g : Polynomial (MvPolynomial σ K ⧸ I))).coeff (n + 1) at he
  rw [quotientRadialMap_coeff, Polynomial.coeff_X_mul] at he
  rw [he]
  exact g.property n

lemma homogeneousComponent_mul_homogeneous_left {K σ : Type*} [CommRing K]
    {f : MvPolynomial σ K} {i : ℕ} (hf : f.IsHomogeneous i)
    (g : MvPolynomial σ K) (j : ℕ) :
    homogeneousComponent (i + j) (f * g) = f * homogeneousComponent j g := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  have ht := DirectSum.coe_decompose_mul_add_of_left_mem
    (homogeneousSubmodule σ K) (j := j) hf (b := g)
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] using ht

/-- A coordinate-power certificate at infinity gives a balanced reduction in
the original affine quotient. -/
theorem power_reduction_of_infinity_certificate {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (l : MvPolynomial σ K) (hl : l.IsHomogeneous 1)
    (j : σ) (N : ℕ) (hN : 0 < N)
    (hpow : X j ^ N ∈ leadingInfinityIdeal I ⊔ Ideal.span {l}) :
    ∃ r s : MvPolynomial σ K, r.totalDegree ≤ N - 1 ∧ s.totalDegree ≤ N - 1 ∧
      (Ideal.Quotient.mk I) (X j ^ N) = (Ideal.Quotient.mk I) r +
        (Ideal.Quotient.mk I) l * (Ideal.Quotient.mk I) s := by
  cases N with
  | zero => omega
  | succ n =>
    obtain ⟨g, hg, t, ht, he⟩ := Submodule.mem_sup.mp hpow
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp ht
    have hrel : X j ^ (n + 1) - l * s ∈ leadingInfinityIdeal I := by
      rw [← he, hs]
      simpa only [add_sub_cancel_right] using hg
    have hm := leadingInfinityIdeal_component_mem I _ hrel n
    rw [map_sub, homogeneousComponent_eq_self (isHomogeneous_X_pow j (n + 1)),
      show n + 1 = 1 + n by omega, homogeneousComponent_mul_homogeneous_left hl] at hm
    obtain ⟨r, hr, heq⟩ := Submodule.mem_map.mp hm
    refine ⟨r, homogeneousComponent n s, (mem_restrictTotalDegree _ _ _).mp hr,
      (homogeneousComponent_isHomogeneous n s).totalDegree_le, ?_⟩
    change (Ideal.Quotient.mk I) r =
      (Ideal.Quotient.mk I) (X j ^ (1 + n) - l * homogeneousComponent n s) at heq
    rw [map_sub, map_mul] at heq
    rw [show n + 1 = 1 + n by omega]
    exact eq_add_of_sub_eq (heq.symm)

/-- Avoiding every nonzero infinity direction supplies all coordinate-power
reductions with a single positive exponent. -/
theorem exists_power_reductions_of_infinity_avoidance {K L σ : Type*}
    [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (l : MvPolynomial σ K) (hl : l.IsHomogeneous 1)
    (hzero : ∀ z ∈ MvPolynomial.zeroLocus L (leadingInfinityIdeal I ⊔ Ideal.span {l}), z = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ j : σ, ∃ r s : MvPolynomial σ K,
      r.totalDegree ≤ N - 1 ∧ s.totalDegree ≤ N - 1 ∧
      (Ideal.Quotient.mk I) (X j ^ N) = (Ideal.Quotient.mk I) r +
        (Ideal.Quotient.mk I) l * (Ideal.Quotient.mk I) s := by
  classical
  let J := leadingInfinityIdeal I ⊔ Ideal.span {l}
  have hp (j : σ) : ∃ m : ℕ, X j ^ m ∈ J := by
    have hm : X j ∈ vanishingIdeal K (MvPolynomial.zeroLocus L J) := by
      intro z hz
      rw [hzero z hz]
      simp
    rw [vanishingIdeal_zeroLocus_eq_radical] at hm
    exact hm
  choose m hm using hp
  let N := Finset.univ.sup m + 1
  have hN : 0 < N := by dsimp [N]; omega
  refine ⟨N, hN, ?_⟩
  intro j
  apply power_reduction_of_infinity_certificate I l hl j N hN
  have hj : m j ≤ N := (Finset.le_sup (f := m) (Finset.mem_univ j)).trans (Nat.le_succ _)
  have hh := J.mul_mem_left (X j ^ (N - m j)) (hm j)
  simpa only [← pow_add, Nat.sub_add_cancel hj] using hh

end
end AffineCurveCounting
