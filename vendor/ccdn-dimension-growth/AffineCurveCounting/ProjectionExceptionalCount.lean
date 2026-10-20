module

public import AffineCurveCounting.BoundedBirationalProjection

/-! Polynomial reconstruction controls actual exceptional points and finite
point counts. The error is d times the reconstruction denominator's degree;
a uniform O(d^2) bound still requires a low-degree denominator. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The proper denominator of a linear projection vanishes at at most d*deg(Q)
distinct points of the source curve. -/
theorem reconstruction_exceptional_card_le {K σ τ ι : Type*} [Field K]
    [Fintype σ] [Fintype τ] [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime] (d : ℕ)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (a : σ → MvPolynomial τ K) (ha : ∀ j, (a j).totalDegree ≤ 1)
    (Q : MvPolynomial σ K) (hQ : aeval a Q ∉ I)
    (z : ι → τ → K) (hz : Function.Injective z)
    (hzi : ∀ i, ∀ f ∈ I, eval (z i) f = 0)
    (hzQ : ∀ i, eval (z i) (aeval a Q) = 0) :
    Fintype.card ι ≤ d * Q.totalDegree := by
  apply polynomial_section_card_le_degree I d hdegree (aeval a Q) hQ Q.totalDegree
    (by simpa only [one_mul] using aeval_totalDegree_le a ha Q) z hz hzi hzQ

/-- For every finite set of source points, projection loses at most
 d*deg(Q) points, where Q is any proper reconstruction denominator. -/
theorem projection_card_le_image_add {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    [DecidableEq (σ → K)]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime] (d : ℕ)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
      (Module.finrank K (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c)
    (a : σ → MvPolynomial τ K) (ha : ∀ j, (a j).totalDegree ≤ 1)
    (Q : MvPolynomial σ K) (P : τ → MvPolynomial σ K)
    (hQ : aeval a Q ∉ I) (hP : ∀ i, aeval a Q * X i - aeval a (P i) ∈ I)
    (S : Finset (τ → K)) (hS : ∀ z ∈ S, ∀ f ∈ I, eval z f = 0) :
    let π : (τ → K) → (σ → K) := fun z j => eval z (a j)
    S.card ≤ (S.image π).card + d * Q.totalDegree := by
  classical
  let π : (τ → K) → (σ → K) := fun z j => eval z (a j)
  let T := S.filter (fun z => eval z (aeval a Q) = 0)
  let G := S.filter (fun z => eval z (aeval a Q) ≠ 0)
  have hT : T.card ≤ d * Q.totalDegree := by
    have hh := reconstruction_exceptional_card_le I d hdegree a ha Q hQ
      (fun z : T => z.val) Subtype.val_injective
      (fun z => hS z.val (Finset.mem_filter.mp z.property).1)
      (fun z => (Finset.mem_filter.mp z.property).2)
    simpa only [Fintype.card_coe] using hh
  have hG : G.card ≤ (S.image π).card := by
    apply Finset.card_le_card_of_injOn π
    · intro z hz
      exact Finset.mem_image.mpr ⟨z, (Finset.mem_filter.mp hz).1, rfl⟩
    · intro z hz w hw he
      obtain ⟨hzS, hzQ⟩ := Finset.mem_filter.mp hz
      obtain ⟨hwS, _⟩ := Finset.mem_filter.mp hw
      exact projection_injective_off_reconstruction I a Q P hP z w
        (hS z hzS) (hS w hwS) hzQ he
  have hcard : T.card + G.card = S.card := Finset.card_filter_add_card_filter_not _
  change S.card ≤ (S.image π).card + _
  omega

end
end AffineCurveCounting
