module

public import AffineCurveCounting.InfinityEvaluationSpan

/-! Finite interpolation in a projective affine chart can be performed by
homogeneous polynomials of any sufficiently large common degree. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma exists_homogeneous_chart_delta {L σ ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]
    (z : ι → σ → L) (hz : Function.Injective z) (j : σ) (hj : ∀ i, z i j = 1)
    (m : ℕ) (hm : Fintype.card ι ≤ m) (i : ι) :
    ∃ p : MvPolynomial σ L, p.IsHomogeneous m ∧
      ∀ k, MvPolynomial.eval (z k) p = if i = k then 1 else 0 := by
  classical
  have hdiff (k : ι) (hik : i ≠ k) : ∃ q : σ, z i q ≠ z k q := by
    by_contra! he
    exact hik (hz (funext he))
  let q (k : ι) (hik : i ≠ k) := (hdiff k hik).choose
  have hq (k : ι) (hik : i ≠ k) : z i (q k hik) - z k (q k hik) ≠ 0 :=
    sub_ne_zero.mpr (hdiff k hik).choose_spec
  let l (k : ι) : MvPolynomial σ L := if hik : i = k then X j else
    C ((z i (q k hik) - z k (q k hik))⁻¹) *
      (X (q k hik) - C (z k (q k hik)) * X j)
  have hl (k : ι) : (l k).IsHomogeneous 1 := by
    dsimp [l]
    split_ifs
    · exact isHomogeneous_X L j
    · exact ((isHomogeneous_X L _).sub (isHomogeneous_C_mul_X _ _)).C_mul _
  have hli (k : ι) : MvPolynomial.eval (z i) (l k) = 1 := by
    dsimp [l]
    split_ifs with hik
    · simp [hj]
    · simp [hj, hq k hik]
  have hlk (k : ι) (hik : i ≠ k) : MvPolynomial.eval (z k) (l k) = 0 := by
    simp [l, hik, hj]
  let p := (∏ k, l k) * X j ^ (m - Fintype.card ι)
  refine ⟨p, ?_, ?_⟩
  · have hh : (∏ k, l k).IsHomogeneous (Fintype.card ι) := by
      simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
        IsHomogeneous.prod Finset.univ l (fun _ => 1) (fun k _ => hl k)
    have ht := hh.mul (isHomogeneous_X_pow j (m - Fintype.card ι))
    simpa only [Nat.add_sub_of_le hm] using ht
  · intro k
    by_cases hik : i = k
    · subst k
      simp [p, hli, hj]
    · have hh : ∏ t, MvPolynomial.eval (z k) (l t) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) (hlk k hik)
      simp [p, hik, hh]

end
end AffineCurveCounting
