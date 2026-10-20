/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import AffineCurveCounting.FilteredIntersection
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset

/-!
# Dimension of bounded-degree polynomial spaces

Adding a slack exponent identifies degree-at-most monomials with multisets of
fixed cardinality on one extra variable. This proves the usual binomial dimension
formula needed in the filtered intersection estimate.
-/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- One slack coordinate turns a bounded sum of exponents into an exact sum. -/
def slackExponentEquiv (σ : Type*) [Fintype σ] (N : ℕ) :
    {p : σ → ℕ // ∑ j, p j ≤ N} ≃ {q : Option σ → ℕ // ∑ j, q j = N} where
  toFun p := ⟨(fun j => j.elim (N - ∑ i, p.val i) p.val), by
    simp only [Fintype.sum_option, Option.elim_none, Option.elim_some]
    exact Nat.sub_add_cancel p.property⟩
  invFun q := ⟨fun j => q.val (some j), by
    have h := q.property
    rw [Fintype.sum_option] at h
    change (∑ j, q.val (some j)) ≤ N
    omega⟩
  left_inv p := by rfl
  right_inv q := by
    apply Subtype.ext
    funext j
    cases j with
    | none =>
      have h := q.property
      rw [Fintype.sum_option] at h
      dsimp
      omega
    | some j => rfl

/-- Monomials of degree at most `N` are fixed-size multisets on one extra variable. -/
def boundedExponentEquivSym (σ : Type*) [Fintype σ] [DecidableEq σ] (N : ℕ) :
    {p : σ →₀ ℕ // p.sum (fun _ e => e) ≤ N} ≃ Sym (Option σ) N :=
  (Finsupp.equivFunOnFinite.subtypeEquiv (fun p => by simp [Finsupp.sum_fintype])).trans
    ((slackExponentEquiv σ N).trans (Sym.equivNatSumOfFintype (Option σ) N).symm)

/-- Exact dimension of polynomials of total degree at most `N`. -/
theorem finrank_restrictTotalDegree {K σ : Type*} [Field K] [Fintype σ] (N : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree σ K N) =
      (Fintype.card σ + N).choose N := by
  classical
  let e := boundedExponentEquivSym σ N
  let : Fintype ↥({p : σ →₀ ℕ | p.sum (fun _ e => e) ≤ N} : Set (σ →₀ ℕ)) :=
    Fintype.ofEquiv (Sym (Option σ) N) e.symm
  let : Fintype {p : σ →₀ ℕ // p.sum (fun _ e => e) ≤ N} :=
    Fintype.ofEquiv (Sym (Option σ) N) e.symm
  change Module.finrank K
    (MvPolynomial.restrictSupport K {p : σ →₀ ℕ | p.sum (fun _ e => e) ≤ N}) = _
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K _)]
  change Fintype.card {p : σ →₀ ℕ // p.sum (fun _ e => e) ≤ N} = _
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  simp only [Fintype.card_option]
  congr 1
  omega

end
end AffineCurveCounting
