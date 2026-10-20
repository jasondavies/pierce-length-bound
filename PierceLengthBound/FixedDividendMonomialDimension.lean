/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendFilteredIntersection
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset

/-!
# Dimension of bounded-degree polynomial spaces

Adding a slack exponent identifies degree-at-most monomials with multisets of
fixed cardinality on one extra variable. This proves the usual binomial dimension
formula needed in the filtered intersection estimate.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
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

/-- In three variables the dimension is the cubic binomial coefficient. -/
theorem finrank_restrictTotalDegree_three {K : Type*} [Field K] (N : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin 3) K N) = (N + 3).choose 3 := by
  rw [finrank_restrictTotalDegree]
  simp only [Fintype.card_fin]
  rw [Nat.add_comm 3 N, Nat.choose_symm_add]


lemma six_mul_choose_add_three (n : ℕ) :
    6 * (n + 3).choose 3 = (n + 3) * (n + 2) * (n + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3
  norm_num [Nat.descFactorial_succ] at h
  rw [← h]
  ring

/-- The cubic binomial second difference has linear growth with slope `d*e`. -/
lemma cubic_binomial_difference_bound {H N d e : ℕ} (hN : d + e ≤ N)
    (h : H + (N - d + 3).choose 3 + (N - e + 3).choose 3 ≤
      (N + 3).choose 3 + (N - (d + e) + 3).choose 3) :
    H ≤ d * e * (N + 2) := by
  have hd : d ≤ N := by omega
  have he : e ≤ N := by omega
  have h0 := six_mul_choose_add_three N
  have h1 := six_mul_choose_add_three (N - d)
  have h2 := six_mul_choose_add_three (N - e)
  have h3 := six_mul_choose_add_three (N - (d + e))
  have hZ : (H : ℤ) + ((N - d + 3).choose 3 : ℤ) + ((N - e + 3).choose 3 : ℤ) ≤
      ((N + 3).choose 3 : ℤ) + ((N - (d + e) + 3).choose 3 : ℤ) := by exact_mod_cast h
  have h0Z : (6 : ℤ) * (N + 3).choose 3 = (N + 3 : ℤ) * (N + 2) * (N + 1) := by
    exact_mod_cast h0
  have h1Z : (6 : ℤ) * (N - d + 3).choose 3 =
      ((N : ℤ) - d + 3) * ((N : ℤ) - d + 2) * ((N : ℤ) - d + 1) := by
    exact_mod_cast (show (6 : ℤ) * ((N - d + 3).choose 3 : ℤ) =
      ((N - d : ℕ) + 3 : ℤ) * ((N - d : ℕ) + 2 : ℤ) * ((N - d : ℕ) + 1 : ℤ) from
      by exact_mod_cast h1)
  have h2Z : (6 : ℤ) * (N - e + 3).choose 3 =
      ((N : ℤ) - e + 3) * ((N : ℤ) - e + 2) * ((N : ℤ) - e + 1) := by
    exact_mod_cast (show (6 : ℤ) * ((N - e + 3).choose 3 : ℤ) =
      ((N - e : ℕ) + 3 : ℤ) * ((N - e : ℕ) + 2 : ℤ) * ((N - e : ℕ) + 1 : ℤ) from
      by exact_mod_cast h2)
  have h3Z : (6 : ℤ) * (N - (d + e) + 3).choose 3 =
      ((N : ℤ) - (d + e) + 3) * ((N : ℤ) - (d + e) + 2) * ((N : ℤ) - (d + e) + 1) := by
    exact_mod_cast (show (6 : ℤ) * ((N - (d + e) + 3).choose 3 : ℤ) =
      ((N - (d + e) : ℕ) + 3 : ℤ) * ((N - (d + e) : ℕ) + 2 : ℤ) *
        ((N - (d + e) : ℕ) + 1 : ℤ) from by exact_mod_cast h3)
  have hpos : (0 : ℤ) ≤ (d : ℤ) * e * (d + e) := by positivity
  have hresult : (H : ℤ) ≤ (d : ℤ) * e * (N + 2) := by nlinarith
  exact_mod_cast hresult

/-- Linear growth of the filtered coordinate space, with the Bézout product as
slope. Eventual Hilbert polynomials and component-degree additivity are separate. -/
theorem filteredCoordinateSpace_finrank_linear {K : Type*} [Field K]
    {f g : MvPolynomial (Fin 3) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin 3) K)) (hIf : f ∈ I) (hIg : g ∈ I)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace I N) ≤ f.totalDegree * g.totalDegree * (N + 2) := by
  have h := filteredCoordinateSpace_finrank_bound hf hfg I hIf hIg hN
  simp only [finrank_restrictTotalDegree_three] at h
  exact cubic_binomial_difference_bound hN h


/-- The actual intersection and each of its prime components have filtered
coordinate spaces bounded by `24*(N+2)`. -/
theorem curve_filteredCoordinateSpace_le {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℂ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℂ))
    (hIf : curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' ∈ I)
    (hIg : curveEquation (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a ∈ I)
    {N : ℕ} (hN : 14 ≤ N) :
    Module.finrank ℂ (filteredCoordinateSpace I N) ≤ 24 * (N + 2) := by
  have hf : Prime (curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v') := by
    apply Irreducible.prime
    apply lineQuadratic_irreducible
    all_goals exact_mod_cast (by linarith : _ ≠ (0 : ℝ))
  have hfd := curveQuadratic_degree_le_two (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v'
  have hgd := curveEquation_degree_le (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a
  have hfg : ¬ curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' ∣
      curveEquation (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a :=
    curveQuadratic_not_dvd_fixed_dividend hρ hu hv ρ' u' v' A a ha
  have h := filteredCoordinateSpace_finrank_linear (N := N) hf hfg I hIf hIg (by omega)
  exact h.trans (Nat.mul_le_mul_right (N + 2) (Nat.mul_le_mul hfd hgd))

end
end PierceLengthBound.FixedDividend
