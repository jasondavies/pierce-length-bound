module

public import AffineCurveCounting.MonomialDimension
public import AffineCurveCounting.Interpolation

/-! Complete homogeneous monomial lists, their exact cardinalities, and the
corresponding polynomial-space dimensions. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Exponents of total degree exactly `M` are multisets of cardinality `M`. -/
def exactExponentEquivSym (σ : Type*) [Fintype σ] [DecidableEq σ] (M : ℕ) :
    {p : σ →₀ ℕ // p.sum (fun _ e => e) = M} ≃ Sym σ M :=
  (Finsupp.equivFunOnFinite.subtypeEquiv (fun p => by simp [Finsupp.sum_fintype])).trans
    (Sym.equivNatSumOfFintype σ M).symm

theorem card_exact_exponents (n M : ℕ) :
    Nat.card {p : Fin (n + 1) →₀ ℕ // p.sum (fun _ e => e) = M} = (n + M).choose M := by
  rw [Nat.card_congr (exactExponentEquivSym (Fin (n + 1)) M), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  congr 1
  omega

/-- A canonical finite indexing of all degree-`M` monomials in `n+1` variables. -/
def homogeneousExponentEquiv (n M : ℕ) :
    Fin ((n + M).choose M) ≃ {p : Fin (n + 1) →₀ ℕ // p.sum (fun _ e => e) = M} := by
  let e := exactExponentEquivSym (Fin (n + 1)) M
  let _ := Fintype.ofEquiv (Sym (Fin (n + 1)) M) e.symm
  have hc : Fintype.card {p : Fin (n + 1) →₀ ℕ // p.sum (fun _ e => e) = M} =
      (n + M).choose M := by rw [← Nat.card_eq_fintype_card, card_exact_exponents]
  exact (finCongr hc.symm).trans (Fintype.equivFin _).symm

def homogeneousMonomials (n M : ℕ) : Fin ((n + M).choose M) → (Fin (n + 1) →₀ ℕ) :=
  fun j => (homogeneousExponentEquiv n M j).val

lemma homogeneousMonomials_injective (n M : ℕ) : Function.Injective (homogeneousMonomials n M) :=
  Subtype.val_injective.comp (homogeneousExponentEquiv n M).injective

lemma homogeneousMonomials_degree (n M : ℕ) (j : Fin ((n + M).choose M)) :
    (homogeneousMonomials n M j).sum (fun _ e => e) = M :=
  (homogeneousExponentEquiv n M j).property

lemma homogeneousMonomials_surjective (n M : ℕ) (p : Fin (n + 1) →₀ ℕ)
    (hp : p.sum (fun _ e => e) = M) : ∃ j, homogeneousMonomials n M j = p := by
  obtain ⟨j, hj⟩ := (homogeneousExponentEquiv n M).surjective ⟨p, hp⟩
  exact ⟨j, congrArg Subtype.val hj⟩

theorem finrank_homogeneousSubmodule {K : Type*} [Field K] (n M : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (n + 1)) K M) = (n + M).choose M := by
  classical
  let e := exactExponentEquivSym (Fin (n + 1)) M
  let _ := Fintype.ofEquiv (Sym (Fin (n + 1)) M) e.symm
  let _ : Fintype ↥({p : Fin (n + 1) →₀ ℕ | p.sum (fun _ e => e) = M} : Set _) :=
    Fintype.ofEquiv (Sym (Fin (n + 1)) M) e.symm
  have he : homogeneousSubmodule (Fin (n + 1)) K M =
      restrictSupport K {p | p.sum (fun _ e => e) = M} := by
    rw [homogeneousSubmodule_eq_finsupp_supported]
    rfl
  rw [he, Module.finrank_eq_card_basis (basisRestrictSupport K _)]
  change Fintype.card {p : Fin (n + 1) →₀ ℕ // p.sum (fun _ e => e) = M} = _
  rw [← Nat.card_eq_fintype_card, card_exact_exponents]

theorem polynomialOfCoefficients_homogeneous (n M : ℕ)
    (v : Fin ((n + M).choose M) → ℤ) :
    (polynomialOfCoefficients (homogeneousMonomials n M) v).IsHomogeneous M := by
  apply IsHomogeneous.sum
  intro j _
  apply isHomogeneous_monomial
  exact homogeneousMonomials_degree n M j

end
end AffineCurveCounting
