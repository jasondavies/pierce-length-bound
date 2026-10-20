module

public import AffineCurveCounting.HomogeneousTranslation

/-! The affine translations underlying the homogeneous coordinate changes
preserve degree and irreducibility, over every coefficient field. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def affineTranslationHom (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R := aeval (fun j => X j + C (a j))

lemma affineTranslationHom_comp {R : Type*} [CommRing R] {n : ℕ} (a b : Fin n → R) :
    (affineTranslationHom R a).comp (affineTranslationHom R b) = affineTranslationHom R (a + b) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [affineTranslationHom, add_assoc]

@[simp] lemma affineTranslationHom_zero (R : Type*) [CommRing R] (n : ℕ) :
    affineTranslationHom R (0 : Fin n → R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp [affineTranslationHom]

def affineTranslation (R : Type*) [CommRing R] {n : ℕ} (a : Fin n → R) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom (affineTranslationHom R a) (affineTranslationHom R (-a))
    (by rw [affineTranslationHom_comp, add_neg_cancel, affineTranslationHom_zero])
    (by rw [affineTranslationHom_comp, neg_add_cancel, affineTranslationHom_zero])

lemma affineTranslation_irreducible_iff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    Irreducible (affineTranslation R a f) ↔ Irreducible f :=
  MulEquiv.irreducible_iff (f := affineTranslation R a)

lemma affineTranslation_totalDegree_le {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).totalDegree ≤ f.totalDegree := by
  classical
  have hm (m : Fin n →₀ ℕ) (c : R) :
      (affineTranslation R a (monomial m c)).totalDegree ≤ m.sum (fun _ e => e) := by
    change (aeval (fun j => X j + C (a j)) (monomial m c)).totalDegree ≤ _
    rw [aeval_monomial]
    have hp : (m.prod (fun j e => (X j + C (a j)) ^ e)).totalDegree ≤ m.sum (fun _ e => e) := by
      apply (totalDegree_finsetProd _ _).trans
      apply Finset.sum_le_sum
      intro j _
      have hh : (X j + C (a j) : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
        exact (totalDegree_add _ _).trans (by simp)
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m j) hh)
    have hh := totalDegree_mul (C c) (m.prod (fun j e => (X j + C (a j)) ^ e))
    simp only [totalDegree_C, zero_add] at hh
    exact hh.trans hp
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm'
  exact (hm m _).trans (le_totalDegree hm')

lemma affineTranslation_totalDegree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).totalDegree = f.totalDegree := by
  apply le_antisymm (affineTranslation_totalDegree_le a f)
  have hh := affineTranslation_totalDegree_le (-a) (affineTranslation R a f)
  have he : affineTranslation R (-a) (affineTranslation R a f) = f :=
    (affineTranslation R a).symm_apply_apply f
  rwa [he] at hh

lemma affineTranslation_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    MvPolynomial.map φ (affineTranslation R a f) = affineTranslation S (φ ∘ a) (MvPolynomial.map φ f) := by
  have he : (MvPolynomial.map φ).comp (affineTranslation R a).toRingHom =
      (affineTranslation S (φ ∘ a)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineTranslation, affineTranslationHom]
    · intro j
      simp [affineTranslation, affineTranslationHom]
  exact RingHom.congr_fun he f

lemma affineChart_homogeneousTranslation {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    affineChart n (homogeneousTranslation R a f) = affineTranslation R a (affineChart n f) := by
  have he : (affineChart n).comp (homogeneousTranslation R a).toRingHom =
      (affineTranslation R a).toRingHom.comp (affineChart n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineChart, homogeneousTranslation, homogeneousTranslationHom, affineTranslation, affineTranslationHom]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [affineChart, homogeneousTranslation, homogeneousTranslationHom, affineTranslation, affineTranslationHom]
  exact RingHom.congr_fun he f

lemma homogeneousTranslation_chart_degree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    (affineChart n (homogeneousTranslation R a f)).totalDegree = (affineChart n f).totalDegree := by
  rw [affineChart_homogeneousTranslation, affineTranslation_totalDegree]

lemma homogeneousTranslation_chart_irreducible {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) :
    Irreducible (MvPolynomial.map φ (affineChart n (homogeneousTranslation R a f))) ↔
      Irreducible (MvPolynomial.map φ (affineChart n f)) := by
  rw [affineChart_homogeneousTranslation, affineTranslation_map, affineTranslation_irreducible_iff]

end
end AffineCurveCounting
