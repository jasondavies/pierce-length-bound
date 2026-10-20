module

public import AffineCurveCounting.SingularPlaneChart

/-! Positive singular multiplicity is derived from an actual nonzero equation
vanishing at the origin; it is bounded by the equation's total degree. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The first nonzero homogeneous component realizes the order at the origin.
No multiplicity or ideal-power membership is supplied as a hypothesis. -/
theorem exists_origin_multiplicity {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hz : eval (0 : σ → K) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      f ∈ idealOfVars σ K ^ μ ∧ homogeneousComponent μ f ≠ 0 := by
  classical
  have hex : ∃ n, homogeneousComponent n f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    rw [← sum_homogeneousComponent f]
    simp only [h, Finset.sum_const_zero]
  let μ := Nat.find hex
  have hμ : homogeneousComponent μ f ≠ 0 := Nat.find_spec hex
  have hpow : f ∈ idealOfVars σ K ^ μ := by
    rw [mem_pow_idealOfVars_iff']
    intro e he
    have hzero : homogeneousComponent e.degree f = 0 :=
      not_not.mp (Nat.find_min hex he)
    have hc := congrArg (fun u : MvPolynomial σ K => u.coeff e) hzero
    simpa [coeff_homogeneousComponent] using hc
  have hpos : 0 < μ := by
    by_contra h
    have he : μ = 0 := by omega
    have hconst : f.coeff 0 = 0 := by simpa only [eval_zero, constantCoeff_eq] using hz
    apply hμ
    rw [he, homogeneousComponent_zero, hconst, map_zero]
  have hdeg : μ ≤ f.totalDegree := by
    by_contra h
    exact hμ (homogeneousComponent_eq_zero μ f (by omega))
  exact ⟨μ, hpos, hdeg, hpow, hμ⟩

/-- Substituting affine linear polynomials does not increase total degree. -/
theorem linear_eval₂_totalDegree_le {R S σ τ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : σ → MvPolynomial τ S) (hg : ∀ j, (g j).totalDegree ≤ 1)
    (f : MvPolynomial σ R) :
    (eval₂Hom (C.comp φ) g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial, RingHom.comp_apply]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  change (∏ j ∈ e.support, g j ^ e j).totalDegree ≤ f.totalDegree
  calc _ ≤ ∑ j ∈ e.support, (g j ^ e j).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ j ∈ e.support, e j := by
      apply Finset.sum_le_sum
      intro j _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e j) (hg j))
    _ ≤ f.totalDegree := le_totalDegree he

def originShift {R σ : Type*} [CommRing R] (a : σ → R) :
    MvPolynomial σ R →+* MvPolynomial σ R := eval₂Hom C (fun j => X j + C (a j))

lemma originShift_neg {R σ : Type*} [CommRing R] (a : σ → R) (f : MvPolynomial σ R) :
    originShift (-a) (originShift a f) = f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [originShift]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    simp only [map_mul]
    rw [hf]
    simp [originShift]

lemma originShift_ne_zero {R σ : Type*} [CommRing R] (a : σ → R)
    {f : MvPolynomial σ R} (hf : f ≠ 0) : originShift a f ≠ 0 := by
  intro h
  apply hf
  rw [← originShift_neg a f, h, map_zero]

lemma originShift_map {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : σ → R) (f : MvPolynomial σ R) :
    map φ (originShift a f) = originShift (fun j => φ (a j)) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [originShift]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    simp only [map_mul]
    rw [hf]
    simp [originShift]

lemma eval_zero_originShift {R σ : Type*} [CommRing R] (a : σ → R)
    (f : MvPolynomial σ R) : eval (0 : σ → R) (originShift a f) = eval a f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [originShift]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    simp only [map_mul]
    rw [hf]
    simp [originShift]

/-- A genuine reduced point of a nonzero equation has a positive multiplicity,
measured after translation, at most the original integer equation's degree. -/
theorem exists_reduction_multiplicity {p : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ) (a : Fin 2 → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      map (Int.castRingHom (ZMod p)) (planeTranslate a f) ∈
        idealOfVars (Fin 2) (ZMod p) ^ μ ∧
      homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (planeTranslate a f)) ≠ 0 := by
  let φ := Int.castRingHom (ZMod p)
  have hshift : map φ (planeTranslate a f) = originShift (fun j => φ (a j)) (map φ f) :=
    originShift_map φ a f
  have hn : map φ (planeTranslate a f) ≠ 0 := by
    rw [hshift]
    exact originShift_ne_zero _ hf
  have hz : eval (0 : Fin 2 → ZMod p) (map φ (planeTranslate a f)) = 0 := by
    rw [hshift, eval_zero_originShift, eval_map]
    exact ha
  have he : map φ (planeTranslate a f) =
      eval₂Hom (C.comp φ) (fun j => X j + C (φ (a j))) f := by
    rw [hshift]
    exact eval₂Hom_map_hom φ _ C f
  have hdeg : (map φ (planeTranslate a f)).totalDegree ≤ f.totalDegree := by
    rw [he]
    apply linear_eval₂_totalDegree_le
    intro j
    exact (totalDegree_add _ _).trans
      (max_le (le_of_eq (totalDegree_X _)) (by rw [totalDegree_C]; omega))
  obtain ⟨μ, hpos, hμdeg, hpow, hμ⟩ := exists_origin_multiplicity _ hn hz
  exact ⟨μ, hpos, hμdeg.trans hdeg, hpow, hμ⟩

end
end AffineCurveCounting
