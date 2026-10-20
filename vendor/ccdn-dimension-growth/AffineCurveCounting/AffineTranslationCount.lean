module

public import AffineCurveCounting.AffineTranslation
public import AffineCurveCounting.PlaneGridHeight
public import AffineCurveCounting.SingularReduction

/-! Bounded translations remove a zero constant coefficient and preserve the
actual finite-field residue count, primitivity and integer point families. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma affineTranslation_eval {R : Type*} [CommRing R] {n : ℕ}
    (a x : Fin n → R) (f : MvPolynomial (Fin n) R) :
    eval x (affineTranslation R a f) = eval (x + a) f := by
  change eval x (eval₂ C (fun j => X j + C (a j)) f) = _
  rw [← eval_assoc]
  congr 2
  funext j
  simp

lemma affineTranslation_constantCoeff {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (f : MvPolynomial (Fin n) R) :
    (affineTranslation R a f).coeff 0 = eval a f := by
  have he := affineTranslation_eval a 0 f
  simpa only [zero_add, eval_zero, constantCoeff_eq] using he

lemma PrimitiveIntegerPolynomial.translate_affine {n : ℕ} (a : Fin n → ℤ)
    {f : MvPolynomial (Fin n) ℤ} (hf : PrimitiveIntegerPolynomial f) :
    PrimitiveIntegerPolynomial (affineTranslation ℤ a f) := by
  intro c hc
  have hd := (C_dvd_iff_dvd_coeff c _).mpr hc
  have he := map_dvd (affineTranslation ℤ a).symm.toRingHom hd
  have hC : (affineTranslation ℤ a).symm (C c) = C c := (affineTranslation ℤ a).symm.commutes c
  change (affineTranslation ℤ a).symm (C c) ∣
    (affineTranslation ℤ a).symm (affineTranslation ℤ a f) at he
  rw [hC, AlgEquiv.symm_apply_apply] at he
  exact hf c ((C_dvd_iff_dvd_coeff c f).mp he)

/-- Translation of the actual residue zero set, over ZMod p for every p. -/
def affineTranslationResidueEquiv (a : Fin 2 → ℤ) (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    PlaneResidue (affineTranslation ℤ a f) p ≃ PlaneResidue f p where
  toFun x := ⟨x.val + fun j => (a j : ZMod p), by
    have h := x.property
    rw [← eval_map] at h
    rw [affineTranslation_map, affineTranslation_eval] at h
    simpa only [eval_map, Function.comp_def, Int.coe_castRingHom] using h⟩
  invFun x := ⟨x.val - fun j => (a j : ZMod p), by
    rw [← eval_map]
    rw [affineTranslation_map, affineTranslation_eval]
    simpa only [Function.comp_def, Int.coe_castRingHom, sub_add_cancel, eval_map] using x.property⟩
  left_inv x := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv x := by apply Subtype.ext; exact sub_add_cancel _ _

lemma affineTranslation_residue_card (a : Fin 2 → ℤ) (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Nat.card (PlaneResidue (affineTranslation ℤ a f) p) = Nat.card (PlaneResidue f p) :=
  Nat.card_congr (affineTranslationResidueEquiv a f p)

theorem exists_bounded_translation_nonzero_constant (f : MvPolynomial (Fin 2) ℤ) (hf : f ≠ 0) :
    ∃ a : Fin 2 → ℤ, (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      (affineTranslation ℤ a f).coeff 0 ≠ 0 := by
  obtain ⟨x, y, hx, hy, hn, _⟩ := exists_integer_plane_grid_height_witness f hf le_rfl
  refine ⟨![(x : ℤ), (y : ℤ)], ?_, ?_⟩
  · intro j
    fin_cases j
    · change 0 ≤ (x : ℤ) ∧ (x : ℤ) ≤ f.totalDegree
      exact ⟨by positivity, by exact_mod_cast hx⟩
    · change 0 ≤ (y : ℤ) ∧ (y : ℤ) ≤ f.totalDegree
      exact ⟨by positivity, by exact_mod_cast hy⟩
  · rwa [affineTranslation_constantCoeff]

end
end AffineCurveCounting
