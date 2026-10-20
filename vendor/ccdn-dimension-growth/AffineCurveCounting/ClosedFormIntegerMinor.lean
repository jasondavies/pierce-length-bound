module

public import AffineCurveCounting.ClosedFormRank
public import AffineCurveCounting.ClosedFormBaseChange
public import AffineCurveCounting.FiniteRowMinor

/-! An actual nonzero integer minor of the closed-form coefficient matrix.
Rank drop after reduction forces divisibility of this same integer. The
geometric rank-drop criterion and the height bound are separate obligations. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

/-- Determinants of selected coefficient minors commute with any coefficient
ring map. -/
theorem closedForm_minor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d r : ℕ) (f : R[X][X])
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d) :
    φ (((closedFormCoefficientMatrix d f).submatrix a c).det) =
      ((closedFormCoefficientMatrix d (bivariateMap φ f)).submatrix a c).det := by
  rw [φ.map_det]
  change (((closedFormCoefficientMatrix d f).map φ).submatrix a c).det = _
  rw [closedFormCoefficientMatrix_map]

/-- A monic integer equation irreducible over an algebraically closed field of
characteristic zero has a nonzero integer coefficient minor of order 2*d²-1. -/
theorem exists_closedForm_integer_minor
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (f : ℤ[X][X])
    (hf : Irreducible (bivariateMap (Int.castRingHom F) f))
    (hm : (bivariateMap (Int.castRingHom F) f).Monic)
    (hdeg : (bivariateMap (Int.castRingHom F) f).degree = d) :
    ∃ (a : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
      (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d),
      Function.Injective a ∧ Function.Injective c ∧
      ((closedFormCoefficientMatrix d f).submatrix a c).det ≠ 0 := by
  have hr := closedForm_coefficient_rank_lower d _ hf hm hdeg
  obtain ⟨a, c, ha, hc, hdet⟩ := exists_nonzero_minor_of_rank_le
    (closedFormCoefficientMatrix d (bivariateMap (Int.castRingHom F) f))
    (2 * d ^ 2 - 1) (by omega)
  refine ⟨a, c, ha, hc, ?_⟩
  intro hz
  apply hdet
  rw [← closedForm_minor_map, hz, map_zero]

/-- Any characteristic-p rank drop below the chosen minor order makes p
 divide its integer determinant. The field may be an algebraic closure. -/
theorem characteristic_dvd_closedForm_minor_of_rank_lt
    {K : Type*} [Field K] (p : ℕ) [CharP K p]
    (d r : ℕ) (f : ℤ[X][X]) (a : Fin r → ℕ × ℕ)
    (c : Fin r → ClosedFormColumns d)
    (hr : (closedFormCoefficientMatrix d (bivariateMap (Int.castRingHom K) f)).rank < r) :
    (p : ℤ) ∣ ((closedFormCoefficientMatrix d f).submatrix a c).det := by
  apply (CharP.intCast_eq_zero_iff K p _).mp
  change (Int.castRingHom K) _ = 0
  rw [closedForm_minor_map]
  by_contra hn
  have he := Matrix.rank_of_det_ne_zero hn
  have hl := (closedFormCoefficientMatrix d (bivariateMap (Int.castRingHom K) f)).rank_submatrix_le a c
  rw [he, Fintype.card_fin] at hl
  omega

end
end AffineCurveCounting
