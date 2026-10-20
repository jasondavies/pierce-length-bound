module

public import AffineCurveCounting.ClosedFormReducibility
public import AffineCurveCounting.ClosedFormMinorCharge
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! A coefficient-controlled bad-prime witness for monic integer bivariate
equations. Bad reduction is actual reducibility over an algebraic closure of
the residue field, not an assumed matrix-rank predicate. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Real

/-- The actual reduced equation fails to be irreducible over an algebraic
closure of the prime field. The primality witness supplies the field instance. -/
def BivariateGeometricBadPrime (f : ℤ[X][X]) (p : ℕ) : Prop :=
  ∃ hp : p.Prime, let _ : Fact p.Prime := ⟨hp⟩
    ¬Irreducible (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p))) f)

lemma monic_bad_prime_dvd_coefficient_minor
    (d : ℕ) (hd : 0 < d) (f : ℤ[X][X]) (hf : f.Monic)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d)
    (a : Fin (2 * d ^ 2 - 1) → ℕ × ℕ)
    (c : Fin (2 * d ^ 2 - 1) → ClosedFormColumns d)
    (p : ℕ) (hp : d < p) (hbad : BivariateGeometricBadPrime f p) :
    (p : ℤ) ∣ ((closedFormCoefficientMatrix d f).submatrix a c).det := by
  obtain ⟨hpp, hred⟩ := hbad
  let : Fact p.Prime := ⟨hpp⟩
  let K := AlgebraicClosure (ZMod p)
  change ¬Irreducible (bivariateMap (Int.castRingHom K) f) at hred
  have hr := closedForm_rank_drop_of_not_irreducible p d hd hp
    (bivariateMap (Int.castRingHom K) f) (bivariateMap_monic _ hf) hred
    ((bivariateMap_natDegree_of_monic _ hf).trans hdeg)
    ((bivariateTotalDegree_map_le _ f).trans htotal)
  apply characteristic_dvd_closedForm_minor_of_rank_lt (K := K) p d (2 * d ^ 2 - 1) f a c
  omega

/-- For a monic integer equation of full outer degree, absolute irreducibility
in characteristic zero constructs a positive integer divisible by every
geometric bad prime above the degree, with the required logarithmic height. -/
theorem exists_monic_bad_prime_witness
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (hd : 1 ≤ d) (f : ℤ[X][X]) (hf : f.Monic)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d)
    (hir : Irreducible (bivariateMap (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) ∧
      ∀ p : ℕ, d < p → BivariateGeometricBadPrime f p → (p : ℤ) ∣ D := by
  have hm := bivariateMap_monic (Int.castRingHom F) hf
  have hdegF : (bivariateMap (Int.castRingHom F) f).degree = d := by
    rw [degree_eq_natDegree hm.ne_zero, bivariateMap_natDegree_of_monic _ hf, hdeg]
  obtain ⟨a, c, _, _, hD⟩ := exists_closedForm_integer_minor d f hir hm hdegF
  let D := ((closedFormCoefficientMatrix d f).submatrix a c).det
  refine ⟨|D|, abs_pos.mpr hD, ?_, ?_⟩
  · simpa only [D, Int.cast_abs] using closedForm_minor_log_height d (2 * d ^ 2 - 1) hd
      (by omega) f H hH hcoeff (hdeg.le)
      (fun i => (bivariate_coefficient_natDegree_le_totalDegree f i).trans htotal) a c hD
  · intro p hp hbad
    exact (dvd_abs _ _).mpr (monic_bad_prime_dvd_coefficient_minor d (by omega) f hf hdeg htotal a c p hp hbad)

/-- The geometric bad-prime charge in the monic case has the required scaled
logarithmic-height bound; no finite-field counting result is used here. -/
theorem monic_geometric_bad_prime_charge
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (d : ℕ) (hd : 1 ≤ d) (f : ℤ[X][X]) (hf : f.Monic)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d)
    (hir : Irreducible (bivariateMap (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : BivariateCoefficientBound f H)
    (P : Finset ℕ) (hbad : ∀ p ∈ P, BivariateGeometricBadPrime f p)
    (hlo : ∀ p ∈ P, 27 * (d : ℝ) ^ 4 < (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log (1 + Real.log H / (d : ℝ) ^ 2) + 2 * mertensError + 1 := by
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_monic_bad_prime_witness d hd f hf hdeg htotal hir H hH hcoeff
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcut : (d : ℝ) ≤ 27 * (d : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  refine bad_prime_charge_of_height (D := D) (L := 27 * (d : ℝ) ^ 4)
    (H := 1 + Real.log H / (d : ℝ) ^ 2) P hD ?_ ?_ ?_ ?_ hlo hheight
  · intro p hp
    exact (hbad p hp).choose
  · intro p hp
    apply hdiv p _ (hbad p hp)
    exact_mod_cast hcut.trans_lt (hlo p hp)
  · linarith
  · exact le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _))

end
end AffineCurveCounting
