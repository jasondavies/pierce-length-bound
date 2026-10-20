module

public import AffineCurveCounting.BivariateTotalDegree

/-! Rank drop from actual coprime factor decompositions in small degree
relative to the characteristic. Coprimality is imposed in the univariate
fraction-field ring, where factorization can supply it. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial

lemma polynomial_derivative_ne_zero_below_characteristic
    {R : Type*} [CommRing R] [IsDomain R] (p : ℕ) [CharP R p]
    (f : R[X]) (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    f.derivative ≠ 0 := by
  have hf : f ≠ 0 := by intro h; simp [h] at hpos
  have hn : (f.natDegree : R) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt hpos hsmall) ((CharP.cast_eq_zero_iff R p _).mp h)
  intro hz
  have hc := congrArg (fun g : R[X] => g.coeff (f.natDegree - 1)) hz
  rw [coeff_derivative, show f.natDegree - 1 + 1 = f.natDegree by omega, coeff_zero] at hc
  have he : ((f.natDegree - 1 : ℕ) : R) + 1 = (f.natDegree : R) := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hpos]
  rw [he] at hc
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hf) hn) hc

/-- A bounded extra solution outside the scalar gradient span forces rank drop. -/
theorem closedForm_rank_drop_of_extra_form {F : Type*} [Field F]
    (d : ℕ) (hd : 0 < d) (f p q : F[X][X])
    (hf : bivariateTotalDegree f ≤ d) (hf' : f.derivative ≠ 0)
    (hp : InBivariateGrid d p) (hq : InBivariateGrid d q)
    (hclosed : closedFormOperator f (p,q) = 0)
    (hind : ∀ a : F, p ≠ C (C a) * f.derivative) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  obtain ⟨hg₁, hg₂⟩ := bivariate_gradient_in_grid d hd f hf
  apply closedForm_rank_drop_of_two_forms d f
    (f.derivative, (bivariateCoefficientDerivative F) f) (p,q)
    hg₁ hg₂ hp hq (closedFormOperator_gradient f) hclosed
  · intro he
    exact hf' (congrArg Prod.fst he)
  · intro a ha
    apply hind a
    have he := congrArg Prod.fst ha
    change a • f.derivative = p at he
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using he.symm

/-- A nontrivial coprime product gives two independent bounded closed forms,
and hence the required matrix rank drop. -/
theorem closedForm_rank_drop_of_coprime_factors
    {F : Type*} [Field F] (p d : ℕ) [CharP F p] (hd : 0 < d) (hdp : d < p)
    (g h : F[X][X]) (hg : Irreducible g) (hgm : g.Monic)
    (hh : h ≠ 0) (hhpos : 0 < h.natDegree)
    (hcop : IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
      (h.map (algebraMap F[X] (RatFunc F))))
    (hdeg : (g * h).natDegree = d) (htotal : bivariateTotalDegree (g * h) ≤ d) :
    (closedFormCoefficientMatrix d (g * h)).rank + 2 ≤ 2 * d ^ 2 := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hsum := natDegree_mul hg.ne_zero hh
  have hgsmall : g.natDegree < p := by omega
  have hhsmall : h.natDegree < p := by omega
  have hgnat : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hhnat : (h.map φ).natDegree = h.natDegree := natDegree_map_eq_of_injective hinj _
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
    (separable_iff_derivative_ne_zero hgR).mpr
      (polynomial_derivative_ne_zero_below_characteristic p _ (hgnat ▸ hgpos) (hgnat ▸ hgsmall))
  have hh' := polynomial_derivative_ne_zero_below_characteristic p (h.map φ)
    (hhnat ▸ hhpos) (hhnat ▸ hhsmall)
  have hgd : 0 < bivariateTotalDegree g := hgpos.trans_le (bivariate_natDegree_le_totalDegree g)
  obtain ⟨hpgrid, hqgrid⟩ := bivariate_factor_form_in_grid d g h hg.ne_zero hh hgd htotal
  apply closedForm_rank_drop_of_extra_form d hd (g * h)
    (h * g.derivative) (h * (bivariateCoefficientDerivative F) g) htotal
    (polynomial_derivative_ne_zero_below_characteristic p _ (hdeg ▸ hd) (hdeg ▸ hdp)) hpgrid hqgrid
  · have he := bivariate_factor_closed_form g h
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination he
  · intro a he
    apply factor_numerator_not_scalar_gradient (g.map φ) (h.map φ)
      (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg hh' (algebraMap F (RatFunc F) a)
    simpa only [Polynomial.map_mul, Polynomial.map_C, derivative_map, derivative_mul, Polynomial.map_add,
      RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using congrArg (Polynomial.map φ) he

/-- Repeated irreducible factors of every multiplicity at least two likewise
force rank drop; no squarefreeness assumption on the whole equation is used. -/
theorem closedForm_rank_drop_of_repeated_factor
    {F : Type*} [Field F] (p d k : ℕ) [CharP F p] (hd : 0 < d) (hdp : d < p)
    (g h : F[X][X]) (hg : Irreducible g) (hgm : g.Monic) (hh : h ≠ 0)
    (hcop : IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
      (h.map (algebraMap F[X] (RatFunc F))))
    (hdeg : (g ^ (k + 2) * h).natDegree = d)
    (htotal : bivariateTotalDegree (g ^ (k + 2) * h) ≤ d) :
    (closedFormCoefficientMatrix d (g ^ (k + 2) * h)).rank + 2 ≤ 2 * d ^ 2 := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hfn : g ^ (k + 2) * h ≠ 0 := mul_ne_zero (pow_ne_zero _ hg.ne_zero) hh
  have hgdiv : g ∣ g ^ (k + 2) * h := dvd_mul_of_dvd_left (dvd_pow_self g (by omega)) h
  have hgle := natDegree_le_of_dvd hgdiv hfn
  have hgsmall : g.natDegree < p := by omega
  have hgnat : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
    (separable_iff_derivative_ne_zero hgR).mpr
      (polynomial_derivative_ne_zero_below_characteristic p _ (hgnat ▸ hgpos) (hgnat ▸ hgsmall))
  have hgd : 0 < bivariateTotalDegree g := hgpos.trans_le (bivariate_natDegree_le_totalDegree g)
  obtain ⟨hpgrid, hqgrid⟩ := bivariate_power_factor_form_in_grid d k g h hg.ne_zero hh hgd htotal
  apply closedForm_rank_drop_of_extra_form d hd (g ^ (k + 2) * h)
    (g ^ k * h * g.derivative) (g ^ k * h * (bivariateCoefficientDerivative F) g) htotal
    (polynomial_derivative_ne_zero_below_characteristic p _ (hdeg ▸ hd) (hdeg ▸ hdp)) hpgrid hqgrid
  · have he := bivariate_power_factor_closed_form g h k
    change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination he
  · intro a he
    apply power_factor_numerator_not_scalar_gradient (g.map φ) (h.map φ) k
      (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg (algebraMap F (RatFunc F) a)
    have hp : (g.map φ) ^ (k + 2) * h.map φ = (g ^ (k + 2) * h).map φ := by simp
    rw [hp, Polynomial.derivative_map (g ^ (k + 2) * h) φ]
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, derivative_map,
      RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using congrArg (Polynomial.map φ) he

end
end AffineCurveCounting
