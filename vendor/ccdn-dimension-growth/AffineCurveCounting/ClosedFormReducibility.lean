module

public import AffineCurveCounting.ClosedFormFactorRank
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! The full reducibility-to-rank-drop implication for normalized monic
bivariate equations of degree below the characteristic. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial

lemma exists_monic_bivariate_irreducible_factor {F : Type*} [Field F]
    (f : F[X][X]) (hf : f.Monic) (hu : ¬IsUnit f) :
    ∃ g : F[X][X], Irreducible g ∧ g.Monic ∧ g ∣ f := by
  obtain ⟨r, hr, hrf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf.ne_zero
  obtain ⟨s, hs⟩ := hrf
  have hl : r.leadingCoeff * s.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hs]
    exact hf
  have hsU : IsUnit s.leadingCoeff :=
    ⟨⟨s.leadingCoeff, r.leadingCoeff, by rw [mul_comm, hl], hl⟩, rfl⟩
  have hC : IsUnit (C s.leadingCoeff) := hsU.map C
  have ha := associated_mul_unit_right r (C s.leadingCoeff) hC
  refine ⟨r * C s.leadingCoeff, ha.irreducible_iff.mp hr, ?_, ?_⟩
  · change (r * C s.leadingCoeff).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, hl]
  · exact ha.dvd_iff_dvd_left.mp ⟨s, hs⟩

/-- Extract one monic irreducible factor with its full multiplicity; the
remaining factor is monic and coprime after passage to the fraction field. -/
lemma exists_monic_bivariate_primary_factor {F : Type*} [Field F]
    (f : F[X][X]) (hf : f.Monic) (hu : ¬IsUnit f) :
    ∃ (g h : F[X][X]) (m : ℕ), Irreducible g ∧ g.Monic ∧ h.Monic ∧
      0 < m ∧ f = g ^ m * h ∧
      IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
        (h.map (algebraMap F[X] (RatFunc F))) := by
  obtain ⟨g, hg, hgm, hgf⟩ := exists_monic_bivariate_irreducible_factor f hf hu
  obtain ⟨m, h, hnd, he⟩ := WfDvdMonoid.max_power_factor hf.ne_zero hg
  have hm : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    simp only [hz, pow_zero, one_mul] at he
    exact hnd (he ▸ hgf)
  have hhm : h.Monic := (hgm.pow m).of_mul_monic_left (he ▸ hf)
  refine ⟨g, h, m, hg, hgm, hhm, hm, he, ?_⟩
  have hgR : Irreducible (g.map (algebraMap F[X] (RatFunc F))) :=
    hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  apply (hgR.isCoprime_or_dvd _).resolve_right
  intro hdiv
  exact hnd ((hgm.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map (RatFunc F)).mpr hdiv)

/-- A reducible normalized equation of total degree at most d, with outer
degree d below the characteristic, has coefficient-matrix kernel dimension
at least two. Both squarefree and repeated-factor cases are covered. -/
theorem closedForm_rank_drop_of_not_irreducible
    {F : Type*} [Field F] (p d : ℕ) [CharP F p] (hd : 0 < d) (hdp : d < p)
    (f : F[X][X]) (hf : f.Monic) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hfu : ¬IsUnit f := not_isUnit_of_natDegree_pos f (hdeg ▸ hd)
  obtain ⟨g, h, m, hg, hgm, hhm, hm, he, hcop⟩ :=
    exists_monic_bivariate_primary_factor f hf hfu
  by_cases hm1 : m = 1
  · have he' : f = g * h := by simpa only [hm1, pow_one] using he
    have hhu : ¬IsUnit h := by
      intro hhU
      apply hred
      rw [he']
      exact (associated_mul_unit_left g h hhU).irreducible_iff.mpr hg
    rw [he'] at hdeg htotal ⊢
    exact closedForm_rank_drop_of_coprime_factors p d hd hdp g h hg hgm hhm.ne_zero
      (hhm.natDegree_pos_of_not_isUnit hhu) hcop hdeg htotal
  · have hm2 : m = (m - 2) + 2 := by omega
    rw [hm2] at he
    rw [he] at hdeg htotal ⊢
    exact closedForm_rank_drop_of_repeated_factor p d (m - 2) hd hdp g h hg hgm
      hhm.ne_zero hcop hdeg htotal

end
end AffineCurveCounting
