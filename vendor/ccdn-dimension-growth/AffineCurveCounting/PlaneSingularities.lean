module

public import AffineCurveCounting.Bezout

/-! The singular-point correction in the finite-field curve estimate. The
remaining estimate for all nonsingular rational points is not asserted here. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem pderiv_totalDegree_le {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (i : σ) : (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff : f.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  have he : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
    simp
  rw [he] at hd
  omega

/-- Below the characteristic, a nonconstant polynomial has a nonzero partial
derivative. This explicitly excludes inseparable equations. -/
theorem exists_pderiv_ne_zero_of_degree_lt_char {K σ : Type*} [Field K] [Fintype σ]
    {p : ℕ} [CharP K p] (f : MvPolynomial σ K)
    (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p) :
    ∃ i, pderiv i f ≠ 0 := by
  classical
  have hne : f.support.Nonempty := by
    by_contra h
    have hz : f.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [totalDegree, hz] at hpos
  obtain ⟨m, hm, hdeg⟩ := Finset.exists_mem_eq_sup f.support hne
    (fun m => m.sum (fun _ e => e))
  have hsm : m.sum (fun _ e => e) = ∑ i, m i := by
    rw [Finsupp.sum_fintype]
    intro i
    rfl
  have hsum : 0 < ∑ i, m i := by
    have : 0 < m.sum (fun _ e => e) := by simpa only [totalDegree, hdeg] using hpos
    simpa only [hsm] using this
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hsum
  have hmi : m i ≤ f.totalDegree := by
    calc m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = m.sum (fun _ e => e) := hsm.symm
      _ ≤ f.totalDegree := le_totalDegree hm
  let u := m - Finsupp.single i 1
  have hui : u i + 1 = m i := by simp only [u, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
  have hu : u + Finsupp.single i 1 = m := by
    apply tsub_add_cancel_of_le
    intro j
    by_cases hji : j = i
    · subst j; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_eq_of_ne hji]
  have hcast : (m i : K) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt hi (lt_of_le_of_lt hmi hchar)
      ((CharP.cast_eq_zero_iff K p (m i)).mp h)
  refine ⟨i, fun hz => ?_⟩
  have hc := congrArg (fun g : MvPolynomial σ K => g.coeff u) hz
  rw [coeff_pderiv, hu] at hc
  change f.coeff m * ((u i : K) + 1) = 0 at hc
  have he : (u i : K) + 1 = (m i : K) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : K)) hui
  rw [he] at hc
  exact (mul_ne_zero (mem_support_iff.mp hm) hcast) hc

/-- Distinct singular points of an irreducible plane equation of degree `d`
number at most `d(d-1)`, whenever the degree is smaller than the characteristic. -/
theorem plane_singular_points_card_le {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {p : ℕ} [CharP K p] (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0)
    (hzsing : ∀ i j, eval (z i) (pderiv j f) = 0) :
    Fintype.card ι ≤ f.totalDegree * (f.totalDegree - 1) := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero_of_degree_lt_char f hpos hchar
  have hdeg := pderiv_totalDegree_le f j
  have hnd : ¬ f ∣ pderiv j f := by
    intro hd
    obtain ⟨q, he⟩ := hd
    have hq : q ≠ 0 := by intro hq; simp [hq] at he; exact hj he
    have htotal := totalDegree_mul_of_isDomain hf.ne_zero hq
    rw [← he] at htotal
    omega
  exact (plane_common_zeros_card_le f (pderiv j f) hf hnd z hz hzf
    (fun i => hzsing i j)).trans (Nat.mul_le_mul_left _ hdeg)

end
end AffineCurveCounting
