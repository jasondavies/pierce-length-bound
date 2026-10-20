module

public import AffineCurveCounting.PolynomialLinearDescent

/-! Irreducible base-field plane curves that split over an extension have at
most d² base-field points. Linear coefficient descent and Bézout suffice;
no Galois transitivity or smooth-point criterion is assumed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma plane_extension_section_card_le {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial (Fin 2) k) (hf : Irreducible f)
    (g : MvPolynomial (Fin 2) K) (hg : g ≠ 0) (hdeg : g.totalDegree < f.totalDegree)
    (z : ι → Fin 2 → k) (hinj : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (algebraMap k K ∘ z i) g = 0) :
    Fintype.card ι ≤ f.totalDegree * g.totalDegree := by
  obtain ⟨g₀, hg₀, hdeg₀, hzero⟩ := exists_nonzero_polynomial_linear_descent (k := k) g hg
  have hnd : ¬ f ∣ g₀ := by
    intro hdiv
    have h := totalDegree_le_of_dvd_of_isDomain hdiv hg₀
    omega
  exact (plane_common_zeros_card_le f g₀ hf hnd z hinj hzf (fun i => hzero (z i) (hzg i))).trans
    (Nat.mul_le_mul_left _ hdeg₀)

lemma plane_points_card_le_of_extension_factorization {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial (Fin 2) k) (hf : Irreducible f)
    (g h : MvPolynomial (Fin 2) K) (hg : g ≠ 0) (hh : h ≠ 0)
    (hgd : 0 < g.totalDegree) (hhd : 0 < h.totalDegree)
    (hfac : MvPolynomial.map (algebraMap k K) f = g * h)
    (z : ι → Fin 2 → k) (hinj : Function.Injective z) (hz : ∀ i, eval (z i) f = 0) :
    Fintype.card ι ≤ f.totalDegree ^ 2 := by
  classical
  have hdegree : g.totalDegree + h.totalDegree = f.totalDegree := by
    have hm : (MvPolynomial.map (algebraMap k K) f).totalDegree = f.totalDegree := by
      unfold totalDegree
      rw [support_map_of_injective _ (algebraMap k K).injective]
    rw [hfac, totalDegree_mul_of_isDomain hg hh] at hm
    exact hm
  let S := Finset.univ.filter (fun i : ι => eval (algebraMap k K ∘ z i) g = 0)
  let T := Finset.univ.filter (fun i : ι => ¬ eval (algebraMap k K ∘ z i) g = 0)
  have hs := plane_extension_section_card_le f hf g hg (by omega)
    (fun i : S => z i.val) (hinj.comp Subtype.val_injective)
    (fun i => hz i.val) (fun i => (Finset.mem_filter.mp i.property).2)
  have ht := plane_extension_section_card_le f hf h hh (by omega)
    (fun i : T => z i.val) (hinj.comp Subtype.val_injective)
    (fun i => hz i.val) (by
      intro i
      have he := congrArg (algebraMap k K) (hz i.val)
      rw [map_eval, hfac, eval_mul, map_zero] at he
      exact (mul_eq_zero.mp he).resolve_left (Finset.mem_filter.mp i.property).2)
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun i : ι => eval (algebraMap k K ∘ z i) g = 0)
  simp only [Fintype.card_coe] at hs ht
  change S.card + T.card = Finset.univ.card at hsum
  rw [Finset.card_univ] at hsum
  calc
    Fintype.card ι = S.card + T.card := hsum.symm
    _ ≤ f.totalDegree * g.totalDegree + f.totalDegree * h.totalDegree := Nat.add_le_add hs ht
    _ = f.totalDegree ^ 2 := by rw [← Nat.mul_add, hdegree, pow_two]

lemma totalDegree_pos_of_nonzero_nonunit {k : Type*} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (hf : f ≠ 0) (hu : ¬ IsUnit f) : 0 < f.totalDegree := by
  by_contra hd
  have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos hd)
  apply hu
  have hc : f.coeff 0 ≠ 0 := by
    intro h
    apply hf
    simpa only [h, map_zero] using he
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- Splitting over any extension gives the unconditional d² bound on
base-field points. No hypothesis on the extension's Galois group is needed. -/
theorem nonabsolute_plane_points_card_le {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial (Fin 2) k) (hf : Irreducible f) (hd : 0 < f.totalDegree)
    (hred : ¬ Irreducible (MvPolynomial.map (algebraMap k K) f))
    (z : ι → Fin 2 → k) (hinj : Function.Injective z) (hz : ∀ i, eval (z i) f = 0) :
    Fintype.card ι ≤ f.totalDegree ^ 2 := by
  have hmap0 : MvPolynomial.map (algebraMap k K) f ≠ 0 := by
    exact fun he => hf.ne_zero ((map_injective (algebraMap k K) (algebraMap k K).injective) (by simpa using he))
  have hmapu : ¬ IsUnit (MvPolynomial.map (algebraMap k K) f) := by
    intro hu
    have he := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    unfold totalDegree at he
    rw [support_map_of_injective _ (algebraMap k K).injective] at he
    exact (Nat.ne_of_gt hd) he
  have hfac : ∃ g h : MvPolynomial (Fin 2) K,
      MvPolynomial.map (algebraMap k K) f = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! hn
    apply hred
    refine ⟨hmapu, ?_⟩
    intro g h he
    by_cases hu : IsUnit g
    · exact Or.inl hu
    · exact Or.inr (hn g h he hu)
  obtain ⟨g, h, hfac, hgu, hhu⟩ := hfac
  have hg : g ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hh : h ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  exact plane_points_card_le_of_extension_factorization f hf g h hg hh
    (totalDegree_pos_of_nonzero_nonunit g hg hgu) (totalDegree_pos_of_nonzero_nonunit h hh hhu)
    hfac z hinj hz

end
end AffineCurveCounting
