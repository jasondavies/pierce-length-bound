module

public import AffineCurveCounting.FormalPlaneDifferentiation

/-! A polynomial criterion for the multiplicity form of plane Bézout.
All formal branches are constructed from the nonsingularity assumptions. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Successive tangent derivatives vanishing at distinct smooth points force
N times their cardinality to be at most the section-degree product. -/
theorem plane_tangent_multiplicity_bound {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : ι → Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv (j i).rev f) ≠ 0)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) (N : ℕ)
    (hchar : ∀ n, 0 < n → n < N → (n : K) ≠ 0)
    (hvan : ∀ i r, r < N → eval (z i) ((planeTangent f (j i))^[r] g) = 0) :
    Fintype.card ι * N ≤ f.totalDegree * g.totalDegree := by
  have hb (i : ι) := exists_faithful_formal_plane_branch f hf (z i) (j i).rev
    (hzero i) (hsmooth i)
  choose ψ hconst hparam hfaith using hb
  apply formal_plane_multiplicity_bound f hf z hz ψ
    (fun i => (hfaith i f).mpr dvd_rfl) hconst j
    (by simpa only [Fin.rev_rev] using hparam) g hnd N
  intro i
  exact formal_plane_multiplicity_of_tangent f (ψ i) ((hfaith i f).mpr dvd_rfl)
    (z i) (hconst i) (j i) (by simpa only [Fin.rev_rev] using hparam i)
    (hsmooth i) g N hchar (hvan i)

/-- Characteristic p allows all requested multiplicities up to p. -/
lemma cast_ne_zero_below_characteristic {K : Type*} [Field K]
    (p N : ℕ) [CharP K p] (hN : N ≤ p) :
    ∀ n, 0 < n → n < N → (n : K) ≠ 0 := by
  intro n hn hnN hzero
  have hd := (CharP.cast_eq_zero_iff K p n).mp hzero
  exact (not_le_of_gt (hnN.trans_le hN)) (Nat.le_of_dvd hn hd)

theorem plane_tangent_multiplicity_bound_charP {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (p : ℕ) [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) (j : ι → Fin 2)
    (hsmooth : ∀ i, eval (z i) (pderiv (j i).rev f) ≠ 0)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) (N : ℕ) (hN : N ≤ p)
    (hvan : ∀ i r, r < N → eval (z i) ((planeTangent f (j i))^[r] g) = 0) :
    Fintype.card ι * N ≤ f.totalDegree * g.totalDegree :=
  plane_tangent_multiplicity_bound f hf z hz hzero j hsmooth g hnd N
    (cast_ne_zero_below_characteristic p N hN) hvan

end
end AffineCurveCounting
