module

public import AffineCurveCounting.PolynomialKernelDerivative
public import AffineCurveCounting.PlaneSingularities

/-! In characteristic zero, a plane relation with a transcendental first
coordinate has a nonzero derivative in the second coordinate. That derivative
is a proper section of degree at most d-1 of the source curve. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma pderiv_ne_zero_of_mem_vars_charZero {K σ : Type*} [Field K] [CharZero K]
    (f : MvPolynomial σ K) (i : σ) (hi : i ∈ f.vars) : pderiv i f ≠ 0 := by
  classical
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  have hmpos : 0 < m i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmi)
  let u := m - Finsupp.single i 1
  have hui : u i + 1 = m i := by simp only [u, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
  have hu : u + Finsupp.single i 1 = m := by
    apply tsub_add_cancel_of_le
    intro j
    by_cases hji : j = i
    · subst j; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_eq_of_ne hji]
  intro hz
  have hc := congrArg (fun g : MvPolynomial σ K => g.coeff u) hz
  rw [coeff_pderiv, hu] at hc
  change f.coeff m * ((u i : K) + 1) = 0 at hc
  have he : (u i : K) + 1 = (m i : K) := by exact_mod_cast hui
  rw [he] at hc
  exact (mul_ne_zero (mem_support_iff.mp hm) (Nat.cast_ne_zero.mpr (by omega))) hc

/-- A nonzero relation cannot omit the coordinate complementary to a
transcendental coordinate. -/
theorem plane_relation_pderiv_ne_zero {K A : Type*} [Field K] [CharZero K]
    [CommRing A] [Algebra K A] (ψ : MvPolynomial (Fin 2) K →ₐ[K] A)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hzero : ψ f = 0)
    (j k : Fin 2) (hjk : j ≠ k) (hj : Transcendental K (ψ (X j))) :
    pderiv k f ≠ 0 := by
  classical
  apply pderiv_ne_zero_of_mem_vars_charZero
  by_contra hk
  have hvars : (f.vars : Set (Fin 2)) ⊆ Set.range (fun _ : Unit => j) := by
    intro t ht
    have htk : t ≠ k := fun h => hk (h ▸ ht)
    have htj : t = j := by omega
    exact ⟨(), htj.symm⟩
  obtain ⟨g, hg⟩ := exists_rename_eq_of_vars_subset_range f (fun _ : Unit => j)
    (Function.injective_of_subsingleton _) hvars
  have he : ψ.comp (rename (fun _ : Unit => j)) = aeval (fun _ : Unit => ψ (X j)) := by
    apply MvPolynomial.algHom_ext
    intro t
    simp
  have hi : Function.Injective (aeval (R := K) (fun _ : Unit => ψ (X j))) :=
    (algebraicIndependent_unique_type_iff (R := K) (x := fun _ : Unit => ψ (X j))).mpr hj
  have hz : aeval (fun _ : Unit => ψ (X j)) g = 0 := by
    rw [← he]
    change ψ (rename (fun _ : Unit => j) g) = 0
    rwa [hg]
  have hg0 : g = 0 := hi (by simpa only [map_zero] using hz)
  exact hf (by rw [← hg, hg0, map_zero])

/-- The derivative is a proper degree-(d-1) section when f generates the
actual projection kernel. This is the proposed common reconstruction cut. -/
theorem projection_derivative_proper {K τ : Type*} [Field K] [CharZero K] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g)
    (j k : Fin 2) (hjk : j ≠ k)
    (hj : Transcendental K ((Ideal.Quotient.mk I) (a j))) :
    aeval a (pderiv k f) ∉ I ∧
      (aeval a (pderiv k f)).totalDegree ≤ f.totalDegree - 1 := by
  let ψ := projectionCoordinateMap I a
  have hz : ψ f = 0 := by
    change (Ideal.Quotient.mk I) (aeval a f) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker f).mpr (dvd_refl f))
  have ht : Transcendental K (ψ (X j)) := by
    change Transcendental K ((Ideal.Quotient.mk I) (aeval a (X j)))
    rwa [aeval_X]
  have hp := plane_relation_pderiv_ne_zero ψ f hf hz j k hjk ht
  have hdeg := pderiv_totalDegree_le f k
  have hdpos : 0 < f.totalDegree := by
    by_contra! hn
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hn)
    apply hp
    rw [he, pderiv_C]
  refine ⟨?_, (aeval_totalDegree_le a ha _).trans (by simpa only [one_mul] using hdeg)⟩
  intro hbad
  have hdiv := (hker _).mp hbad
  obtain ⟨g, hg⟩ := hdiv
  have hg0 : g ≠ 0 := by intro he; apply hp; rw [hg, he, mul_zero]
  have he := totalDegree_mul_of_isDomain hf hg0
  rw [← hg] at he
  omega

end
end AffineCurveCounting
