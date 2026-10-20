module

public import AffineCurveCounting.PlaneProjectionKernel
public import AffineCurveCounting.NonabsolutePlaneCount

/-! The irreducible image equation has degree at most the original affine
Hilbert degree. This is an upper bound; preservation of degree is not assumed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma eventual_linear_slope_le (f g : ℕ → ℕ) (a b : ℕ)
    (hf : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N, (f n : ℤ) = (a : ℤ) * n + c)
    (hg : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N, (g n : ℤ) = (b : ℤ) * n + c)
    (hle : ∀ n, f n ≤ g n) : a ≤ b := by
  obtain ⟨N₀, c, hc⟩ := hf
  obtain ⟨N₁, e, he⟩ := hg
  by_contra hbad
  have hab : b + 1 ≤ a := by omega
  let N := N₀ + N₁ + c.natAbs + e.natAbs + 1
  have hN₀ : N₀ ≤ N := by dsimp [N]; omega
  have hN₁ : N₁ ≤ N := by dsimp [N]; omega
  have hh : (a : ℤ) * N + c ≤ (b : ℤ) * N + e := by
    rw [← hc N hN₀, ← he N hN₁]
    exact_mod_cast hle N
  have hmul : ((b : ℤ) + 1) * N ≤ (a : ℤ) * N := by
    exact_mod_cast Nat.mul_le_mul_right N hab
  have hce : -(c.natAbs : ℤ) ≤ c := by
    have hh : -c ≤ ((-c).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at hh
    omega
  have hee : e ≤ (e.natAbs : ℤ) := Int.le_natAbs
  have hNeq : (N : ℤ) = N₀ + N₁ + c.natAbs + e.natAbs + 1 := by
    simp only [N, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- A principal image equation of a linear projection has degree at most the
source's affine Hilbert degree. -/
theorem plane_projection_equation_degree_le {K τ : Type*} [Field K] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (d : ℕ)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree ≤ d := by
  apply eventual_linear_slope_le
    (fun M => Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M))
    (fun M => Module.finrank K (filteredCoordinateSpace I M)) f.totalDegree d
    ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
      fun M hM => principal_plane_hilbert_function f hf hM⟩ hdegree
  intro M
  rw [← hker]
  exact linear_projection_filtered_finrank_le I a ha M

/-- A linear plane projection with a transcendental coordinate has an actual
irreducible equation of positive degree at most d and no extra kernel relations. -/
theorem exists_plane_projection_equation_degree_le {K τ : Type*} [Field K] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (j : Fin 2) (hj : Transcendental K ((Ideal.Quotient.mk I) (a j))) :
    ∃ f : MvPolynomial (Fin 2) K, Irreducible f ∧ 0 < f.totalDegree ∧ f.totalDegree ≤ d ∧
      ∀ g, aeval a g ∈ I ↔ f ∣ g := by
  obtain ⟨f, hf, hker⟩ := exists_plane_projection_equation I a ha d hdegree j hj
  refine ⟨f, hf, totalDegree_pos_of_nonzero_nonunit f hf.ne_zero hf.not_isUnit,
    plane_projection_equation_degree_le I a ha d hdegree f hf.ne_zero hker, ?_⟩
  intro g
  have hh : aeval a g ∈ I ↔ g ∈ RingHom.ker (projectionCoordinateMap I a) := by
    change _ ↔ (Ideal.Quotient.mk I) (aeval a g) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  rw [hh, hker, Ideal.mem_span_singleton]

/-- The defining image equation vanishes at projections of actual source points. -/
lemma projection_equation_eval_zero {K τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (f : MvPolynomial (Fin 2) K) (hf : aeval a f ∈ I)
    (z : τ → K) (hz : ∀ g ∈ I, eval z g = 0) :
    eval (fun i => eval z (a i)) f = 0 := by
  have hh := hz (aeval a f) hf
  change eval z (eval₂ C a f) = 0 at hh
  rwa [← eval_assoc] at hh

end
end AffineCurveCounting
