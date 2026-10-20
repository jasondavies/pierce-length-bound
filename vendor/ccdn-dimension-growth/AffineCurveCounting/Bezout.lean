module

public import AffineCurveCounting.PolynomialSection
public import AffineCurveCounting.PlaneHilbert

/-! Sharp bounds for distinct points in proper polynomial sections. In the plane,
the principal Hilbert function gives the usual product-of-degrees bound. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- An irreducible plane curve and a polynomial not divisible by its equation
have at most the product of their degrees many distinct common zeros. -/
theorem plane_common_zeros_card_le {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (f g : MvPolynomial (Fin 2) K) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzf : ∀ i, MvPolynomial.eval (z i) f = 0)
    (hzg : ∀ i, MvPolynomial.eval (z i) g = 0) :
    Fintype.card ι ≤ f.totalDegree * g.totalDegree := by
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  let : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  apply polynomial_section_card_le_degree I f.totalDegree
    ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
      fun N hN => principal_plane_hilbert_function f hf.ne_zero hN⟩
    g (by simpa only [I, Ideal.mem_span_singleton] using hfg)
    g.totalDegree le_rfl z hz _ hzg
  intro i h hh
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hh
  rw [MvPolynomial.eval_mul, hzf, zero_mul]

/-- The section bound directly in the real-radius integer counting interface. -/
theorem count_curve_section_le {n d : ℕ} (I : Ideal (CoordinatePolynomial n))
    [I.IsPrime] (hd : HasAffineCurveDegree I d)
    (g : CoordinatePolynomial n) (hg : g ∉ I) (B : ℝ) :
    count (idealZeroLocus I ∩ zeroLocus g) B ≤ d * g.totalDegree := by
  classical
  let S := integralPoints (idealZeroLocus I ∩ zeroLocus g) B
  let z : S → RatPoint n := fun x => rationalPoint x.val
  have hz : Function.Injective z := by
    intro x y h
    apply Subtype.ext
    funext j
    exact Int.cast_injective (congrFun h j)
  have hzp (i : S) : z i ∈ idealZeroLocus I :=
    (mem_integralPoints.mp i.property).2.1
  have hzg (i : S) : MvPolynomial.eval (z i) g = 0 :=
    (mem_integralPoints.mp i.property).2.2
  have h := polynomial_section_card_le_degree I d hd g hg g.totalDegree le_rfl z hz hzp hzg
  simpa only [Fintype.card_coe, S, count] using h

theorem idealZeroLocus_span_singleton {n : ℕ} (f : CoordinatePolynomial n) :
    idealZeroLocus (Ideal.span {f}) = zeroLocus f := by
  ext x
  constructor
  · intro hx
    exact hx f (Ideal.subset_span (by simp))
  · intro hx h hh
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hh
    change MvPolynomial.eval x (f * q) = 0
    rw [MvPolynomial.eval_mul, show MvPolynomial.eval x f = 0 from hx, zero_mul]

/-- The final sharp intersection step for an auxiliary polynomial. Its degree
and nondivisibility must still be supplied by the determinant method. -/
theorem count_plane_common_zeros_le (f g : CoordinatePolynomial 2)
    (hf : Irreducible f) (hfg : ¬ f ∣ g) (B : ℝ) :
    count (zeroLocus f ∩ zeroLocus g) B ≤ f.totalDegree * g.totalDegree := by
  let : (Ideal.span {f}).IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  have h := count_curve_section_le (Ideal.span {f})
    (principal_plane_hasAffineCurveDegree f hf.ne_zero) g
    (by simpa only [Ideal.mem_span_singleton] using hfg) B
  rwa [idealZeroLocus_span_singleton] at h

end
end AffineCurveCounting
