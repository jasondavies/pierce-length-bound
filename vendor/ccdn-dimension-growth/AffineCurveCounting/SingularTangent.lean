module

public import AffineCurveCounting.HomogeneousHilbert
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Actual origin-adic layers of a nonhomogeneous hypersurface. The first
nonzero homogeneous part supplies the singular multiplicity bound directly. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma homogeneous_mem_origin_power {K σ : Type*} [CommRing K]
    {f : MvPolynomial σ K} {k : ℕ} (hf : f.IsHomogeneous k) :
    f ∈ idealOfVars σ K ^ k := by
  rw [mem_pow_idealOfVars_iff]
  intro e he
  exact (hf.degree_eq_sum_deg_support he).le

/-- Taking the first permitted homogeneous part changes a polynomial only by
one higher power of the actual origin ideal. -/
lemma sub_homogeneousComponent_mem_origin_power {K σ : Type*} [CommRing K]
    {f : MvPolynomial σ K} {k : ℕ} (hf : f ∈ idealOfVars σ K ^ k) :
    f - homogeneousComponent k f ∈ idealOfVars σ K ^ (k + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hf ⊢
  intro e he
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases hk : e.degree = k
  · simp only [hk, ite_true, sub_self]
  · rw [ite_eq_right hk, sub_zero]
    exact hf e (by omega)

def originTruncationIdeal {K σ : Type*} [Field K] (f : MvPolynomial σ K) (k : ℕ) :
    Ideal (MvPolynomial σ K) := Ideal.span {f} ⊔ idealOfVars σ K ^ (k + 1)

/-- The degree-k layer of the origin ideal, in the curve's quotient modulo
its next power. This is the actual image of the ideal power, not a tangent-cone model. -/
def originLayer {K σ : Type*} [Field K] (f : MvPolynomial σ K) (k : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ originTruncationIdeal f k) :=
  ((idealOfVars σ K ^ k).restrictScalars K).map
    (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap

/-- Homogeneous degree-k polynomials generate the actual degree-k layer. -/
theorem originLayer_eq_homogeneousCoordinateSpace {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (k : ℕ) :
    originLayer f k = homogeneousCoordinateSpace (originTruncationIdeal f k) k := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨homogeneousComponent k u,
      homogeneousComponent_isHomogeneous k u, ?_⟩
    apply (sub_eq_zero.mp ?_)
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (show idealOfVars σ K ^ (k + 1) ≤ originTruncationIdeal f k from le_sup_right)
    simpa only [neg_sub] using (idealOfVars σ K ^ (k + 1)).neg_mem
      (sub_homogeneousComponent_mem_origin_power hu)
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨u, homogeneous_mem_origin_power hu, rfl⟩

/-- The initial homogeneous equation really vanishes in each origin-adic layer
after multiplying by an allowed homogeneous polynomial. -/
lemma initial_form_multiple_mem_truncation {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} {μ k : ℕ} (hf : f ∈ idealOfVars σ K ^ μ) (hk : μ ≤ k)
    {u : MvPolynomial σ K} (hu : u.IsHomogeneous (k - μ)) :
    homogeneousComponent μ f * u ∈ originTruncationIdeal f k := by
  have hr := Ideal.mul_mem_mul (sub_homogeneousComponent_mem_origin_power hf)
    (homogeneous_mem_origin_power hu)
  rw [← pow_add, show μ + 1 + (k - μ) = k + 1 by omega] at hr
  have hfu : f * u ∈ originTruncationIdeal f k :=
    (show Ideal.span {f} ≤ originTruncationIdeal f k from le_sup_left)
      (Ideal.mem_span_singleton.mpr (dvd_mul_right f u))
  have hru : (f - homogeneousComponent μ f) * u ∈ originTruncationIdeal f k :=
    (show idealOfVars σ K ^ (k + 1) ≤ originTruncationIdeal f k from le_sup_right) hr
  convert (originTruncationIdeal f k).sub_mem hfu hru using 1
  ring

/-- The first nonzero homogeneous part gives the expected binomial upper bound
for the actual local layer. No tangent-cone or graded-ring identification is assumed. -/
theorem originLayer_hilbert_bound {K : Type*} [Field K] {n μ k : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f ∈ idealOfVars (Fin (n + 1)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) (hk : μ ≤ k) :
    Module.finrank K (originLayer f k) + (n + (k - μ)).choose (k - μ) ≤
      (n + k).choose k := by
  let g := homogeneousComponent μ f
  let V := homogeneousSubmodule (Fin (n + 1)) K k
  let U := homogeneousMultiples g μ k
  let φ := (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap
  let _ : Module.Finite K V := Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  have hUV : U ≤ V := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    change (g * u).IsHomogeneous k
    simpa only [Nat.add_sub_of_le hk] using (homogeneousComponent_isHomogeneous μ f).mul hu
  have hker : U ≤ φ.ker := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (initial_form_multiple_mem_truncation hf hk hu)
  have h := finrank_map_add_kernel_subspace_le φ V U hUV hker
  rw [homogeneousMultiples_finrank _ hμ, finrank_homogeneousSubmodule,
    finrank_homogeneousSubmodule] at h
  rwa [originLayer_eq_homogeneousCoordinateSpace]

instance originLayer_finite {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial σ K) (k : ℕ) : Module.Finite K (originLayer f k) := by
  rw [originLayer_eq_homogeneousCoordinateSpace]
  let _ : Module.Finite K (homogeneousSubmodule σ K k) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  unfold homogeneousCoordinateSpace
  infer_instance

lemma originLayer_finrank_le {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (k : ℕ) :
    Module.finrank K (originLayer f k) ≤ (n + k).choose k := by
  rw [originLayer_eq_homogeneousCoordinateSpace]
  let _ : Module.Finite K (homogeneousSubmodule (Fin (n + 1)) K k) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  exact (Submodule.finrank_map_le _ _).trans_eq (finrank_homogeneousSubmodule n k)

/-- In the plane-curve case each actual origin-adic layer has dimension at most
its multiplicity. This is the bound needed for the quadratic local exponent. -/
theorem plane_originLayer_finrank_le_multiplicity {K : Type*} [Field K]
    {μ k : ℕ} (f : MvPolynomial (Fin 2) K)
    (hf : f ∈ idealOfVars (Fin 2) K ^ μ) (hμ : homogeneousComponent μ f ≠ 0) :
    Module.finrank K (originLayer f k) ≤ μ := by
  by_cases hk : μ ≤ k
  · have h := originLayer_hilbert_bound (n := 1) f hf hμ hk
    simp only [Nat.add_comm 1, Nat.choose_succ_self_right] at h
    change Module.finrank K (originLayer f k) + (k - μ + 1) ≤ k + 1 at h
    omega
  · have h := originLayer_finrank_le (n := 1) f k
    simp only [Nat.add_comm 1, Nat.choose_succ_self_right] at h
    change Module.finrank K (originLayer f k) ≤ k + 1 at h
    omega

end
end AffineCurveCounting
