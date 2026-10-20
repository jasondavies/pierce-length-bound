module

public import AffineCurveCounting.HomogeneousMonomials
public import AffineCurveCounting.PlaneHilbert

/-! Exact homogeneous Hilbert functions of a principal equation. Multiplication
by a homogeneous nonzero equation identifies the entire homogeneous kernel. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma homogeneousComponent_mul_left {K σ : Type*} [CommRing K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (u : MvPolynomial σ K) (k : ℕ) :
    homogeneousComponent (d + k) (f * u) = f * homogeneousComponent k u := by
  classical
  calc
    homogeneousComponent (d + k) (f * u) =
        homogeneousComponent (d + k) (f * ∑ j ∈ Finset.range (u.totalDegree + 1),
          homogeneousComponent j u) := by rw [sum_homogeneousComponent]
    _ = ∑ j ∈ Finset.range (u.totalDegree + 1),
        homogeneousComponent (d + k) (f * homogeneousComponent j u) := by rw [Finset.mul_sum, map_sum]
    _ = homogeneousComponent (d + k) (f * homogeneousComponent k u) := by
      apply Finset.sum_eq_single k
      · intro j _ hjk
        rw [homogeneousComponent_of_mem (hf.mul (homogeneousComponent_isHomogeneous j u))]
        simp only [show d + k ≠ d + j by omega, ite_false]
      · intro hk
        have hk' : u.totalDegree < k := by simpa using hk
        rw [homogeneousComponent_eq_zero k u hk', mul_zero, map_zero]
    _ = f * homogeneousComponent k u :=
      homogeneousComponent_eq_self (hf.mul (homogeneousComponent_isHomogeneous k u))

lemma homogeneous_multiplier {K σ : Type*} [CommRing K] [IsDomain K]
    {f u : MvPolynomial σ K} {d M : ℕ} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hfu : (f * u).IsHomogeneous M) (hM : d ≤ M) : u.IsHomogeneous (M - d) := by
  have he : f * u = f * homogeneousComponent (M - d) u := by
    rw [← homogeneousComponent_mul_left hf, Nat.add_sub_of_le hM, homogeneousComponent_eq_self hfu]
  rw [mul_left_cancel₀ hf0 he]
  exact homogeneousComponent_isHomogeneous _ _

def homogeneousCoordinateSpace {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (M : ℕ) : Submodule K (MvPolynomial σ K ⧸ I) :=
  (homogeneousSubmodule σ K M).map (Ideal.Quotient.mkₐ K I).toLinearMap

def homogeneousMultiples {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (d M : ℕ) : Submodule K (MvPolynomial σ K) :=
  (homogeneousSubmodule σ K (M - d)).map (LinearMap.mulLeft K f)

theorem homogeneousMultiples_finrank {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (d M : ℕ) :
    Module.finrank K (homogeneousMultiples f d M) =
      Module.finrank K (homogeneousSubmodule σ K (M - d)) :=
  (Submodule.equivMapOfInjective (LinearMap.mulLeft K f)
    (fun _ _ h => mul_left_cancel₀ hf h) _).finrank_eq.symm

theorem principal_homogeneous_finrank {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial σ K) {d M : ℕ} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hM : d ≤ M) :
    Module.finrank K (homogeneousCoordinateSpace (Ideal.span {f}) M) +
      Module.finrank K (homogeneousSubmodule σ K (M - d)) =
      Module.finrank K (homogeneousSubmodule σ K M) := by
  let φ := (Ideal.Quotient.mkₐ K (Ideal.span {f})).toLinearMap
  let V := homogeneousSubmodule σ K M
  have hk : V ⊓ φ.ker = homogeneousMultiples f d M := by
    ext x
    constructor
    · rintro ⟨hx, hz⟩
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
      exact Submodule.mem_map.mpr ⟨u, homogeneous_multiplier hf hf0 hx hM, rfl⟩
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      refine ⟨?_, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (dvd_mul_right f u))⟩
      change (f * u).IsHomogeneous M
      simpa only [Nat.add_sub_of_le hM] using hf.mul hu
  let _ : Module.Finite K V := Module.Finite.of_fg (homogeneousSubmodule_fg σ K M)
  have h := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict V)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he := Submodule.finrank_map_subtype_eq V (φ.ker.comap V.subtype)
  rw [Submodule.map_comap_subtype, hk, homogeneousMultiples_finrank f hf0] at he
  rw [← he] at h
  exact h

/-- Exact projective hypersurface Hilbert count, with no geometric hypothesis. -/
theorem principal_homogeneous_hilbert_count {K : Type*} [Field K]
    {n d M : ℕ} (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hM : d ≤ M) :
    Module.finrank K (homogeneousCoordinateSpace (Ideal.span {f}) M) +
      (n + (M - d)).choose (M - d) = (n + M).choose M := by
  simpa only [finrank_homogeneousSubmodule] using principal_homogeneous_finrank f hf hf0 hM

end
end AffineCurveCounting
