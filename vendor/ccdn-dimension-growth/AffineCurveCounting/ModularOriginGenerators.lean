module

public import AffineCurveCounting.OriginTruncationGenerators
public import AffineCurveCounting.ModularPolynomialLift

/-! Lift singular local generators from the actual reduction modulo p. The
remaining error is an explicit multiple of p, with a separate high-order term. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The local generators are actual homogeneous integer polynomials. Their
uniform reduction formula separates the defining equation, the origin-adic
error, and the p-divisible error. -/
theorem exists_integer_origin_generators {p μ : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 2) ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin 2) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0) :
    ∃ (r : ℕ → ℕ) (g : (k : ℕ) → Fin (r k) → MvPolynomial (Fin 2) ℤ),
      (∀ k, r k ≤ μ) ∧ (∀ k j, (g k j).IsHomogeneous k) ∧
      ∀ N u, ∃ (c : (k : Fin N) → Fin (r k.val) → ℤ) (h v w : MvPolynomial (Fin 2) ℤ),
        v ∈ idealOfVars (Fin 2) ℤ ^ N ∧
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j = f * h + v + C (p : ℤ) * w := by
  classical
  let π := Int.castRingHom (ZMod p)
  obtain ⟨r, g, hr, hg, hspan⟩ := exists_plane_truncation_generators (map π f) hf hμ
  refine ⟨r, (fun k j => modularPolynomialLift (g k j)), hr,
    (fun k j => modularPolynomialLift_homogeneous _ (hg k j)), ?_⟩
  intro N u
  obtain ⟨c, hc⟩ := hspan N (map π u)
  obtain ⟨h', hh', v, hv, he⟩ := Submodule.mem_sup.mp hc
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.mp hh'
  let cZ : (k : Fin N) → Fin (r k.val) → ℤ := fun k j => (c k j).val
  let S := ∑ k : Fin N, ∑ j, cZ k j • modularPolynomialLift (g k.val j)
  have hS : map π S = ∑ k : Fin N, ∑ j, c k j • g k.val j := by
    simp only [S, cZ, smul_eq_C_mul, map_sum, map_mul, map_C, map_modularPolynomialLift,
      π, Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]
  let D := u - S - f * modularPolynomialLift h - modularPolynomialLift v
  have hlift (q : MvPolynomial (Fin 2) (ZMod p)) : map π (modularPolynomialLift q) = q :=
    map_modularPolynomialLift q
  have hD : map π D = 0 := by
    simp only [D, map_sub, map_mul, hlift, hS]
    linear_combination -he
  obtain ⟨w, hw⟩ := (map_mod_prime_eq_zero_iff p D).mp hD
  refine ⟨cZ, modularPolynomialLift h, modularPolynomialLift v, w,
    modularPolynomialLift_mem_origin_power v hv, ?_⟩
  change u - S = _
  dsimp only [D] at hw
  linear_combination hw

end
end AffineCurveCounting
