module

public import AffineCurveCounting.PlaneBadPrimes
public import AffineCurveCounting.SingularDeterminantCutoff
import all ArithmeticHeights.BombieriVaaler

/-! The determinant lower bound with the bad-prime input discharged by the
actual coefficient-controlled witness. The sharp finite-field point estimate
remains explicit and is not asserted as a theorem here. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Finset MvPolynomial Real

def heightDeterminantError (C : ℝ) : ℝ :=
  degreeFourDeterminantError C + Real.log 7 + 2 * mertensError + 1

/-- The excluded-prime set and its charge are derived from the actual absolute
irreducibility and coefficient-height hypotheses. The only remaining local
arithmetic estimate is the stated sharp finite-field point bound. -/
theorem singular_determinant_log_lower_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    {s N : ℕ} (hs : 0 < s) (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ H)
    (g : Fin N → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) f) →
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log f.totalDegree -
      Real.log (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) - heightDeterminantError C) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k))) := by
  obtain ⟨B, hmem, hcharge⟩ := exists_plane_bad_prime_set f hd hir H hH hcoeff
  have hred (p : ℕ) (hp : p ∈ ((Ioc 0 s).filter Nat.Prime) \ B)
      (hlo : 27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ)) :
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
    have hpp := (mem_filter.mp (mem_sdiff.mp hp).1).2
    let : Fact p.Prime := ⟨hpp⟩
    apply irreducible_reduction_of_not_planeBadReduction f p
    intro hbad
    exact (mem_sdiff.mp hp).2 ((hmem p).mpr ⟨hlo, hbad⟩)
  have hupper (p : ℕ) (hp : p ∈ ((Ioc 0 s).filter Nat.Prime) \ B)
      (hlo : 27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ)) :
      (Nat.card (PlaneResidue f p) : ℝ) ≤ p + C * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p :=
    hcount p (mem_filter.mp (mem_sdiff.mp hp).1).2 hlo (hred p hp hlo)
  have hlower := singular_determinant_log_lower_at_rank hs f hd g z hz hrows hC B hred hupper
  have hh := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
  dsimp only [heightDeterminantError]
  nlinarith

end
end AffineCurveCounting
