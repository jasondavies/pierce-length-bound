module

public import AffineCurveCounting.SmoothReduction
public import AffineCurveCounting.PrimeSums
import all ArithmeticHeights.BombieriVaaler

/-! The global determinant estimate for points with smooth reduction at the
selected primes. Finite-field point counts and the excluded-prime set remain
explicit geometric inputs. Local divisibility is proved, not assumed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Finset Real

/-- Global logarithmic bound for the gcd of the maximal evaluation minors at
smooth reductions. The number of residue classes is the actual number of
smooth points of the reduced equation. -/
theorem smooth_determinant_log_lower {s N : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (hf : ∀ i, MvPolynomial.eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i k => MvPolynomial.eval (z i) (g k)).map ((↑) : ℤ → ℚ)).row)
    {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) (B : Finset ℕ)
    (hsmooth : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, ∀ i,
      ∃ j, (MvPolynomial.eval (z i) (MvPolynomial.pderiv j f) : ZMod p) ≠ 0)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B,
      (Nat.card (SmoothPlaneResidue f p) : ℝ) ≤ p + C * Real.sqrt p) :
    (s : ℝ)^2 / 2 * (Real.log x - mertensError -
      (∑ p ∈ B, Real.log p / p) - C * primeErrorMass) -
      s * ((Real.log 4 + 4) * x) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i k => MvPolynomial.eval (z i) (g k))) := by
  classical
  let S := ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B
  let D := Int.Matrix.minorGcd (Matrix.of fun i k => MvPolynomial.eval (z i) (g k))
  let n : ℕ → ℝ := fun p => Nat.card (SmoothPlaneResidue f p)
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := (mem_filter.mp (mem_sdiff.mp h).1).2
  have hlocal (p : ℕ) (h : p ∈ S) :
      ∃ e : ℕ, (s : ℝ)^2 / (2 * n p) - s ≤ e ∧ (p : ℤ)^e ∣ D := by
    let : Fact p.Prime := ⟨hp p h⟩
    simpa only [n, Nat.card_eq_fintype_card] using
      smooth_reduction_minorGcd hs f g z hf (hsmooth p h)
  let e : ℕ → ℕ := fun p => if h : p ∈ S then (hlocal p h).choose else 0
  have hn (p : ℕ) (h : p ∈ S) : 0 < n p := by
    let : Fact p.Prime := ⟨hp p h⟩
    have hr : Nonempty (SmoothPlaneResidue f p) := by
      refine ⟨⟨(fun k => (z ⟨0, hs⟩ k : ZMod p)), ?_, ?_⟩⟩
      · rw [← cast_plane_eval, hf]; simp
      · simpa only [← cast_plane_eval] using hsmooth p h ⟨0, hs⟩
    have hc : 0 < Fintype.card (SmoothPlaneResidue f p) := Fintype.card_pos_iff.mpr hr
    simpa only [n, Nat.card_eq_fintype_card, Nat.cast_pos] using hc
  apply determinant_log_lower_from_local_bounds hx hC B n s e
    (D := D) (lt_of_lt_of_le (by norm_num) (Int.Matrix.one_le_minorGcd hrows)) hn hupper
  · intro p h
    have heq : e p = (hlocal p h).choose := dite_eq_left h
    rw [heq]
    exact (hlocal p h).choose_spec.1
  · intro p h
    have heq : e p = (hlocal p h).choose := dite_eq_left h
    rw [heq]
    exact (hlocal p h).choose_spec.2

end
end AffineCurveCounting
