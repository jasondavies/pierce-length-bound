module

public import AffineCurveCounting.Box

/-!
# The plane-curve target

`PlaneCurveBound` records the statement proved by `planeCurveBound` in `SharpPlaneCount`.
Irreducibility is over `ℚ`, not absolute irreducibility. The one constant is uniform in the
polynomial, its degree, its coefficients, and the real radius.
-/

@[expose] public section

namespace AffineCurveCounting

def zeroLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) : Set (RatPoint n) :=
  {x | MvPolynomial.eval x f = 0}

noncomputable def curveBound (d : ℕ) (B : ℝ) : ℝ :=
  (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d)

/-- The `n = 2` case of CCDN (2020), Theorem 3, expressed using rational defining
polynomials. The proof in `SharpPlaneCount` includes denominator clearing and content removal. -/
def PlaneCurveBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : MvPolynomial (Fin 2) ℚ, Irreducible f →
    0 < f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤ C * curveBound f.totalDegree B

/-- A nonvertical rational affine line has at most one integral point for each first
coordinate. This base case does not use a curve-counting hypothesis. -/
theorem count_affineLine_le (a b c : ℚ) (hb : b ≠ 0) (B : ℝ) :
    count {x : RatPoint 2 | a * x 0 + b * x 1 = c} B ≤ (2 * ⌊B⌋ + 1).toNat := by
  let X : Set (RatPoint 2) := {x | a * x 0 + b * x 1 = c}
  have hmap : ∀ x ∈ integralPoints X B, x 0 ∈ Finset.Icc (-⌊B⌋) ⌊B⌋ := by
    intro x hx
    have hbox : x ∈ integerBox 2 B := mem_integerBox.mpr (mem_integralPoints.mp hx).1
    exact Fintype.mem_piFinset.mp hbox 0
  have hinj : Set.InjOn (fun x : IntPoint 2 => x 0) (↑(integralPoints X B)) := by
    intro x hx y hy hxy
    change x 0 = y 0 at hxy
    have hxline : a * (x 0 : ℚ) + b * (x 1 : ℚ) = c := (mem_integralPoints.mp hx).2
    have hyline : a * (y 0 : ℚ) + b * (y 1 : ℚ) = c := (mem_integralPoints.mp hy).2
    have h1 : (x 1 : ℚ) = (y 1 : ℚ) := by
      rw [hxy] at hxline
      exact mul_left_cancel₀ hb (by linarith)
    ext i
    fin_cases i
    · exact hxy
    · exact_mod_cast h1
  have h := Finset.card_le_card_of_injOn (fun x : IntPoint 2 => x 0) hmap hinj
  simpa only [count, X, Int.card_Icc, sub_neg_eq_add,
    show ⌊B⌋ + 1 + ⌊B⌋ = 2 * ⌊B⌋ + 1 by omega] using h

end AffineCurveCounting
