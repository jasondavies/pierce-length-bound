module

public import AffineCurveCounting.Interpolation

/-!
# Vanishing transfers from independent rows to their span

The determinant argument selects independent evaluation rows. This module justifies why a
coefficient vector annihilating those rows vanishes on every point whose row they span.
-/

@[expose] public section

namespace AffineCurveCounting

open Matrix

theorem dotProduct_eq_zero_of_mem_span {s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℚ) (v : Fin N → ℚ) (hAv : A *ᵥ v = 0)
    {r : Fin N → ℚ} (hr : r ∈ Submodule.span ℚ (Set.range A.row)) : r ⬝ᵥ v = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨i, rfl⟩ := hr
    exact congrFun hAv i
  | zero => simp
  | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
  | smul a x hx ih => simp [smul_dotProduct, ih]

theorem integer_dotProduct_eq_zero_of_mem_span {s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℤ) (v : Fin N → ℤ) (hAv : A *ᵥ v = 0)
    {r : Fin N → ℤ}
    (hr : (fun j => (r j : ℚ)) ∈ Submodule.span ℚ (Set.range (A.map ((↑) : ℤ → ℚ)).row)) :
    r ⬝ᵥ v = 0 := by
  have hAvQ : A.map ((↑) : ℤ → ℚ) *ᵥ (fun j => (v j : ℚ)) = 0 := by
    ext i
    have hi := congrFun hAv i
    change ∑ j, (A i j : ℚ) * (v j : ℚ) = 0
    exact_mod_cast hi
  have h := dotProduct_eq_zero_of_mem_span _ _ hAvQ hr
  simp only [dotProduct] at h ⊢
  exact_mod_cast h

theorem vanishes_of_evaluation_row_mem_span {n N s : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → (Fin n → ℤ))
    (v : Fin N → ℤ) (hAv : evaluationMatrix mon points *ᵥ v = 0)
    (x : Fin n → ℤ)
    (hx : (fun j => (((mon j).prod (fun k e => x k ^ e) : ℤ) : ℚ)) ∈
      Submodule.span ℚ (Set.range ((evaluationMatrix mon points).map ((↑) : ℤ → ℚ)).row)) :
    MvPolynomial.eval x (polynomialOfCoefficients mon v) = 0 := by
  have h := integer_dotProduct_eq_zero_of_mem_span _ _ hAv hx
  simpa [polynomialOfCoefficients, MvPolynomial.eval_monomial, dotProduct, mul_comm] using h

end AffineCurveCounting
