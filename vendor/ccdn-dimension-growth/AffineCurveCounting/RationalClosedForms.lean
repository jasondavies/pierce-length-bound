module

public import AffineCurveCounting.DifferentialResidue

/-! Degree-bounded closed rational forms for irreducible monic polynomials
over a rational function field with algebraically closed constant field. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Differential
open scoped Differential
attribute [local instance] rationalDifferential

/-- The closed-form solution space for a monic irreducible f over F(t) is
spanned over F by (∂f/∂x, ∂f/∂t), under strict x-degree bounds.
All differential-field and residue inputs are constructed here. -/
theorem rational_closed_form_eq_gradient
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f p q : (RatFunc F)[X]) (hf : Irreducible f) (hm : f.Monic)
    (hpdeg : p.degree < f.degree) (hqdeg : q.degree < f.degree)
    (hclosed : Differential.mapCoeffs p * f - p * Differential.mapCoeffs f =
      q.derivative * f - q * f.derivative) :
    ∃ a : F, p = C (algebraMap F (RatFunc F) a) * f.derivative ∧
      q = C (algebraMap F (RatFunc F) a) * Differential.mapCoeffs f := by
  let : Fact (Irreducible f) := ⟨hf⟩
  let : Fact f.Monic := ⟨hm⟩
  let : Module.Finite (RatFunc F) (AdjoinRoot f) := hm.finite_adjoinRoot
  have : Differential.ContainConstants F (AdjoinRoot f) :=
    rational_algebraic_differential_constants (F := F) (L := AdjoinRoot f) inferInstance
  have hc : aeval (AdjoinRoot.root f) f = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hs : aeval (AdjoinRoot.root f) f.derivative ≠ 0 :=
    hf.separable.aeval_derivative_ne_zero hc
  exact closed_form_eq_constant_gradient f p q hf hm (AdjoinRoot.root f) hc hs hpdeg hqdeg hclosed

end
end AffineCurveCounting
