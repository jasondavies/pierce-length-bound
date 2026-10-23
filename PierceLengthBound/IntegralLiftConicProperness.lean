/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftPolynomialQuotient
public import PierceLengthBound.IntegralLiftRawResolvent

/-! Properness of the integral lift on a nonexceptional conic (the properness part of
Lemma A.2, `lem:jointconicproper`). Along a quadratic parametrization `z` with polynomial
quotient `q`, the raw resolvent formula gives the lift as `F / V` with `deg F = 9` and
`deg V = 12`, once the resolvent cut vanishes; it vanishes when more than `492` orbit states of
the same `θ` lie on the conic. Hence the reduced denominator of the lift has degree three more
than its numerator, and at most twelve. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- `ρ_V - 1 - z₀ - z₁ - z₂`; at the free nodes it is the `X³` coefficient of the orbit Newton
quartic. -/
def orbitResolventP3 (a b i : ℕ) (z : Fin 3 → Polynomial ℚ) : Polynomial ℚ :=
  C (patternVQ a b i - 1) - z 0 - z 1 - z 2

/-- The resolvent numerator `a ((q - P₃) H₃(k) - H_mixed(k))` in the parametrized gaps `k`. -/
def orbitResolventNumerator (a b i : ℕ) (z : Fin 3 → Polynomial ℚ)
    (q : Polynomial ℚ) : Polynomial ℚ :=
  let k := orbitParameterGaps a b i z
  C (a : ℚ) * ((q - orbitResolventP3 a b i z) * rawHankelThree (k 0) (k 1) (k 2) -
    rawHankelMixed (k 0) (k 1) (k 2) (k 3))

/-- The resolvent denominator: the quartic `parabolaV` at the shifted quotients, which is the
orbit Newton quartic evaluated at `-q`. -/
def orbitResolventDenominator (a b i : ℕ) (z : Fin 3 → Polynomial ℚ)
    (q : Polynomial ℚ) : Polynomial ℚ :=
  parabolaV (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) j.castSucc)
    (fun j => q + (![0, z 0, z 1, z 2] : Fin 4 → Polynomial ℚ) j)

/-- The resolvent cut `N V - F D`, comparing the lift quotient `N / D` with the resolvent
quotient `F / V` along the parametrization. -/
def orbitResolventCut (a b i : ℕ) (z : Fin 3 → Polynomial ℚ)
    (q : Polynomial ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval z (orbitLiftNumeratorQ a b i) * orbitResolventDenominator a b i z q -
    orbitResolventNumerator a b i z q * MvPolynomial.aeval z (orbitLiftDenominatorQ a b i)

lemma orbitResolventP3_degree (a b i : ℕ) (z : Fin 3 → Polynomial ℚ)
    (hz : ∀ j, (z j).natDegree ≤ 2) : (orbitResolventP3 a b i z).natDegree ≤ 2 := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  unfold orbitResolventP3
  compute_degree
  omega

lemma orbitResolventP3_eval {a b i : ℕ} (z : Fin 3 → Polynomial ℚ) (t : ℚ)
    (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b i j) :
    (orbitResolventP3 a b i z).eval t = (orbitNewtonQuarticQ a b i).coeff 3 := by
  simp [orbitResolventP3, hz, orbitNewtonQuarticQ, firstNewtonQuartic_eq,
    monicQuartic_coeff, firstNewtonCoeffs, coeffs]
  ring

lemma orbitResolventDenominator_eval {a b i : ℕ} (z : Fin 3 → Polynomial ℚ)
    (q : Polynomial ℚ) (t : ℚ) (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b i j)
    (hq : q.eval t = (qq a b i : ℚ)) :
    (orbitResolventDenominator a b i z q).eval t =
      (orbitNewtonQuarticQ a b i).eval (-(qq a b i : ℚ)) := by
  simp [orbitResolventDenominator, parabolaV, orbitNewtonQuarticQ, firstNewtonQuartic,
    hz, hq]
  ring

lemma orbitResolventNumerator_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (z : Fin 3 → Polynomial ℚ) (q : Polynomial ℚ) (t : ℚ)
    (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b i j) (hq : q.eval t = (qq a b i : ℚ)) :
    (orbitResolventNumerator a b i z q).eval t =
      (a : ℚ) * (((qq a b i : ℚ) - (orbitNewtonQuarticQ a b i).coeff 3) *
        rawHankelThree (kq a b i : ℚ) (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ) -
        rawHankelMixed (kq a b i : ℚ) (kq a b (i + 1) : ℚ)
          (kq a b (i + 2) : ℚ) (kq a b (i + 3) : ℚ)) := by
  have hk := orbitParameterGaps_eval hba hi z t hz
  simp [orbitResolventNumerator, rawHankelThree, rawHankelMixed, hk, hq,
    orbitResolventP3_eval z t hz]

/-- At the parameter of an orbit state, `I₃ · V = F` (the raw resolvent formula). -/
lemma orbitResolvent_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (z : Fin 3 → Polynomial ℚ) (q : Polynomial ℚ) (t : ℚ)
    (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b i j) (hq : q.eval t = (qq a b i : ℚ)) :
    (integralLiftCoordinate a b i : ℚ) * (orbitResolventDenominator a b i z q).eval t =
      (orbitResolventNumerator a b i z q).eval t := by
  rw [orbitResolventDenominator_eval z q t hz hq, orbitResolventNumerator_eval hba hi z q t hz hq]
  exact orbit_integralLift_raw_resolvent_Q hba hi

/-- The resolvent cut vanishes at the parameter of every orbit state on the conic. -/
lemma orbitResolventCut_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (z : Fin 3 → Polynomial ℚ) (q : Polynomial ℚ) (t : ℚ)
    (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b i j) (hq : q.eval t = (qq a b i : ℚ)) :
    (orbitResolventCut a b i z q).eval t = 0 := by
  have he (f : MvPolynomial (Fin 3) ℚ) :
      (MvPolynomial.aeval z f).eval t = MvPolynomial.eval (orbitFreeNodesQ a b i) f := by
    rw [polynomial_substitution_eval,
      show (fun j => (z j).eval t) = orbitFreeNodesQ a b i from funext hz]
  have hI := orbitLift_evaluation hba hi
  have hr := orbitResolvent_eval hba hi z q t hz hq
  have hn := (eq_div_iff hI.1).mp hI.2
  simp only [orbitResolventCut, eval_sub, eval_mul, he]
  rw [← hn, ← hr]
  ring

lemma orbitQuotient_polynomials_congr {a b i l : ℕ} (h : theta a b i = theta a b l) :
    orbitQuotientNumeratorQ a b i = orbitQuotientNumeratorQ a b l ∧
    orbitQuotientDenominatorQ a b i = orbitQuotientDenominatorQ a b l := by
  obtain ⟨_, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitQuotientNumeratorQ, orbitQuotientDenominatorQ, orbitCurveCofactorsQ,
    hρ, hu, hv, hρ', hu', hv', and_self]

lemma orbitResolventCut_congr {a b i l : ℕ} (h : theta a b i = theta a b l)
    (z : Fin 3 → Polynomial ℚ) (q : Polynomial ℚ) :
    orbitResolventCut a b i z q = orbitResolventCut a b l z q := by
  obtain ⟨_, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitResolventCut, orbitLiftNumeratorQ, orbitLiftDenominatorQ,
    orbitCurveCofactorsQ, orbitResolventNumerator, orbitResolventDenominator, orbitResolventP3,
    orbitParameterGaps, hρ, hu, hv, hρ', hu', hv']

lemma polynomial_quotient_eval_state {a b i l : ℕ} (hba : b < a) (hi : l + 7 < P a b)
    (hθ : theta a b i = theta a b l) (z : Fin 3 → Polynomial ℚ) (q : Polynomial ℚ) (t : ℚ)
    (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b l j)
    (hq : q * MvPolynomial.aeval z (orbitQuotientDenominatorQ a b i) =
      MvPolynomial.aeval z (orbitQuotientNumeratorQ a b i)) : q.eval t = (qq a b l : ℚ) := by
  obtain ⟨hn, hd⟩ := orbitQuotient_polynomials_congr hθ
  have h := congrArg (Polynomial.eval t) hq
  simp only [eval_mul, polynomial_substitution_eval, hn, hd,
    show (fun j => (z j).eval t) = orbitFreeNodesQ a b l from funext hz] at h
  have he := orbitQuotient_evaluation hba hi
  rw [he.2]
  exact (eq_div_iff he.1).mpr h

/-- Along a quadratic parametrization with `deg F = 9` and `deg V = 12`, the resolvent cut has
degree at most `492`. -/
lemma orbitResolventCut_degree (a b i : ℕ) (z : Fin 3 → Polynomial ℚ)
    (hz : ∀ j, (z j).natDegree ≤ 2) (q : Polynomial ℚ)
    (hF : (orbitResolventNumerator a b i z q).natDegree = 9)
    (hV : (orbitResolventDenominator a b i z q).natDegree = 12) :
    (orbitResolventCut a b i z q).natDegree ≤ 492 := by
  have hn := (polynomial_substitution_degree z hz (orbitLiftNumeratorQ a b i)).trans
    (Nat.mul_le_mul_left 2 (orbitLift_polynomial_degrees a b i).1)
  have hd := (polynomial_substitution_degree z hz (orbitLiftDenominatorQ a b i)).trans
    (Nat.mul_le_mul_left 2 (orbitLift_polynomial_degrees a b i).2)
  unfold orbitResolventCut
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by omega)
  · exact natDegree_mul_le.trans (by omega)

/-- The resolvent cut is identically zero when it vanishes at more than `492` distinct
parameters of orbit states with the same `θ`. -/
lemma orbitResolventCut_zero_of_many_states {a b i : ℕ} (hba : b < a)
    (z : Fin 3 → Polynomial ℚ) (hz : ∀ j, (z j).natDegree ≤ 2) (q : Polynomial ℚ)
    (hF : (orbitResolventNumerator a b i z q).natDegree = 9)
    (hV : (orbitResolventDenominator a b i z q).natDegree = 12)
    (hq : q * MvPolynomial.aeval z (orbitQuotientDenominatorQ a b i) =
      MvPolynomial.aeval z (orbitQuotientNumeratorQ a b i))
    {ι : Type*} [Fintype ι] (l : ι → ℕ) (t : ι → ℚ) (ht : Function.Injective t)
    (hi : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hp : ∀ j k, (z k).eval (t j) = orbitFreeNodesQ a b (l j) k)
    (hcard : 492 < Fintype.card ι) : orbitResolventCut a b i z q = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht
  · intro j
    rw [orbitResolventCut_congr (hθ j)]
    exact orbitResolventCut_eval hba (hi j) z q (t j) (hp j)
      (polynomial_quotient_eval_state hba (hi j) (hθ j) z q (t j) (hp j) hq)
  · exact (orbitResolventCut_degree a b i z hz q hF hV).trans_lt hcard

/-- The rational lift along a parametrization `z`: the universal lift numerator over the lift
denominator, both evaluated at `z`. -/
def orbitLiftParameter (a b i : ℕ) (z : Fin 3 → Polynomial ℚ) : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (MvPolynomial.aeval z (orbitLiftNumeratorQ a b i)) /
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (MvPolynomial.aeval z (orbitLiftDenominatorQ a b i))

/-- On a quadratically parametrized nonexceptional conic through the free nodes at `i` and
those of more than `492` orbit states with the same `θ`, at distinct parameters, the lift is
strictly proper: its reduced denominator has degree three more than its reduced numerator,
positive and at most twelve. -/
theorem orbit_conic_integralLift_proper {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (z : Fin 3 → Polynomial ℚ) (hz : ∀ j, (z j).natDegree ≤ 2)
    (hfirst : (z 0).coeff 2 ≠ 0)
    (hquad : MvPolynomial.aeval z (orbitCurveQuadraticQ a b i) = 0)
    (hcurve : MvPolynomial.aeval z (orbitCurveEquationQ a b i) = 0)
    (t0 : ℚ) (hz0 : ∀ j, (z j).eval t0 = orbitFreeNodesQ a b i j)
    {ι : Type*} [Fintype ι] (l : ι → ℕ) (t : ι → ℚ) (ht : Function.Injective t)
    (hl : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hp : ∀ j k, (z k).eval (t j) = orbitFreeNodesQ a b (l j) k)
    (hcard : 492 < Fintype.card ι) :
    (orbitLiftParameter a b i z).num.natDegree + 3 =
        (orbitLiftParameter a b i z).denom.natDegree ∧
      0 < (orbitLiftParameter a b i z).denom.natDegree ∧
      (orbitLiftParameter a b i z).denom.natDegree ≤ 12 := by
  obtain ⟨q, hq3, hq, hV⟩ := orbit_conic_quotient_cubic hba hi hne z hz hfirst hquad hcurve
    t0 hz0 l t ht hl hθ hp (by omega)
  let k := orbitParameterGaps a b i z
  obtain ⟨hρ, hu, hv, hneq, ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  have hraw := quadratic_parameter_raw_degrees hρ hu hv hneq
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a ha z hz hfirst hquad hcurve
  have hF : (orbitResolventNumerator a b i z q).natDegree = 9 := by
    have hinner := integralLift_parabola_numerator_degree q (orbitResolventP3 a b i z)
      (rawHankelThree (k 0) (k 1) (k 2)) (rawHankelMixed (k 0) (k 1) (k 2) (k 3))
      hq3 (orbitResolventP3_degree a b i z hz) hraw.1 hraw.2.2
    exact (natDegree_C_mul ha).trans hinner
  have hcut := orbitResolventCut_zero_of_many_states hba z hz q hF hV hq l t ht hl hθ hp hcard
  let N := MvPolynomial.aeval z (orbitLiftNumeratorQ a b i)
  let D := MvPolynomial.aeval z (orbitLiftDenominatorQ a b i)
  let F := orbitResolventNumerator a b i z q
  let V := orbitResolventDenominator a b i z q
  have hD : D ≠ 0 := by
    intro hd
    have he : D.eval t0 = MvPolynomial.eval (orbitFreeNodesQ a b i)
        (orbitLiftDenominatorQ a b i) := by
      dsimp only [D]
      rw [polynomial_substitution_eval,
        show (fun j => (z j).eval t0) = orbitFreeNodesQ a b i from funext hz0]
    rw [hd, eval_zero] at he
    exact (orbitLift_evaluation hba hi).1 he.symm
  have hVdegree : V.natDegree = 12 := hV
  have hV0 : V ≠ 0 := ne_zero_of_natDegree_gt (show 0 < V.natDegree by omega)
  let f := algebraMap (Polynomial ℚ) (RatFunc ℚ)
  have hf := IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)
  have hDf : f D ≠ 0 := by simpa only [map_zero] using hf.ne hD
  have hVf : f V ≠ 0 := by simpa only [map_zero] using hf.ne hV0
  have he : orbitLiftParameter a b i z = f F / f V := by
    change f N / f D = f F / f V
    apply (div_eq_div_iff hDf hVf).mpr
    have hid : N * V = F * D := sub_eq_zero.mp hcut
    simpa only [map_mul] using congrArg f hid
  rw [he]
  have hp := proper_remainder_denominator hF hV
  refine ⟨hp.1, hp.2, ?_⟩
  exact (natDegree_le_of_dvd (RatFunc.denom_div_dvd F V) hV0).trans_eq hVdegree

end
end PierceLengthBound.FixedDividend
