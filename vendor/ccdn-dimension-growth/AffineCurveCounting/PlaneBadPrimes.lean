module

public import AffineCurveCounting.GeneralBadReduction
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Data.Nat.PrimeFin

/-! Actual finite bad-prime sets for plane equations, with coefficient-height
charge bounds and irreducible good reductions. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Real

lemma mvPolynomial_irreducible_of_field_map
    {F K σ : Type*} [Field F] [Field K] (φ : F →+* K)
    (f : MvPolynomial σ F) (hf : Irreducible (MvPolynomial.map φ f)) : Irreducible f := by
  have hunit (q : MvPolynomial σ F) (hq : IsUnit (MvPolynomial.map φ q)) : IsUnit q := by
    obtain ⟨hc, hd⟩ := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hq
    have he : (MvPolynomial.map φ q).totalDegree = q.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [MvPolynomial.support_map_of_injective _ φ.injective]
    apply MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr
    refine ⟨isUnit_iff_ne_zero.mpr ?_, he ▸ hd⟩
    intro hz
    apply hc.ne_zero
    rw [MvPolynomial.coeff_map, hz, map_zero]
  refine ⟨fun h => hf.not_isUnit (h.map (MvPolynomial.map φ)), ?_⟩
  intro g h he
  have hh := hf.isUnit_or_isUnit (by rw [he, map_mul])
  exact hh.imp (hunit g) (hunit h)

lemma bivariateTotalDegree_equiv {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 2) R) :
    bivariateTotalDegree (bivariatePolynomialEquiv R f) = f.totalDegree := by
  simp only [bivariateTotalDegree, AlgEquiv.symm_apply_apply]

/-- Bad reduction for the actual multivariate plane equation. -/
def PlaneBadReduction (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) : Prop :=
  BivariateBadReduction (bivariatePolynomialEquiv ℤ f) f.totalDegree p

lemma not_planeBadReduction_iff (f : MvPolynomial (Fin 2) ℤ)
    (p : ℕ) [Fact p.Prime] :
    ¬PlaneBadReduction f p ↔
      (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree = f.totalDegree ∧
      Irreducible (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) := by
  let K := AlgebraicClosure (ZMod p)
  have hbad : PlaneBadReduction f p ↔
      (MvPolynomial.map (Int.castRingHom K) f).totalDegree ≠ f.totalDegree ∨
        ¬Irreducible (MvPolynomial.map (Int.castRingHom K) f) := by
    constructor
    · rintro ⟨hp, hh⟩
      change bivariateTotalDegree (bivariateMap (Int.castRingHom K) (bivariatePolynomialEquiv ℤ f)) ≠
        f.totalDegree ∨ ¬Irreducible (bivariateMap (Int.castRingHom K) (bivariatePolynomialEquiv ℤ f)) at hh
      rw [bivariatePolynomialEquiv_map, bivariateTotalDegree_equiv,
        MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv K)] at hh
      exact hh
    · intro hh
      refine ⟨Fact.out, ?_⟩
      change bivariateTotalDegree (bivariateMap (Int.castRingHom K) (bivariatePolynomialEquiv ℤ f)) ≠
        f.totalDegree ∨ ¬Irreducible (bivariateMap (Int.castRingHom K) (bivariatePolynomialEquiv ℤ f))
      rw [bivariatePolynomialEquiv_map, bivariateTotalDegree_equiv,
        MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv K)]
      exact hh
  rw [hbad]
  simp only [not_or, not_not, K]

/-- Geometric irreducibility implies the irreducibility over the prime field
needed by the singular determinant estimate. -/
lemma irreducible_reduction_of_not_planeBadReduction
    (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) [Fact p.Prime]
    (hf : ¬PlaneBadReduction f p) :
    Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
  have h := ((not_planeBadReduction_iff f p).mp hf).2
  apply mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
  have he : (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom (AlgebraicClosure (ZMod p)) := by ext; simp
  simpa only [MvPolynomial.map_map, he] using h

/-- The complete set of bad primes above 27*d^4 is finite and has the
required charge bound. Good reductions outside this set are actual
irreducible reductions, not an additional input. -/
theorem exists_plane_bad_prime_set
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f : MvPolynomial (Fin 2) ℤ) (hd : 0 < f.totalDegree)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ H) :
    ∃ B : Finset ℕ,
      (∀ p, p ∈ B ↔ 27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) ∧ PlaneBadReduction f p) ∧
      (∑ p ∈ B, Real.log p / p) ≤
        Real.log (1 + Real.log H / (f.totalDegree : ℝ) ^ 2) + Real.log 7 + 2 * mertensError + 1 := by
  classical
  let q := bivariatePolynomialEquiv ℤ f
  have hqdeg : bivariateTotalDegree q = f.totalDegree := bivariateTotalDegree_equiv f
  have hqir : Irreducible (bivariateMap (Int.castRingHom F) q) := by
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)]
    exact hir
  have hqcoeff : BivariateCoefficientBound q H := by
    intro i j
    rw [bivariatePolynomialEquiv_coeff]
    exact hcoeff _
  obtain ⟨D, hD, _, hdiv⟩ := exists_plane_bad_prime_witness f.totalDegree hd q hqdeg hqir H hH hqcoeff
  let B := D.natAbs.primeFactors.filter
    (fun p : ℕ => 27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) ∧ PlaneBadReduction f p)
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hcut : (f.totalDegree : ℝ) ≤ 27 * (f.totalDegree : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
  have hmem (p : ℕ) : p ∈ B ↔
      27 * (f.totalDegree : ℝ) ^ 4 < (p : ℝ) ∧ PlaneBadReduction f p := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro hp
      apply Finset.mem_filter.mpr
      refine ⟨?_, hp⟩
      apply Nat.mem_primeFactors.mpr
      refine ⟨hp.2.choose, ?_, Int.natAbs_ne_zero.mpr hD.ne'⟩
      have hz := hdiv p (by exact_mod_cast hcut.trans_lt hp.1) hp.2
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hz
  refine ⟨B, hmem, ?_⟩
  exact plane_geometric_bad_prime_charge f.totalDegree hd q hqdeg hqir H hH hqcoeff B
    (fun p hp => ((hmem p).mp hp).2) (fun p hp => ((hmem p).mp hp).1)

end
end AffineCurveCounting
