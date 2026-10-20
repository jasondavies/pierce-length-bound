module

public import AffineCurveCounting.PrimitiveNormalization
public import AffineCurveCounting.PlaneChartDeterminant

/-! Restriction to x₀=1 is injective on forms of a fixed homogeneous degree.
Explicit homogenization supplies its inverse on bounded-degree polynomials. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def affineChart {K : Type*} [CommRing K] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K :=
  eval₂Hom C (Fin.cons 1 X)

def chartExponent {n : ℕ} (m : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i.succ)

@[simp] lemma chartExponent_apply {n : ℕ} (m : Fin (n + 1) →₀ ℕ) (i : Fin n) :
    chartExponent m i = m i.succ := rfl

lemma exponent_degree_split {n : ℕ} (m : Fin (n + 1) →₀ ℕ) :
    m.sum (fun _ e => e) = m 0 + (chartExponent m).sum (fun _ e => e) := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ,
    Finsupp.sum_fintype _ _ (by simp)]
  rfl

lemma chartExponent_injective_on_degree {n M : ℕ} {m k : Fin (n + 1) →₀ ℕ}
    (hm : m.sum (fun _ e => e) = M) (hk : k.sum (fun _ e => e) = M)
    (he : chartExponent m = chartExponent k) : m = k := by
  have h0 : m 0 = k 0 := by
    rw [exponent_degree_split] at hm hk
    rw [he] at hm
    omega
  ext i
  refine Fin.cases h0 (fun j => ?_) i
  exact congrArg (fun t => t j) he

lemma affineChart_monomial {K : Type*} [CommRing K] {n : ℕ}
    (m : Fin (n + 1) →₀ ℕ) (c : K) :
    affineChart n (monomial m c) = monomial (chartExponent m) c := by
  change eval₂ C (Fin.cons 1 X) (monomial m c) = _
  rw [eval₂_monomial, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp

lemma affineChart_homogeneous_coefficient {K : Type*} [CommRing K] {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M)
    (j : Fin ((n + M).choose M)) :
    (affineChart n f).coeff (chartExponent (homogeneousMonomials n M j)) =
      f.coeff (homogeneousMonomials n M j) := by
  classical
  have hinj : Function.Injective (fun j => chartExponent (homogeneousMonomials n M j)) := by
    intro j k he
    apply homogeneousMonomials_injective n M
    exact chartExponent_injective_on_degree (homogeneousMonomials_degree n M j)
      (homogeneousMonomials_degree n M k) he
  conv_lhs => rw [homogeneous_eq_sum_coeff f hf]
  simp [map_sum, affineChart_monomial, coeff_monomial, hinj.eq_iff]

lemma affineChart_injective_on_homogeneous {K : Type*} [CommRing K] {n M : ℕ}
    {f g : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous M) (hg : g.IsHomogeneous M)
    (he : affineChart n f = affineChart n g) : f = g := by
  have hc : ∀ j, f.coeff (homogeneousMonomials n M j) = g.coeff (homogeneousMonomials n M j) := by
    intro j
    rw [← affineChart_homogeneous_coefficient f hf j,
      ← affineChart_homogeneous_coefficient g hg j, he]
  rw [homogeneous_eq_sum_coeff f hf, homogeneous_eq_sum_coeff g hg]
  simp only [hc]

lemma affineChart_totalDegree_le {K : Type*} [CommRing K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) : (affineChart n f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [affineChart_monomial]
  have h := le_totalDegree hm
  rw [exponent_degree_split] at h
  apply (totalDegree_monomial_le _ _).trans
  change (chartExponent m).sum (fun _ e => e) ≤ f.totalDegree
  omega

def homogenizedExponent {n : ℕ} (M : ℕ) (m : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons (M - m.sum (fun _ e => e)) m)

@[simp] lemma chartExponent_homogenizedExponent {n : ℕ} (M : ℕ) (m : Fin n →₀ ℕ) :
    chartExponent (homogenizedExponent M m) = m := by
  ext i
  rfl

lemma homogenizedExponent_degree {n M : ℕ} (m : Fin n →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ M) :
    (homogenizedExponent M m).sum (fun _ e => e) = M := by
  rw [exponent_degree_split, chartExponent_homogenizedExponent]
  change M - m.sum (fun _ e => e) + m.sum (fun _ e => e) = M
  omega

def boundedHomogenize {K : Type*} [CommRing K] {n : ℕ} (M : ℕ) (f : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin (n + 1)) K :=
  ∑ m ∈ f.support, monomial (homogenizedExponent M m) (f.coeff m)

lemma affineChart_boundedHomogenize {K : Type*} [CommRing K] {n : ℕ}
    (M : ℕ) (f : MvPolynomial (Fin n) K) : affineChart n (boundedHomogenize M f) = f := by
  classical
  simp only [boundedHomogenize, map_sum, affineChart_monomial, chartExponent_homogenizedExponent]
  exact f.as_sum.symm

lemma boundedHomogenize_homogeneous {K : Type*} [CommRing K] {n M : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ M) :
    (boundedHomogenize M f).IsHomogeneous M := by
  apply IsHomogeneous.sum
  intro m hm
  exact isHomogeneous_monomial _ (homogenizedExponent_degree m ((le_totalDegree hm).trans hf))

lemma affineChart_map {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (φ : K →+* L) (f : MvPolynomial (Fin (n + 1)) K) :
    affineChart n (MvPolynomial.map φ f) = MvPolynomial.map φ (affineChart n f) := by
  have he : (affineChart n).comp (MvPolynomial.map φ) =
      (MvPolynomial.map φ).comp (affineChart n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineChart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [affineChart]
  exact RingHom.congr_fun he f

lemma affineChart_eval {K : Type*} [CommRing K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (x : Fin n → K) :
    eval x (affineChart n f) = eval (Fin.cons 1 x) f := by
  change eval x (eval₂ C (Fin.cons 1 X) f) = _
  rw [← eval_assoc]
  have he : (eval x) ∘ Fin.cons (1 : MvPolynomial (Fin n) K) X = Fin.cons 1 x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [he]

/-- Divisibility of affine charts lifts to homogeneous divisibility when the
first equation retains its degree on the chart. -/
theorem homogeneous_dvd_of_affineChart_dvd {K : Type*} [CommRing K] [IsDomain K]
    {n d M : ℕ} {f g : MvPolynomial (Fin (n + 1)) K}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg : g.IsHomogeneous M)
    (hdchart : (affineChart n f).totalDegree = d)
    (hdiv : affineChart n f ∣ affineChart n g) : f ∣ g := by
  have hcf : affineChart n f ≠ 0 := by
    intro hz
    exact hf0 (affineChart_injective_on_homogeneous hf (isHomogeneous_zero _ _ d)
      (by simpa only [map_zero] using hz))
  by_cases hcg : affineChart n g = 0
  · have hg0 := affineChart_injective_on_homogeneous hg (isHomogeneous_zero _ _ M)
      (by simpa only [map_zero] using hcg)
    rw [hg0]
    exact dvd_zero f
  obtain ⟨q, hq⟩ := hdiv
  have hq0 : q ≠ 0 := by intro hz; apply hcg; rw [hq, hz, mul_zero]
  have hdeg : d + q.totalDegree ≤ M := by
    have hh := (affineChart_totalDegree_le g).trans hg.totalDegree_le
    rw [hq, totalDegree_mul_of_isDomain hcf hq0, hdchart] at hh
    exact hh
  have hdM : d ≤ M := by omega
  refine ⟨boundedHomogenize (M - d) q, ?_⟩
  apply affineChart_injective_on_homogeneous hg
  · simpa only [Nat.add_sub_of_le hdM] using
      hf.mul (boundedHomogenize_homogeneous q (show q.totalDegree ≤ M - d by omega))
  · rw [map_mul, affineChart_boundedHomogenize]
    exact hq

/-- Primitive integral homogeneous nonmultiples give proper rational affine
sections. This discharges the coefficient and chart nondivisibility transfers. -/
theorem rational_affineChart_not_dvd {n d M : ℕ} {f g : MvPolynomial (Fin (n + 1)) ℤ}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg : g.IsHomogeneous M)
    (hprim : PrimitiveIntegerPolynomial f) (hdchart : (affineChart n f).totalDegree = d)
    (hnd : ¬ f ∣ g) :
    ¬ MvPolynomial.map (Int.castRingHom ℚ) (affineChart n f) ∣
      MvPolynomial.map (Int.castRingHom ℚ) (affineChart n g) := by
  intro hdiv
  rw [← affineChart_map, ← affineChart_map] at hdiv
  apply hnd
  apply hprim.rational_map_dvd_iff.mp
  apply homogeneous_dvd_of_affineChart_dvd (hf.map _) ?_ (hg.map _) ?_ hdiv
  · exact fun he => hf0 ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa using he))
  · rw [affineChart_map]
    have he : (MvPolynomial.map (Int.castRingHom ℚ) (affineChart n f)).totalDegree =
        (affineChart n f).totalDegree := by
      unfold totalDegree
      rw [support_map_of_injective _ Int.cast_injective]
    exact he.trans hdchart

end
end AffineCurveCounting
