module

public import AffineCurveCounting.ScaledAuxiliaryCount
public import AffineCurveCounting.HomogeneousTranslation

/-! Polynomial coordinates for a translated scaled model, with exact point
transport and transport of an auxiliary nonmultiple back to the original slice. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

def scaledModelCoordinates {n : ℕ} (h : ℤ) (a : Fin n → ℤ) :
    Fin (n + 1) → MvPolynomial (Fin n) ℤ :=
  Fin.cons (C h) (fun j => X j - C (a j * h))

lemma scaledModelCoordinates_eval {n : ℕ} (h : ℤ) (a z : Fin n → ℤ) :
    (fun j => eval z (scaledModelCoordinates h a j)) =
      Fin.cons h (fun j => z j - a j * h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [scaledModelCoordinates]

lemma scaledModelCoordinates_model_eval {n : ℕ} (h : ℤ) (a z : Fin n → ℤ)
    (f : MvPolynomial (Fin n) ℤ) :
    eval (fun j => eval z (scaledModelCoordinates h a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) =
        h ^ f.totalDegree * eval z f := by
  rw [scaledModelCoordinates_eval, homogeneousTranslation_eval]
  simp only [Fin.cons_zero, Fin.cons_succ, sub_add_cancel]
  exact scaledHomogenize_eval _ _ le_rfl _

lemma scaledModelCoordinates_box {n : ℕ} {B : ℝ} {d : ℕ} {h : ℤ}
    (hB : 1 ≤ B) (hh : 0 ≤ h) (hhB : (h : ℝ) ≤ B)
    (a z : Fin n → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    (hz : ∀ j, |(z j : ℝ)| ≤ B) (j : Fin (n + 1)) :
    |(eval z (scaledModelCoordinates h a j) : ℝ)| ≤ ((d : ℝ) + 1) * B := by
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have hdR : (0 : ℝ) ≤ d := by positivity
  have he := congrFun (scaledModelCoordinates_eval h a z) j
  rw [he]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cons_zero, abs_of_nonneg hhR]
    nlinarith
  · simp only [Fin.cons_succ, Int.cast_sub, Int.cast_mul]
    have ha0 : (0 : ℝ) ≤ a k := by exact_mod_cast (ha k).1
    have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
    have hab : (a k : ℝ) * h ≤ d * B := mul_le_mul had hhB hhR hdR
    calc
      |(z k : ℝ) - (a k : ℝ) * h| ≤ |(z k : ℝ)| + |(a k : ℝ) * h| := abs_sub _ _
      _ = |(z k : ℝ)| + (a k : ℝ) * h := by rw [abs_of_nonneg (mul_nonneg ha0 hhR)]
      _ ≤ ((d : ℝ) + 1) * B := by nlinarith [hz k]

lemma scaledModelCoordinates_auxiliary_transport {n M : ℕ}
    (h : ℤ) (a : Fin n → ℤ) (f : MvPolynomial (Fin n) ℤ)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f) ∣ g) :
    ∃ g' : MvPolynomial (Fin (n + 1)) ℤ, g'.IsHomogeneous M ∧
      (∀ z, eval (Fin.cons h z) g' = eval (fun j => eval z (scaledModelCoordinates h a j)) g) ∧
      ¬ scaledHomogenize f.totalDegree h f ∣ g' := by
  refine ⟨homogeneousTranslation ℤ (-a) g, homogeneousTranslation_homogeneous _ hg, ?_, ?_⟩
  · intro z
    rw [homogeneousTranslation_eval, scaledModelCoordinates_eval]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.neg_apply, neg_mul, sub_eq_add_neg]
  · intro hdiv
    apply hnd
    have he := map_dvd (homogeneousTranslation ℤ a).toRingHom hdiv
    change homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f) ∣
      homogeneousTranslation ℤ a ((homogeneousTranslation ℤ a).symm g) at he
    simpa only [AlgEquiv.apply_symm_apply] using he

/-- A nonmultiple on the actual translated scaled model counts the original
integer points. The bound uses only the auxiliary degree and original degree. -/
theorem scaled_positioned_points_card_le {M t : ℕ}
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f))
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ (p : ℤ) ∣ f.coeff 0)
    (a : Fin 2 → ℤ) (g : MvPolynomial (Fin 3) ℤ) (hg : g.IsHomogeneous M)
    (hnd : ¬ homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree (p : ℤ) f) ∣ g)
    (z : Fin t → Fin 2 → ℤ) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0)
    (hzg : ∀ i, eval (fun j => eval (z i) (scaledModelCoordinates (p : ℤ) a j)) g = 0) :
    t ≤ f.totalDegree * M := by
  obtain ⟨g', hg', he, hnd'⟩ := scaledModelCoordinates_auxiliary_transport (p : ℤ) a f g hg hnd
  exact scaled_plane_points_card_le_auxiliary_degree f hprim hir hp hp0 g' hg' hnd' z hinj hz
    (fun i => (he (z i)).trans (hzg i))

end
end AffineCurveCounting
