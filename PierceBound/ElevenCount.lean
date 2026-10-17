import PierceBound.SliceCount
import PierceBound.PatternCount

/-!
# The refined counting lemma

At a state with pattern `θ = (A, A', A'', U, V, U', V')` and gaps `κ = (k₀, …, k₄)`:

* the Cramer formulas `U S(k₁,k₂,k₃) = A' E(k₀,k₁,k₂,k₃) + A S(k₂,k₃,k₄)` and
  `-V S(k₁,k₂,k₃) = A' S(k₀,k₁,k₂) + A E(k₁,k₂,k₃,k₄)` give `U > 0 > V` (`pattern_signs`);
* eliminating `k₀` and `k₄` leaves the ternary quadratic `F_θ(k₁, k₂, k₃) = 0` (`tern_rel`),
  whose binary part has `α = U(U + A') > 0`, discriminant `-4A'V(A' + U)(U - V) > 0`, and slice
  leading coefficient `16 A A'² U (A - V)(A' + U)²(U - V) ≠ 0`.

So each pattern accounts for at most `(2H+1)(W+4)` gap triples (`slice_count`), and
`#G ≤ 4 (2M+1)⁷ (2H+1)(W+4)` (`pattern_count_eleven`).
-/

namespace PierceBound

open Finset

/-- `S(a,b,c) = a²b + (a-1)b² + ac`. -/
def sF (a b c : ℤ) : ℤ := a ^ 2 * b + (a - 1) * b ^ 2 + a * c

/-- `E(a,b,c,d) = a²c + (2a-1)bc + ac² + ad`. -/
def eF (a b c d : ℤ) : ℤ := a ^ 2 * c + (2 * a - 1) * b * c + a * c ^ 2 + a * d

lemma sF_pos {a b c : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 0 < sF a b c := by
  unfold sF
  have h1 : 0 ≤ (a - 1) * b ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 < a ^ 2 * b := by positivity
  have h3 : 0 < a * c := by positivity
  linarith

lemma eF_pos {a b c d : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    0 < eF a b c d := by
  unfold eF
  have h1 : 0 ≤ (2 * a - 1) * b * c := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : 0 < a ^ 2 * c := by positivity
  have h3 : 0 < a * c ^ 2 := by positivity
  have h4 : 0 < a * d := by positivity
  linarith

/-- **The signs** (Lemma 6): `U > 0` and `V < 0`. -/
theorem pattern_signs {A A' U V k0 k1 k2 k3 k4 : ℤ} (hA : 1 ≤ A) (hA' : 1 ≤ A')
    (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) (h3 : 1 ≤ k3) (h4 : 1 ≤ k4)
    (e0 : -A' * k0 + U * k1 + V * k2 + A * k3 = 0)
    (e3 : -A' * (k0 ^ 2 + k1) + U * (k1 * (2 * k0 + k1) + k2) +
      V * (k2 * (2 * k0 + 2 * k1 + k2) + k3) +
      A * (k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4) = 0) :
    0 < U ∧ V < 0 := by
  have hu : U * sF k1 k2 k3 = A' * eF k0 k1 k2 k3 + A * sF k2 k3 k4 := by
    unfold sF eF
    linear_combination (k2 * (2 * k0 + 2 * k1 + k2) + k3) * e0 - k2 * e3
  have hv : -V * sF k1 k2 k3 = A' * sF k0 k1 k2 + A * eF k1 k2 k3 k4 := by
    unfold sF eF
    linear_combination -(k1 * e3 - (k1 * (2 * k0 + k1) + k2) * e0)
  have hS := sF_pos h1 h2 h3
  have r1 : 0 < A' * eF k0 k1 k2 k3 + A * sF k2 k3 k4 :=
    add_pos (mul_pos (by linarith) (eF_pos h0 h1 h2 h3)) (mul_pos (by linarith) (sF_pos h2 h3 h4))
  have r2 : 0 < A' * sF k0 k1 k2 + A * eF k1 k2 k3 k4 :=
    add_pos (mul_pos (by linarith) (sF_pos h0 h1 h2)) (mul_pos (by linarith) (eF_pos h1 h2 h3 h4))
  constructor
  · rw [← hu] at r1; exact pos_of_mul_pos_left r1 hS.le
  · rw [← hv] at r2
    have := pos_of_mul_pos_left r2 hS.le
    linarith

/-- The ternary quadratic of a pattern `θ = (A, A', A'', U, V, U', V')`. -/
def ternθ (A A' A'' U V U' V' x y z : ℤ) : ℤ :=
  tern (U * (U + A')) (2 * V * (U + A')) (V * (V + A')) (2 * A * (U + A')) (A * A'' - A' ^ 2)
    (2 * A * (V + A')) (A' * U - A * U') (A * (A + A')) (A' * V - A * V') 0 x y z

/-- **The ternary relation.** The linear relations at `i` and `i+1` and the quadratic relation
at `i` give `F_θ(k₁, k₂, k₃) = 0`. -/
theorem tern_rel {A A' A'' U V U' V' k0 k1 k2 k3 k4 : ℤ} (hA' : A' ≠ 0)
    (e0 : -A' * k0 + U * k1 + V * k2 + A * k3 = 0)
    (e4 : -A'' * k1 + U' * k2 + V' * k3 + A' * k4 = 0)
    (e3 : -A' * (k0 ^ 2 + k1) + U * (k1 * (2 * k0 + k1) + k2) +
      V * (k2 * (2 * k0 + 2 * k1 + k2) + k3) +
      A * (k3 * (2 * k0 + 2 * k1 + 2 * k2 + k3) + k4) = 0) :
    ternθ A A' A'' U V U' V' k1 k2 k3 = 0 := by
  have h : A' * ternθ A A' A'' U V U' V' k1 k2 k3 = 0 := by
    unfold ternθ tern
    linear_combination A' ^ 2 * e3 + (A * A' * k3 - A' ^ 2 * k0 + A' * U * k1 + A' * V * k2) * e0 -
      A * A' * e4
  exact (mul_eq_zero.mp h).resolve_left hA'

lemma tern_disc (A' U V : ℤ) :
    (2 * V * (U + A')) ^ 2 - 4 * (U * (U + A')) * (V * (V + A')) =
      -4 * A' * V * (A' + U) * (U - V) := by ring

lemma tern_lead (A A' U V : ℤ) :
    (2 * V * (U + A') * (2 * A * (U + A')) - 2 * (U * (U + A')) * (2 * A * (V + A'))) ^ 2 +
      ((2 * V * (U + A')) ^ 2 - 4 * (U * (U + A')) * (V * (V + A'))) *
        (4 * (U * (U + A')) * (A * (A + A')) - (2 * A * (U + A')) ^ 2) =
      16 * A * A' ^ 2 * U * (A - V) * (A' + U) ^ 2 * (U - V) := by ring

/-- Coefficient bounds for `F_θ` from bounds on the pattern. -/
lemma tern_coef_le {A A' A'' U V U' V' M : ℤ} (hA : |A| ≤ M) (hA' : |A'| ≤ M) (hA'' : |A''| ≤ M)
    (hU : |U| ≤ M) (hV : |V| ≤ M) (hU' : |U'| ≤ M) (hV' : |V'| ≤ M) :
    |U * (U + A')| ≤ 4 * M ^ 2 ∧ |2 * V * (U + A')| ≤ 4 * M ^ 2 ∧ |V * (V + A')| ≤ 4 * M ^ 2 ∧
    |2 * A * (U + A')| ≤ 4 * M ^ 2 ∧ |A * A'' - A' ^ 2| ≤ 4 * M ^ 2 ∧
    |2 * A * (V + A')| ≤ 4 * M ^ 2 ∧ |A' * U - A * U'| ≤ 4 * M ^ 2 ∧
    |A * (A + A')| ≤ 4 * M ^ 2 ∧ |A' * V - A * V'| ≤ 4 * M ^ 2 ∧ |(0 : ℤ)| ≤ 4 * M ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hA
  have m2 : ∀ a b X Y : ℤ, |a| ≤ X → |b| ≤ Y → |a * b| ≤ X * Y := fun a b X Y ha hb => by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have s2 : ∀ a b : ℤ, |a| ≤ M → |b| ≤ M → |a + b| ≤ 2 * M := fun a b ha hb =>
    (abs_add_le a b).trans (by linarith)
  have d2 : ∀ a b : ℤ, |a| ≤ M * M → |b| ≤ M * M → |a - b| ≤ 2 * (M * M) := fun a b ha hb =>
    (abs_sub a b).trans (by linarith)
  have hMM : 0 ≤ M * M := mul_nonneg hM hM
  have e : ∀ X : ℤ, X ≤ 2 * M * M → X ≤ 4 * M ^ 2 := fun X h => by nlinarith
  have two : |(2 : ℤ)| = 2 := by norm_num
  refine ⟨e _ (by have := m2 _ _ _ _ hU (s2 _ _ hU hA'); linarith),
    ?_, e _ (by have := m2 _ _ _ _ hV (s2 _ _ hV hA'); linarith), ?_,
    e _ (by have := d2 _ _ (m2 _ _ _ _ hA hA'') (show |A' ^ 2| ≤ M * M by
      rw [sq]; exact m2 _ _ _ _ hA' hA'); linarith),
    ?_, e _ (by have := d2 _ _ (m2 _ _ _ _ hA' hU) (m2 _ _ _ _ hA hU'); linarith),
    e _ (by have := m2 _ _ _ _ hA (s2 _ _ hA hA'); linarith),
    e _ (by have := d2 _ _ (m2 _ _ _ _ hA' hV) (m2 _ _ _ _ hA hV'); linarith), by simp; positivity⟩
  · rw [mul_assoc, abs_mul, two]
    have := m2 _ _ _ _ hV (s2 _ _ hU hA'); nlinarith
  · rw [mul_assoc, abs_mul, two]
    have := m2 _ _ _ _ hA (s2 _ _ hU hA'); nlinarith
  · rw [mul_assoc, abs_mul, two]
    have := m2 _ _ _ _ hA (s2 _ _ hV hA'); nlinarith

/-- The box `[1, H]` sits inside `[-H, H]`. -/
lemma mem_ibox_of {H : ℕ} {x : ℤ} (h1 : 1 ≤ x) (h2 : x ≤ H) : x ∈ ibox H :=
  mem_Icc.mpr ⟨by omega, h2⟩

/-- **The refined counting lemma.** -/
theorem pattern_count_eleven {G : Finset ℕ} {θ : ℕ → Fin 7 → ℤ} {κ : ℕ → Fin 5 → ℤ}
    {Q : ℕ → ℤ} {a : ℤ} {M H W : ℕ} (hH : 1 ≤ H)
    (hQ : Set.InjOn Q G)
    (hθ : ∀ i ∈ G, ∀ t, |θ i t| ≤ M)
    (hκ : ∀ i ∈ G, ∀ t, 1 ≤ κ i t ∧ κ i t ≤ H)
    (h0 : ∀ i ∈ G, 1 ≤ θ i 0) (h1 : ∀ i ∈ G, 1 ≤ θ i 1)
    (e0 : ∀ i ∈ G, -θ i 1 * κ i 0 + θ i 3 * κ i 1 + θ i 4 * κ i 2 + θ i 0 * κ i 3 = 0)
    (e4 : ∀ i ∈ G, -θ i 2 * κ i 1 + θ i 5 * κ i 2 + θ i 6 * κ i 3 + θ i 1 * κ i 4 = 0)
    (e3 : ∀ i ∈ G, -θ i 1 * (κ i 0 ^ 2 + κ i 1) + θ i 3 * (κ i 1 * (2 * κ i 0 + κ i 1) + κ i 2) +
      θ i 4 * (κ i 2 * (2 * κ i 0 + 2 * κ i 1 + κ i 2) + κ i 3) +
      θ i 0 * (κ i 3 * (2 * κ i 0 + 2 * κ i 1 + 2 * κ i 2 + κ i 3) + κ i 4) = 0)
    (hm : ∀ i ∈ G, quart (-θ i 1) (θ i 3) (θ i 4) (θ i 0) (κ i 0) (κ i 1) (κ i 2) (Q i) =
      a * muH4 (κ i 0) (κ i 1) (κ i 2) (κ i 3) (κ i 4))
    (hW : ∀ M' : ℤ, M' ≠ 0 → |M'| ≤ 116 * ((4 * M ^ 2 : ℕ) : ℤ) ^ 4 * (H : ℤ) ^ 2 →
      2 * M'.natAbs.divisors.card ^ 3 *
        (Nat.log 3 ((11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2) + 1) ≤ W) :
    G.card ≤ 4 * (2 * M + 1) ^ 7 * ((2 * H + 1) * (W + 4)) := by
  classical
  set F : ℕ → (Fin 7 → ℤ) × (Fin 5 → ℤ) := fun i => (θ i, κ i)
  -- step 1: at most four states per `(θ, κ)`
  have step1 : G.card ≤ 4 * (G.image F).card := by
    refine card_le_mul_card_image G 4 fun v hv => ?_
    set S := G.filter fun i => F i = v
    rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
    · rw [hS]; simp
    have hi₀' := (mem_filter.mp hi₀)
    rw [← card_image_of_injOn (hQ.mono (fun x hx => (mem_filter.mp hx).1))]
    have hlead : v.1 0 ≠ 0 := by
      rw [← hi₀'.2]; have := h0 i₀ hi₀'.1; simp only [F]; omega
    refine card_le_four_of_quartic (c3 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1)
      (v.2 2) 3) (c2 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 2)
      (c1 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 1)
      (c0 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 0 -
        a * muH4 (v.2 0) (v.2 1) (v.2 2) (v.2 3) (v.2 4)) hlead fun z hz => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    obtain ⟨hiG, hFi⟩ := mem_filter.mp hi
    have := hm i hiG
    rw [quart_eq] at this
    rw [← hFi]
    simp only [F]
    linarith
  -- step 2: `(θ, κ)` is determined by `(θ, κ₁, κ₂, κ₃)`
  set π : (Fin 7 → ℤ) × (Fin 5 → ℤ) → (Fin 7 → ℤ) × ℤ × ℤ × ℤ :=
    fun v => (v.1, v.2 1, v.2 2, v.2 3)
  have step2 : (G.image F).card = ((G.image F).image π).card := by
    refine (card_image_of_injOn fun v hv v' hv' h => ?_).symm
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_coe.mp hv)
    obtain ⟨i', hi', rfl⟩ := mem_image.mp (mem_coe.mp hv')
    simp only [F, π, Prod.mk.injEq] at h ⊢
    obtain ⟨hθ', k1, k2, k3⟩ := h
    refine ⟨hθ', ?_⟩
    have hN : θ i 1 ≠ 0 := by have := h1 i hi; omega
    have a0 := e0 i hi
    have a0' := e0 i' hi'
    have a4 := e4 i hi
    have a4' := e4 i' hi'
    rw [← hθ', ← k1, ← k2, ← k3] at a0' a4'
    have k0 : κ i 0 = κ i' 0 := by
      have : θ i 1 * κ i 0 = θ i 1 * κ i' 0 := by linarith
      exact mul_left_cancel₀ hN this
    have k4 : κ i 4 = κ i' 4 := by
      have : θ i 1 * κ i 4 = θ i 1 * κ i' 4 := by linarith
      exact mul_left_cancel₀ hN this
    funext t
    fin_cases t
    · exact k0
    · exact k1
    · exact k2
    · exact k3
    · exact k4
  -- step 3: each pattern has few gap triples
  set B7 : Finset (Fin 7 → ℤ) := Fintype.piFinset fun _ => Icc (-(M : ℤ)) M
  have hB7 : B7.card = (2 * M + 1) ^ 7 := by
    simp only [B7, Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ, Fintype.card_fin]
    congr 1; omega
  have step3 : ((G.image F).image π).card ≤ ((2 * H + 1) * (W + 4)) * B7.card := by
    refine card_le_mul_card_image_of_maps_to (f := fun w => w.1) (t := B7) (fun w hw => ?_) _
      fun θ0 _ => ?_
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      exact Fintype.mem_piFinset.mpr fun t => mem_Icc.mpr (abs_le.mp (hθ i hi t))
    set Fib := ((G.image F).image π).filter fun w => w.1 = θ0
    rcases Fib.eq_empty_or_nonempty with hF | ⟨w0, hw0⟩
    · rw [hF]; simp
    obtain ⟨hw0m, hw0θ⟩ := mem_filter.mp hw0
    obtain ⟨v0, hv0, rfl⟩ := mem_image.mp hw0m
    obtain ⟨i0, hi0, rfl⟩ := mem_image.mp hv0
    simp only [F, π] at hw0θ
    subst hw0θ
    -- nondegeneracy of `F_θ` from the signs at `i0`
    have hk : ∀ t, 1 ≤ κ i0 t := fun t => (hκ i0 hi0 t).1
    obtain ⟨hU, hV⟩ := pattern_signs (h0 i0 hi0) (h1 i0 hi0) (hk 0) (hk 1) (hk 2) (hk 3) (hk 4)
      (e0 i0 hi0) (e3 i0 hi0)
    have hA := h0 i0 hi0
    have hA' := h1 i0 hi0
    set A := θ i0 0; set A' := θ i0 1; set A'' := θ i0 2
    set U := θ i0 3; set V := θ i0 4; set U' := θ i0 5; set V' := θ i0 6
    have hM : |A| ≤ (M : ℤ) ∧ |A'| ≤ M ∧ |A''| ≤ M ∧ |U| ≤ M ∧ |V| ≤ M ∧ |U'| ≤ M ∧ |V'| ≤ M :=
      ⟨hθ i0 hi0 0, hθ i0 hi0 1, hθ i0 hi0 2, hθ i0 hi0 3, hθ i0 hi0 4, hθ i0 hi0 5, hθ i0 hi0 6⟩
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
      tern_coef_le hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2.1 hM.2.2.2.2.2.2
    have cK : ((4 * M ^ 2 : ℕ) : ℤ) = 4 * (M : ℤ) ^ 2 := by push_cast; ring
    rw [← cK] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have hsl := slice_count (α := U * (U + A')) (β := 2 * V * (U + A')) (γ := V * (V + A'))
      (d1 := 2 * A * (U + A')) (d0 := A * A'' - A' ^ 2) (e1 := 2 * A * (V + A'))
      (e0 := A' * U - A * U') (f2 := A * (A + A')) (f1 := A' * V - A * V') (f0 := 0)
      (K := 4 * M ^ 2) (H := H) (W := W) hH (by positivity)
      (by rw [tern_disc]; nlinarith [mul_pos (mul_pos (show (0 : ℤ) < A' by omega)
        (show (0 : ℤ) < -V by omega)) (mul_pos (show (0 : ℤ) < A' + U by omega)
          (show (0 : ℤ) < U - V by omega))])
      (by
        rw [tern_lead]
        have hA0 : (0 : ℤ) < A := by omega
        have hA'0 : (0 : ℤ) < A' := by omega
        exact ne_of_gt (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hA0)
          (pow_pos hA'0 2)) hU) (by linarith)) (pow_pos (by linarith) 2)) (by linarith)))
      ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ hW
    refine le_trans (card_le_card_of_injOn (fun w => (w.2.1, w.2.2.1, w.2.2.2)) (fun w hw => ?_)
      (fun w hw w' hw' h => ?_)) hsl
    · obtain ⟨hwm, hwθ⟩ := mem_filter.mp (mem_coe.mp hw)
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hwm
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      simp only [F, π] at hwθ ⊢
      have hki := hκ i hi
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_ibox_of (hki 1).1 (hki 1).2,
        mem_product.mpr ⟨mem_ibox_of (hki 2).1 (hki 2).2, mem_ibox_of (hki 3).1 (hki 3).2⟩⟩, ?_⟩
      have := tern_rel (by have := h1 i hi; omega) (e0 i hi) (e4 i hi) (e3 i hi)
      rw [hwθ] at this
      exact this
    · obtain ⟨-, hwθ⟩ := mem_filter.mp (mem_coe.mp hw)
      obtain ⟨-, hwθ'⟩ := mem_filter.mp (mem_coe.mp hw')
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (hwθ.trans hwθ'.symm) (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
  calc G.card ≤ 4 * (G.image F).card := step1
    _ = 4 * ((G.image F).image π).card := by rw [step2]
    _ ≤ 4 * (((2 * H + 1) * (W + 4)) * B7.card) := Nat.mul_le_mul_left _ step3
    _ = 4 * (2 * M + 1) ^ 7 * ((2 * H + 1) * (W + 4)) := by rw [hB7]; ring

/-- **The counting lemma for an arbitrary set of patterns.** -/
theorem pattern_count_gen {G : Finset ℕ} {θ : ℕ → Fin 7 → ℤ} {κ : ℕ → Fin 5 → ℤ}
    {Q : ℕ → ℤ} {a : ℤ} {M H W : ℕ} {B : Finset (Fin 7 → ℤ)} (hH : 1 ≤ H)
    (hB : ∀ i ∈ G, θ i ∈ B)
    (hQ : Set.InjOn Q G)
    (hθ : ∀ i ∈ G, ∀ t, |θ i t| ≤ M)
    (hκ : ∀ i ∈ G, ∀ t, 1 ≤ κ i t ∧ κ i t ≤ H)
    (h0 : ∀ i ∈ G, 1 ≤ θ i 0) (h1 : ∀ i ∈ G, 1 ≤ θ i 1)
    (e0 : ∀ i ∈ G, -θ i 1 * κ i 0 + θ i 3 * κ i 1 + θ i 4 * κ i 2 + θ i 0 * κ i 3 = 0)
    (e4 : ∀ i ∈ G, -θ i 2 * κ i 1 + θ i 5 * κ i 2 + θ i 6 * κ i 3 + θ i 1 * κ i 4 = 0)
    (e3 : ∀ i ∈ G, -θ i 1 * (κ i 0 ^ 2 + κ i 1) + θ i 3 * (κ i 1 * (2 * κ i 0 + κ i 1) + κ i 2) +
      θ i 4 * (κ i 2 * (2 * κ i 0 + 2 * κ i 1 + κ i 2) + κ i 3) +
      θ i 0 * (κ i 3 * (2 * κ i 0 + 2 * κ i 1 + 2 * κ i 2 + κ i 3) + κ i 4) = 0)
    (hm : ∀ i ∈ G, quart (-θ i 1) (θ i 3) (θ i 4) (θ i 0) (κ i 0) (κ i 1) (κ i 2) (Q i) =
      a * muH4 (κ i 0) (κ i 1) (κ i 2) (κ i 3) (κ i 4))
    (hW : ∀ M' : ℤ, M' ≠ 0 → |M'| ≤ 116 * ((4 * M ^ 2 : ℕ) : ℤ) ^ 4 * (H : ℤ) ^ 2 →
      2 * M'.natAbs.divisors.card ^ 3 *
        (Nat.log 3 ((11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2) + 1) ≤ W) :
    G.card ≤ 4 * B.card * ((2 * H + 1) * (W + 4)) := by
  classical
  set F : ℕ → (Fin 7 → ℤ) × (Fin 5 → ℤ) := fun i => (θ i, κ i)
  -- step 1: at most four states per `(θ, κ)`
  have step1 : G.card ≤ 4 * (G.image F).card := by
    refine card_le_mul_card_image G 4 fun v hv => ?_
    set S := G.filter fun i => F i = v
    rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
    · rw [hS]; simp
    have hi₀' := (mem_filter.mp hi₀)
    rw [← card_image_of_injOn (hQ.mono (fun x hx => (mem_filter.mp hx).1))]
    have hlead : v.1 0 ≠ 0 := by
      rw [← hi₀'.2]; have := h0 i₀ hi₀'.1; simp only [F]; omega
    refine card_le_four_of_quartic (c3 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1)
      (v.2 2) 3) (c2 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 2)
      (c1 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 1)
      (c0 := quartC (-v.1 1) (v.1 3) (v.1 4) (v.1 0) (v.2 0) (v.2 1) (v.2 2) 0 -
        a * muH4 (v.2 0) (v.2 1) (v.2 2) (v.2 3) (v.2 4)) hlead fun z hz => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    obtain ⟨hiG, hFi⟩ := mem_filter.mp hi
    have := hm i hiG
    rw [quart_eq] at this
    rw [← hFi]
    simp only [F]
    linarith
  -- step 2: `(θ, κ)` is determined by `(θ, κ₁, κ₂, κ₃)`
  set π : (Fin 7 → ℤ) × (Fin 5 → ℤ) → (Fin 7 → ℤ) × ℤ × ℤ × ℤ :=
    fun v => (v.1, v.2 1, v.2 2, v.2 3)
  have step2 : (G.image F).card = ((G.image F).image π).card := by
    refine (card_image_of_injOn fun v hv v' hv' h => ?_).symm
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_coe.mp hv)
    obtain ⟨i', hi', rfl⟩ := mem_image.mp (mem_coe.mp hv')
    simp only [F, π, Prod.mk.injEq] at h ⊢
    obtain ⟨hθ', k1, k2, k3⟩ := h
    refine ⟨hθ', ?_⟩
    have hN : θ i 1 ≠ 0 := by have := h1 i hi; omega
    have a0 := e0 i hi
    have a0' := e0 i' hi'
    have a4 := e4 i hi
    have a4' := e4 i' hi'
    rw [← hθ', ← k1, ← k2, ← k3] at a0' a4'
    have k0 : κ i 0 = κ i' 0 := by
      have : θ i 1 * κ i 0 = θ i 1 * κ i' 0 := by linarith
      exact mul_left_cancel₀ hN this
    have k4 : κ i 4 = κ i' 4 := by
      have : θ i 1 * κ i 4 = θ i 1 * κ i' 4 := by linarith
      exact mul_left_cancel₀ hN this
    funext t
    fin_cases t
    · exact k0
    · exact k1
    · exact k2
    · exact k3
    · exact k4
  -- step 3: each pattern has few gap triples
  have step3 : ((G.image F).image π).card ≤ ((2 * H + 1) * (W + 4)) * B.card := by
    refine card_le_mul_card_image_of_maps_to (f := fun w => w.1) (t := B) (fun w hw => ?_) _
      fun θ0 _ => ?_
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      exact hB i hi
    set Fib := ((G.image F).image π).filter fun w => w.1 = θ0
    rcases Fib.eq_empty_or_nonempty with hF | ⟨w0, hw0⟩
    · rw [hF]; simp
    obtain ⟨hw0m, hw0θ⟩ := mem_filter.mp hw0
    obtain ⟨v0, hv0, rfl⟩ := mem_image.mp hw0m
    obtain ⟨i0, hi0, rfl⟩ := mem_image.mp hv0
    simp only [F, π] at hw0θ
    subst hw0θ
    -- nondegeneracy of `F_θ` from the signs at `i0`
    have hk : ∀ t, 1 ≤ κ i0 t := fun t => (hκ i0 hi0 t).1
    obtain ⟨hU, hV⟩ := pattern_signs (h0 i0 hi0) (h1 i0 hi0) (hk 0) (hk 1) (hk 2) (hk 3) (hk 4)
      (e0 i0 hi0) (e3 i0 hi0)
    have hA := h0 i0 hi0
    have hA' := h1 i0 hi0
    set A := θ i0 0; set A' := θ i0 1; set A'' := θ i0 2
    set U := θ i0 3; set V := θ i0 4; set U' := θ i0 5; set V' := θ i0 6
    have hM : |A| ≤ (M : ℤ) ∧ |A'| ≤ M ∧ |A''| ≤ M ∧ |U| ≤ M ∧ |V| ≤ M ∧ |U'| ≤ M ∧ |V'| ≤ M :=
      ⟨hθ i0 hi0 0, hθ i0 hi0 1, hθ i0 hi0 2, hθ i0 hi0 3, hθ i0 hi0 4, hθ i0 hi0 5, hθ i0 hi0 6⟩
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
      tern_coef_le hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2.1 hM.2.2.2.2.2.2
    have cK : ((4 * M ^ 2 : ℕ) : ℤ) = 4 * (M : ℤ) ^ 2 := by push_cast; ring
    rw [← cK] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    have hsl := slice_count (α := U * (U + A')) (β := 2 * V * (U + A')) (γ := V * (V + A'))
      (d1 := 2 * A * (U + A')) (d0 := A * A'' - A' ^ 2) (e1 := 2 * A * (V + A'))
      (e0 := A' * U - A * U') (f2 := A * (A + A')) (f1 := A' * V - A * V') (f0 := 0)
      (K := 4 * M ^ 2) (H := H) (W := W) hH (by positivity)
      (by rw [tern_disc]; nlinarith [mul_pos (mul_pos (show (0 : ℤ) < A' by omega)
        (show (0 : ℤ) < -V by omega)) (mul_pos (show (0 : ℤ) < A' + U by omega)
          (show (0 : ℤ) < U - V by omega))])
      (by
        rw [tern_lead]
        have hA0 : (0 : ℤ) < A := by omega
        have hA'0 : (0 : ℤ) < A' := by omega
        exact ne_of_gt (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hA0)
          (pow_pos hA'0 2)) hU) (by linarith)) (pow_pos (by linarith) 2)) (by linarith)))
      ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ hW
    refine le_trans (card_le_card_of_injOn (fun w => (w.2.1, w.2.2.1, w.2.2.2)) (fun w hw => ?_)
      (fun w hw w' hw' h => ?_)) hsl
    · obtain ⟨hwm, hwθ⟩ := mem_filter.mp (mem_coe.mp hw)
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hwm
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
      simp only [F, π] at hwθ ⊢
      have hki := hκ i hi
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_ibox_of (hki 1).1 (hki 1).2,
        mem_product.mpr ⟨mem_ibox_of (hki 2).1 (hki 2).2, mem_ibox_of (hki 3).1 (hki 3).2⟩⟩, ?_⟩
      have := tern_rel (by have := h1 i hi; omega) (e0 i hi) (e4 i hi) (e3 i hi)
      rw [hwθ] at this
      exact this
    · obtain ⟨-, hwθ⟩ := mem_filter.mp (mem_coe.mp hw)
      obtain ⟨-, hwθ'⟩ := mem_filter.mp (mem_coe.mp hw')
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (hwθ.trans hwθ'.symm) (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
  calc G.card ≤ 4 * (G.image F).card := step1
    _ = 4 * ((G.image F).image π).card := by rw [step2]
    _ ≤ 4 * (((2 * H + 1) * (W + 4)) * B.card) := Nat.mul_le_mul_left _ step3
    _ = 4 * B.card * ((2 * H + 1) * (W + 4)) := by ring


end PierceBound
