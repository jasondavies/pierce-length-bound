/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LinearJointGraph
public import PierceLengthBound.LatticeCurvature
public import PierceLengthBound.FixedDividendLatticeCurveCover
public import PierceLengthBound.PoweredJointCountingSlack

/-!
# Counting powered points in exterior lattice coordinates

Fix a full minor pattern `p`. The three node coordinates are replaced by their coordinates in a
reduced basis of the pattern lattice, of size `3H/λ`, and the three curvature coordinates by the
exterior coordinates `c = G W`, of size `8S'/(3λ²)` (`lattice_curvature_coordinates`). The
powered graph with coordinates `(y, cᵐ, Jⁿ)` is the image of the graph of `(nodes, (G W)ᵐ, Jⁿ)`
under an invertible block matrix, so it keeps primality and its Hilbert degree. The external
curve theorem then counts the gap vectors of a pattern in the smaller box
(`selected_latticeJointGraph_gap_count_slow`).
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Matrix Finset

/-! ### Changing the node coordinates -/

/-- The block matrix changing only the node coordinates of a graph. -/
def nodeBlockMatrix (B : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3 ⊕ Fin 4) (Fin 3 ⊕ Fin 4) ℚ :=
  fromBlocks B 0 0 1

lemma nodeBlockMatrix_det (B : Matrix (Fin 3) (Fin 3) ℚ) : (nodeBlockMatrix B).det = B.det := by
  simp [nodeBlockMatrix]

lemma nodeBlockMatrix_mulVec (B : Matrix (Fin 3) (Fin 3) ℚ) (y : Fin 3 → ℚ) (z : Fin 4 → ℚ) :
    nodeBlockMatrix B *ᵥ Sum.elim y z = Sum.elim (B *ᵥ y) z := by
  simp [nodeBlockMatrix, fromBlocks_mulVec]

/-! ### The fixed curvature data of a pattern -/

/-- The matrix `G` of `lattice_curvature_coordinates`, chosen once for each pattern. The
pattern graph depends on `G`; the coordinates `c` are recovered from `patternCurvature_spec`. -/
def patternCurvatureMatrix (p : Fin 10 → ℤ) : Matrix (Fin 3) (Fin 3) ℚ := by
  classical
  exact if h : p 0 ≠ 0 ∧ ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p then
    Classical.choose (lattice_curvature_coordinates h.1 h.2)
  else 1

/-- `lattice_curvature_coordinates` for the chosen matrix `patternCurvatureMatrix p`. -/
theorem patternCurvature_spec {p : Fin 10 → ℤ} (h0 : p 0 ≠ 0)
    (hp : ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p) :
    (patternCurvatureMatrix p).det ≠ 0 ∧
      ∃ c : (Fin 5 → ℤ) → (Fin 5 → ℤ) → Fin 3 → ℤ,
        ∀ M : Fin 3 → Fin 5 → ℤ, plk M = p →
          (fun t => (c (M 0) (M 1) t : ℚ)) = patternCurvatureMatrix p *ᵥ
            (fun t => ((curvatureVector (firstThree (M 0)) (firstThree (M 1)) t : ℤ) : ℚ)) ∧
          ∀ S : ℕ, (∀ j l, |M 0 j * M 1 l - M 0 l * M 1 j| ≤ S) →
            ∀ t, 3 * (shortR p : ℤ) ^ 2 * |c (M 0) (M 1) t| ≤ 8 * S := by
  classical
  have h : p 0 ≠ 0 ∧ ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p := ⟨h0, hp⟩
  simp only [patternCurvatureMatrix, h, ne_eq, not_false_eq_true, and_self, ↓reduceDIte]
  exact Classical.choose_spec (lattice_curvature_coordinates h.1 h.2)

/-! ### Points of the linearly changed powered graph -/

/-- The powered coordinates `(cᵐ, Jⁿ)` of a state. -/
def latticePowers (c : Fin 3 → ℤ) (J m n : ℕ) : Fin 4 → ℤ :=
  ![c 0 ^ m, c 1 ^ m, c 2 ^ m, (J : ℤ) ^ n]

/-- A state's nodes and powered coordinates `(cᵐ, Jⁿ)` lie on the linearly changed graph when
`c = G W`. -/
lemma orbitLinearJointGraph_point {a b l J : ℕ} (hba : b < a) (hl : l + 7 < P a b)
    (Gm : Matrix (Fin 3) (Fin 3) ℚ) (m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hz : orbitFreeNodesQ a b l ∈ coordinateZeroLocus I)
    (hJ : (Lz a b l : ℝ) * orbitNorm a b l = J) (c : Fin 3 → ℤ)
    (hc : (fun t => (c t : ℚ)) = Gm *ᵥ (fun t => (orbitCurvatureVector a b l t : ℚ))) :
    Sum.elim (orbitFreeNodesQ a b l) (fun j => (latticePowers c J m n j : ℚ)) ∈
      coordinateZeroLocus (orbitLinearJointGraphIdeal Gm a b l m n I) := by
  have hj : eval (orbitFreeNodesQ a b l) (jointRankFivePolynomial a b l) = (J : ℚ) := by
    apply (algebraMap ℚ ℝ).injective
    exact (jointRankFivePolynomial_eval_cast hba hl).trans hJ
  have hD := orbitJointDenominator_eval_ne_zero hba hl
  have hDN : eval (orbitFreeNodesQ a b l) (orbitJointDenominator a b l ^ (m + n)) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hD
  have hh := jointGraph_point I (orbitLinearJointNumerators Gm a b l m n)
    (orbitJointDenominator a b l ^ (m + n)) _ hz hDN
  have hlin (t : Fin 3) : eval (orbitFreeNodesQ a b l)
      (linearJointNumerators Gm (orbitJointNumerators a b l) t.castSucc) /
        eval (orbitFreeNodesQ a b l) (orbitJointDenominator a b l) = (c t : ℚ) := by
    rw [linearJointNumerators_castSucc, map_sum, Finset.sum_div, congrFun hc t]
    simp only [mulVec, dotProduct, map_mul, eval_C, mul_div_assoc]
    apply Finset.sum_congr rfl
    intro s _
    rw [orbitJoint_curvature_evaluation hba hl s]
  have he : Sum.elim (orbitFreeNodesQ a b l)
      (fun j => eval (orbitFreeNodesQ a b l) (orbitLinearJointNumerators Gm a b l m n j) /
        eval (orbitFreeNodesQ a b l) (orbitJointDenominator a b l ^ (m + n))) =
      Sum.elim (orbitFreeNodesQ a b l) (fun j => (latticePowers c J m n j : ℚ)) := by
    congr 1
    funext j
    simp only [orbitLinearJointNumerators, poweredGraphNumerators, map_mul, map_pow]
    rw [powered_fraction _ _ hD (jointCoordinatePowers_le m n j)]
    fin_cases j
    · simp only [Fin.zero_eta]
      rw [show (0 : Fin 4) = (0 : Fin 3).castSucc from rfl, hlin 0]
      simp [latticePowers, jointCoordinatePowers]
    · simp only [Fin.mk_one]
      rw [show (1 : Fin 4) = (1 : Fin 3).castSucc from rfl, hlin 1]
      simp [latticePowers, jointCoordinatePowers]
    · rw [show (⟨2, by decide⟩ : Fin 4) = (2 : Fin 3).castSucc from rfl, hlin 2]
      simp [latticePowers, jointCoordinatePowers]
    · change (eval (orbitFreeNodesQ a b l) (orbitJointNumerators a b l 3) /
        eval (orbitFreeNodesQ a b l) (orbitJointDenominator a b l)) ^ n = _
      rw [orbitJoint_rankFive_evaluation hba hl, hj]
      simp [latticePowers]
  rw [he] at hh
  exact hh

/-! ### The box -/

/-- The box of the lattice coordinates of a pattern: nodes `3H/λ`, curvature coordinates
`(8S'/(3λ²))ᵐ` and rank-five integers `Yⁿ` (paper, `lem:latticecoords`). The `max 1` keeps the
box positive when the floor divisions vanish. -/
def latticeJointBoxHeight (p : Fin 10 → ℤ) (a A T m n : ℕ) : ℕ :=
  max 1 (max (3 * selectedGapHeight a A T / shortR p)
    (max ((8 * selectedAllMinorHeight a A T / (3 * shortR p ^ 2)) ^ m)
      (selectedRankFiveHeight a A T ^ n)))

lemma latticeJointBoxHeight_pos (p : Fin 10 → ℤ) (a A T m n : ℕ) :
    1 ≤ latticeJointBoxHeight p a A T m n := le_max_left _ _

lemma le_latticeJointBoxHeight_nodes (p : Fin 10 → ℤ) (a A T m n : ℕ) :
    3 * selectedGapHeight a A T / shortR p ≤ latticeJointBoxHeight p a A T m n :=
  (le_max_left _ _).trans (le_max_right _ _)

lemma le_latticeJointBoxHeight_curvature (p : Fin 10 → ℤ) (a A T m n : ℕ) :
    (8 * selectedAllMinorHeight a A T / (3 * shortR p ^ 2)) ^ m ≤
      latticeJointBoxHeight p a A T m n :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

lemma le_latticeJointBoxHeight_rankFive (p : Fin 10 → ℤ) (a A T m n : ℕ) :
    selectedRankFiveHeight a A T ^ n ≤ latticeJointBoxHeight p a A T m n :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

/-- The lattice box is at most the polynomial bound `10²⁵ᵏ a¹⁵ᵏ`, `k = m + n + 1`, of
`poweredJointPointBoxHeight_polynomial`, so the logarithmic factor is unchanged. -/
lemma latticeJointBoxHeight_polynomial {p : Fin 10 → ℤ} {a A T : ℕ} (ha : 1 ≤ a) (hA : A ≤ a)
    (m n : ℕ) : latticeJointBoxHeight p a A T m n ≤
      (10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1)) := by
  have hold := poweredJointPointBoxHeight_polynomial (T := T) ha hA m n
  have hH : selectedGapHeight a A T ≤ 29 * a := by
    have := Nat.div_le_self (28 * a) (A * T)
    unfold selectedGapHeight
    omega
  have hS : 8 * selectedAllMinorHeight a A T ≤ 10 ^ 25 * a ^ 15 := by
    have h1 : selectedAllMinorHeight a A T ≤ 9472 * A ^ 3 * selectedGapHeight a A T ^ 3 :=
      Nat.div_le_self _ _
    have h2 : 9472 * A ^ 3 * selectedGapHeight a A T ^ 3 ≤ 9472 * a ^ 3 * (29 * a) ^ 3 := by
      gcongr
    have h3 : a ^ 6 ≤ a ^ 15 := Nat.pow_le_pow_right ha (by norm_num)
    calc 8 * selectedAllMinorHeight a A T ≤ 8 * (9472 * a ^ 3 * (29 * a) ^ 3) := by
          omega
      _ = (8 * 9472 * 29 ^ 3) * a ^ 6 := by ring
      _ ≤ (8 * 9472 * 29 ^ 3) * a ^ 15 := by gcongr
      _ ≤ _ := by gcongr; norm_num
  have hbig : 1 ≤ (10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1)) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hB : 10 ^ 25 * a ^ 15 ≤ (10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1)) := by
    calc 10 ^ 25 * a ^ 15 = (10 ^ 25 * a ^ 15) ^ 1 := by ring
      _ ≤ (10 ^ 25 * a ^ 15) ^ (m + n + 1) :=
        Nat.pow_le_pow_right (by positivity) (by omega)
      _ = _ := by ring
  apply max_le hbig
  apply max_le
  · have : 3 * selectedGapHeight a A T / shortR p ≤ 3 * selectedGapHeight a A T :=
      Nat.div_le_self _ _
    exact this.trans ((le_max_left _ _).trans hold)
  · apply max_le
    · have hc : 8 * selectedAllMinorHeight a A T / (3 * shortR p ^ 2) ≤ 10 ^ 25 * a ^ 15 :=
        (Nat.div_le_self _ _).trans hS
      calc _ ≤ (10 ^ 25 * a ^ 15) ^ m := Nat.pow_le_pow_left hc m
        _ ≤ (10 ^ 25 * a ^ 15) ^ (m + n + 1) :=
          Nat.pow_le_pow_right (by positivity) (by omega)
        _ = _ := by ring
    · exact (le_max_right _ _ |>.trans (le_max_right _ _)).trans hold

/-! ### Counting -/

/-- The curvature coordinates of `lattice_curvature_coordinates` fit in the curvature part of
the box. -/
lemma lattice_curvature_power_le {p : Fin 10 → ℤ} (hp0 : p 0 ≠ 0) {S m : ℕ} {c : ℤ}
    (hc : 3 * (shortR p : ℤ) ^ 2 * |c| ≤ 8 * S) :
    |c ^ m| ≤ (((8 * S / (3 * shortR p ^ 2)) ^ m : ℕ) : ℤ) := by
  have hR : (0 : ℤ) < 3 * (shortR p : ℤ) ^ 2 := by
    have := (shortR_spec (piv_ne_zero hp0)).1
    positivity
  have h1 : |c| ≤ (8 * (S : ℤ)) / (3 * (shortR p : ℤ) ^ 2) :=
    Int.le_ediv_of_mul_le hR (by linarith)
  rw [abs_pow]
  push_cast
  exact pow_le_pow_left₀ (abs_nonneg _) (by exact_mod_cast h1) m

/-- Uniform counting of the gap vectors of one full pattern on one component, in the lattice
box. -/
theorem selected_latticeJointGraph_gap_count (m n lo hi : ℕ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ δ : ℕ, lo ≤ δ ∧ δ ≤ hi ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace (orbitLinearJointGraphIdeal
            (patternCurvatureMatrix (plk (Mi a b i))) a b i m n I) k) : ℤ) =
              (δ : ℤ) * k + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, plk (Mi a b l) = plk (Mi a b i)) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤
            C * (latticeJointBoxHeight (plk (Mi a b i)) a A T m n : ℝ) ^ (1 / (lo : ℝ)) *
              (Real.log (latticeJointBoxHeight (plk (Mi a b i)) a A T m n) + 1) := by
  classical
  obtain ⟨C, hC, hcount⟩ := affine_curve_points_finite_coordinates
    (Fin 3 ⊕ Fin 4) lo hi (by simp) hlo hlohi
  refine ⟨C, hC, ?_⟩
  intro a b s T A i hba hmem hsT I hI hdegree G hG hpat hz
  obtain ⟨δ, hdlo, hdhi, hd⟩ := hdegree
  let : I.IsPrime := hI
  set p := plk (Mi a b i)
  set Bx := latticeJointBoxHeight p a A T m n
  have hB : (1 : ℝ) ≤ Bx := by exact_mod_cast latticeJointBoxHeight_pos p a A T m n
  have hlog : 0 ≤ Real.log (Bx : ℝ) := Real.log_nonneg hB
  by_cases hne : G.Nonempty
  swap
  · have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, image_empty, card_empty, Nat.cast_zero]
    positivity
  obtain ⟨j0, hj0⟩ := hne
  have facts (l) (hl : l ∈ G) := selectedStart_spec hmem hsT (hG hl)
  have hθ (l) (hl : l ∈ G) : theta a b i = theta a b l := by
    rw [theta_eq, theta_eq, hpat l hl]
  have hj0P := (facts j0 hj0).1
  have hp0 : p 0 ≠ 0 := by
    rw [← hpat j0 hj0]; exact orbit_pattern_first hba (by omega)
  obtain ⟨hGdet, c0, hGspec⟩ := patternCurvature_spec hp0 ⟨Mi a b i, rfl⟩
  set Gm := patternCurvatureMatrix p
  -- node coordinates in a reduced basis of the pattern lattice
  set V := G.image (kap a b)
  have hVne : V.Nonempty := ⟨_, mem_image_of_mem _ hj0⟩
  have hVs : ∀ k ∈ V, (∀ j, |k j| ≤ selectedGapHeight a A T) ∧
      ∃ M : Fin 3 → Fin 5 → ℤ, plk M = p ∧ ∀ j, M 1 j = k j := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hk
    obtain ⟨_, hkl, _⟩ := facts l hl
    refine ⟨fun j => ?_, Mi a b l, hpat l hl, fun j => ?_⟩
    · have hkj : kap a b l j = kq a b (l + j.val) := by fin_cases j <;> rfl
      have h := hkl j.val (by omega)
      rw [hkj, abs_of_nonneg (by linarith [h.1])]
      exact_mod_cast h.2
    · fin_cases j <;> rfl
  obtain ⟨Bn, y, hBn, hy, hnodes⟩ := lattice_node_coordinates hVne hp0 hVs
  let Bq : Matrix (Fin 3) (Fin 3) ℚ := fun r t => (Bn r t : ℚ)
  have hBq : Bq.det ≠ 0 := by
    change (Bn.map (fun x => (x : ℚ))).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hBn
  let Cb := nodeBlockMatrix Bq
  have hCb : Cb.det ≠ 0 := by rw [nodeBlockMatrix_det]; exact hBq
  let I' := (orbitLinearJointGraphIdeal Gm a b i m n I).map (matrixSubstitution Cb).toRingHom
  have hprime0 : (orbitLinearJointGraphIdeal Gm a b i m n I).IsPrime := by
    rw [orbitLinearJointGraph_congr (hθ j0 hj0)]
    apply jointGraphIdeal_isPrime I _ _
    intro hmemD
    have hev := hz j0 hj0 _ hmemD
    rw [map_pow] at hev
    exact pow_ne_zero (m + n)
      (orbitJointDenominator_eval_ne_zero hba (by omega : j0 + 7 < P a b)) hev
  have hprime : I'.IsPrime := matrix_coordinate_prime Cb hCb _
  have hd' : ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I' k) : ℤ) = (δ : ℤ) * k + c := by
    simpa only [I', nonsingular_matrix_filtered_finrank Cb hCb] using hd
  -- representatives, their rank-five integers and their points
  obtain ⟨l, hl, hkl, _⟩ := gap_image_representatives hba G
    (fun l hl => by have := (facts l hl).1; omega) hθ
  choose J _hJpos hJ hJheight using fun k : V =>
    selected_rankFive_positive_integer hba hmem hsT (hG (hl k))
  let cc := fun k : V => c0 (Mi a b (l k) 0) (Mi a b (l k) 1)
  let z (k : V) : Fin 3 ⊕ Fin 4 → ℤ := Sum.elim (y k.val) (latticePowers (cc k) (J k) m n)
  have hz_inj : Function.Injective z := by
    intro k k' he
    have hy' : y k.val = y k'.val := by
      funext t; exact congrFun he (Sum.inl t)
    exact Subtype.ext (hy k.property k'.property hy')
  let Sz := Finset.univ.image z
  have hScard : Sz.card = V.card := by
    dsimp only [Sz]
    rw [card_image_of_injective _ hz_inj, card_univ, Fintype.card_coe]
  have hSbox : ∀ w ∈ Sz, ∀ t, |(w t : ℝ)| ≤ (Bx : ℝ) := by
    intro w hw t
    obtain ⟨k, _, rfl⟩ := mem_image.mp hw
    have hlk := hl k
    have hZ : |z k t| ≤ (Bx : ℤ) := by
      cases t with
      | inl t =>
        have h := ((hnodes k.val k.property).1 t)
        exact h.trans (by exact_mod_cast le_latticeJointBoxHeight_nodes p a A T m n)
      | inr t =>
        have hcb := (hGspec (Mi a b (l k)) (hpat _ hlk)).2
          (selectedAllMinorHeight a A T) (fun j r =>
            selected_curvature_minor_bound hba hmem hsT (hG hlk) j.isLt r.isLt)
        have hcurB (r : Fin 3) : |cc k r ^ m| ≤ (Bx : ℤ) :=
          (lattice_curvature_power_le hp0 (hcb r)).trans
            (by exact_mod_cast le_latticeJointBoxHeight_curvature p a A T m n)
        fin_cases t
        · exact hcurB 0
        · exact hcurB 1
        · exact hcurB 2
        · change |(J k : ℤ) ^ n| ≤ _
          rw [abs_pow, abs_of_nonneg (Int.natCast_nonneg _)]
          have h1 : (J k : ℤ) ^ n ≤ (selectedRankFiveHeight a A T : ℤ) ^ n :=
            pow_le_pow_left₀ (Int.natCast_nonneg _) (by exact_mod_cast hJheight k) n
          exact h1.trans (by exact_mod_cast le_latticeJointBoxHeight_rankFive p a A T m n)
    exact_mod_cast hZ
  have hSpts : ∀ w ∈ Sz, (fun t => (w t : ℚ)) ∈ coordinateZeroLocus I' := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := mem_image.mp hw
    have hlk := hl k
    have hlkP := (facts _ hlk).1
    apply (matrix_coordinate_zeroLocus Cb hCb _ _).mpr
    have hcast : (fun t => (z k t : ℚ)) =
        Sum.elim (fun t => (y k.val t : ℚ)) (fun j => (latticePowers (cc k) (J k) m n j : ℚ)) := by
      funext t; cases t <;> rfl
    rw [hcast, nodeBlockMatrix_mulVec]
    have hnode : Bq *ᵥ (fun t => (y k.val t : ℚ)) = orbitFreeNodesQ a b (l k) := by
      rw [← integer_matrix_mulVec_cast, ← (hnodes k.val k.property).2, ← hkl k]
      exact gapNodes_kap a b (l k)
    rw [hnode, orbitLinearJointGraph_congr (hθ _ hlk)]
    apply orbitLinearJointGraph_point hba (by omega) Gm m n I (hz _ hlk) (hJ k)
    have h := (hGspec (Mi a b (l k)) (hpat _ hlk)).1
    rw [firstThree_Mi a b (l k)] at h
    exact h
  have hc := hcount I' hprime δ hdlo hdhi hd' (Bx : ℝ) hB Sz hSbox hSpts
  rwa [hScard] at hc

/-- The logarithm costs a proved subpolynomial factor. -/
theorem selected_latticeJointGraph_gap_count_slow (m n lo hi : ℕ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 0 < T →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ δ : ℕ, lo ≤ δ ∧ δ ≤ hi ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace (orbitLinearJointGraphIdeal
            (patternCurvatureMatrix (plk (Mi a b i))) a b i m n I) k) : ℤ) =
              (δ : ℤ) * k + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, plk (Mi a b l) = plk (Mi a b i)) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
            (latticeJointBoxHeight (plk (Mi a b i)) a A T m n : ℝ) ^ (1 / (lo : ℝ)) := by
  obtain ⟨C, hC, hcount⟩ := selected_latticeJointGraph_gap_count m n lo hi hlo hlohi
  let M := ⌈C * 2⌉₊ + 1
  have hM : C * 2 ≤ (M : ℝ) := by
    exact (Nat.le_ceil _).trans (by simp only [M, Nat.cast_add, Nat.cast_one]; linarith)
  have hMs : SlowGrowth (fun _ : ℕ => M) := by
    intro η hη
    refine ⟨M, by dsimp [M]; positivity, fun a ha => ?_⟩
    have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    exact le_mul_of_one_le_right (Nat.cast_nonneg M) hp
  refine ⟨fun a => M * (Nat.log 2 ((10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1))) + 1),
    hMs.mul (polynomial_log_slow ((10 ^ 25) ^ (m + n + 1)) (15 * (m + n + 1))), ?_⟩
  intro a b s T A i hba hmem hsT hT I hI hd G hG hpat hz
  have ha : 1 ≤ a := by omega
  have hA : A ≤ a := by
    have := (hmem 0 hT).1
    have := (orb_le a b (s + 0)).trans hba.le
    omega
  set Bx := latticeJointBoxHeight (plk (Mi a b i)) a A T m n
  let L := Nat.log 2 ((10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1))) + 1
  have hlog : Real.log (Bx : ℝ) + 1 ≤ 2 * (L : ℝ) :=
    box_log_le_polynomial_log (latticeJointBoxHeight_pos _ a A T m n)
      (latticeJointBoxHeight_polynomial ha hA m n)
  calc ((G.image (kap a b)).card : ℝ) ≤
        C * (Bx : ℝ) ^ (1 / (lo : ℝ)) * (Real.log (Bx : ℝ) + 1) :=
      hcount hba hmem hsT I hI hd G hG hpat hz
    _ ≤ C * (Bx : ℝ) ^ (1 / (lo : ℝ)) * (2 * L) := by gcongr
    _ = (C * 2) * L * (Bx : ℝ) ^ (1 / (lo : ℝ)) := by ring
    _ ≤ (M : ℝ) * L * (Bx : ℝ) ^ (1 / (lo : ℝ)) := by gcongr
    _ = _ := by simp only [Nat.cast_mul, L]

end
end PierceLengthBound.FixedDividend
