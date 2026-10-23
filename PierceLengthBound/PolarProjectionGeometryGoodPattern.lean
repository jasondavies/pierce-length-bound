/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountSlow
public import PierceLengthBound.PolarProjectionCountAssembly
public import PierceLengthBound.PolarProjectionRetainedDegree
public import PierceLengthBound.BranchSievePatternCount

/-! Good patterns are defined by irreducibility of an explicit polynomial
and nonvanishing of one fixed proper exceptional polynomial. Their geometric
contribution is proved here; only the arithmetic count of reducible label
specializations remains an input to the global counting estimate. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
noncomputable section

section
open MvPolynomial Finset

/-! The proper algebraic degeneracy locus is included in the actual bad-pattern
count, together with any previously counted specialization exceptions. -/

/-- Combining two good-pattern conditions adds their bad-pattern coefficients. -/
theorem PolarBadPatternCount.inter
    {good₁ good₂ : ℕ → (Fin 10 → ℤ) → Prop} {R₁ R₂ : ℕ → ℕ}
    (h₁ : PolarBadPatternCount good₁ R₁) (h₂ : PolarBadPatternCount good₂ R₂) :
    PolarBadPatternCount (fun a p => good₁ a p ∧ good₂ a p) (fun a => R₁ a + R₂ a) := by
  classical
  intro a b s T A hba hmem hsT hT
  let S := (selectedStarts a b s T A).image (fun i => plk (Mi a b i))
  have hsub : S.filter (fun p => ¬ (good₁ a p ∧ good₂ a p)) ⊆
      S.filter (fun p => ¬ good₁ a p) ∪ S.filter (fun p => ¬ good₂ a p) := by
    intro p hp
    obtain ⟨hp, hn⟩ := mem_filter.mp hp
    by_cases hgood : good₁ a p
    · exact mem_union_right _ (mem_filter.mpr ⟨hp, fun h => hn ⟨hgood, h⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, hgood⟩)
  have hcard : ((S.filter (fun p => ¬ (good₁ a p ∧ good₂ a p))).card : ℝ) ≤
      (S.filter (fun p => ¬ good₁ a p)).card + (S.filter (fun p => ¬ good₂ a p)).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have hcount₁ := h₁ hba hmem hsT hT
  have hcount₂ := h₂ hba hmem hsT hT
  have hsum := hcard.trans (add_le_add hcount₁ hcount₂)
  simpa only [S, Nat.cast_add, add_mul] using hsum

/-- The complement of any proper fixed hypersurface has the required actual
bad-pattern bound with a slowly growing coefficient. -/
theorem polarBadPatternCount_hypersurface {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      PolarBadPatternCount (fun _ p => eval (fun j => (p j : ℚ)) F ≠ 0) R := by
  obtain ⟨R, hR, hcount⟩ := selected_hypersurface_pattern_count_slow hF
  refine ⟨R, hR, ?_⟩
  intro a b s T A hba hmem hsT hT
  simpa only [not_not] using hcount hba hmem hsT hT

/-- Adding the new proper algebraic degeneracy locus to a counted branch-sieve
exception class preserves the exact 14/3 pattern exponent. -/
theorem polarBadPatternCount_add_hypersurface
    {good : ℕ → (Fin 10 → ℤ) → Prop} {R : ℕ → ℕ}
    (hR : SlowGrowth R) (hbad : PolarBadPatternCount good R)
    {F : MvPolynomial (Fin 10) ℚ} (hF : ProperOnMinorCone F) :
    ∃ R' : ℕ → ℕ, SlowGrowth R' ∧
      PolarBadPatternCount
        (fun a p => good a p ∧ eval (fun j => (p j : ℚ)) F ≠ 0) R' := by
  obtain ⟨R₂, hR₂, hbad₂⟩ := polarBadPatternCount_hypersurface hF
  exact ⟨fun a => R a + R₂ a, slowGrowth_add hR hR₂, hbad.inter hbad₂⟩

end

/-- The branch label polynomial depends only on the dividend and full minor
pattern, with a rational choice of primitive-element slope. -/
def patternBranchLabelPolynomial (a : ℕ) (p : Fin 10 → ℤ) (c : ℚ) : Polynomial ℚ :=
  let q := polarMinorParameters (fun j => (p j : ℚ))
  branchResultantLabel (a : ℚ) (p 0 : ℚ) c (-q 0 - q 1) (q 1 - q 2) (q 2 - 1)

theorem patternBranchLabelPolynomial_orbit (a b i : ℕ) (c : ℚ) :
    patternBranchLabelPolynomial a (plk (Mi a b i)) c = orbitBranchLabelPolynomial a b i c := by
  have hA : Lz a b i = plk (Mi a b i) 0 := by
    simpa [theta, projθ] using congrFun (theta_eq (a := a) (b := b) i) 0
  simp only [patternBranchLabelPolynomial, ← orbitPolarParameters_eq_minor]
  simp [orbitPolarParameters, orbitBranchLabelPolynomial, hA]

/-- A full pattern is branch-good when some explicit label polynomial is
irreducible of degree twelve. No component-degree conclusion is part of this
definition. -/
def PolarBranchGood (a : ℕ) (p : Fin 10 → ℤ) : Prop :=
  ∃ c : ℚ, Irreducible (patternBranchLabelPolynomial a p c) ∧
    (patternBranchLabelPolynomial a p c).natDegree = 12

/-- The rational branch label in the four integer vertex coordinates. -/
def branchVertexLabelPolynomial (a : ℕ) (x : Fin 4 → ℤ) (c : ℚ) : Polynomial ℚ :=
  branchResultantLabel (a : ℚ) (x 0 : ℚ) c
    (-((x 3 : ℚ) + x 2) / x 0) (((x 2 : ℚ) + x 1) / x 0)
    (-((x 1 : ℚ) + x 0) / x 0)

def branchVertexGood (a : ℕ) (x : Fin 4 → ℤ) : Prop :=
  ∃ c : ℚ, Irreducible (branchVertexLabelPolynomial a x c) ∧
    (branchVertexLabelPolynomial a x c).natDegree = 12

theorem patternBranchLabelPolynomial_eq_vertex {a : ℕ} {p : Fin 10 → ℤ}
    (hp : p 0 ≠ 0) (c : ℚ) :
    patternBranchLabelPolynomial a p c =
      branchVertexLabelPolynomial a (branchFirstVertex p) c := by
  have hpQ : (p 0 : ℚ) ≠ 0 := by exact_mod_cast hp
  unfold patternBranchLabelPolynomial branchVertexLabelPolynomial
  simp only [polarMinorParameters, branchFirstVertex, branchFirstIndex, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  congr 1 <;> field_simp <;> ring

theorem polarBranchGood_iff_vertex {a : ℕ} {p : Fin 10 → ℤ} (hp : p 0 ≠ 0) :
    PolarBranchGood a p ↔ branchVertexGood a (branchFirstVertex p) := by
  simp only [PolarBranchGood, branchVertexGood, patternBranchLabelPolynomial_eq_vertex hp]

/-- Explicit branch irreducibility and the two local polynomial conditions
already imply the geometric input used in the point count. -/
theorem polarRetainedDegree_of_branch_good (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    PolarRetainedDegree m n (fun a p => PolarBranchGood a p ∧
      polarChartGuard (polarMinorParameters (fun j => (p j : ℚ))) ≠ 0 ∧
      polarInitialMinor (polarMinorParameters (fun j => (p j : ℚ))) ≠ 0) := by
  intro a b i d δ hba hi hne hgood I hI hf hg hz hnorm hres hcut hd hd24 hdegree hgraph
  let : I.IsPrime := hI
  obtain ⟨⟨c, hirr, hdeg⟩, hguard, hminor⟩ := hgood
  rw [patternBranchLabelPolynomial_orbit] at hirr hdeg
  rw [← orbitPolarParameters_eq_minor] at hguard hminor
  obtain ⟨N, c₀, hdegree⟩ := hdegree
  have hG : IsUnit (patternCurvatureMatrix (plk (Mi a b i))).det :=
    isUnit_iff_ne_zero.mpr (patternCurvature_spec
      (orbit_pattern_first hba (by omega)) ⟨Mi a b i, rfl⟩).1
  have h := retained_polar_linearJointGraph_degree_of_irreducible_label
    (patternCurvatureMatrix (plk (Mi a b i))) hG hm hn hba hi hne I hf hg hz
    hnorm hres hcut hguard hminor (by omega) hd24 hdegree hgraph c hirr hdeg
  simpa only [polarProjectionGraphDegree, Nat.add_comm] using h

/-- One fixed proper full-minor polynomial suffices for all local geometric
exclusions, for every dividend and every choice of powers. -/
theorem exists_polar_geometric_good_polynomial :
    ∃ Θ : MvPolynomial (Fin 10) ℚ, ProperOnMinorCone Θ ∧
      ∀ m n : ℕ, 0 < m → 0 < n →
        PolarRetainedDegree m n (fun a p => PolarBranchGood a p ∧
          eval (fun j => (p j : ℚ)) Θ ≠ 0) := by
  obtain ⟨Θ, hΘ, hgood⟩ := exists_polar_full_minor_exceptional_polynomial
  refine ⟨Θ, hΘ, ?_⟩
  intro m n hm hn a b i d δ hba hi hne hp
  have hg := hgood (fun j => (plk (Mi a b i) j : ℚ)) hp.2
  exact polarRetainedDegree_of_branch_good m n hm hn hba hi hne
    ⟨hp.1, hg.2.2.1, hg.2.2.2⟩

/-- The entire geometric and pattern-count assembly reduces to the arithmetic
bound for reducible degree-twelve branch-label specializations. -/
theorem polar_six_term_of_branch_bad_pattern_count (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {Rbad : ℕ → ℕ} (hRbad : SlowGrowth Rbad)
    (hbad : PolarBadPatternCount PolarBranchGood Rbad) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PolarProjectionSixTermEstimate m n R := by
  obtain ⟨Θ, hΘ, hdegree⟩ := exists_polar_geometric_good_polynomial
  obtain ⟨R', hR', hbad'⟩ := polarBadPatternCount_add_hypersurface hRbad hbad hΘ
  exact polar_six_term_of_retained_degree m n hm hn _ (hdegree m n hm hn) hR' hbad'

end
end PierceLengthBound.FixedDividend
