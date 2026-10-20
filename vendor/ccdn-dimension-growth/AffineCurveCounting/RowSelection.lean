module

public import AffineCurveCounting.RowSpan

/-! Independent rows can be selected from the actual finite evaluation matrix.
A nonzero annihilator gives the strict rank deficiency required by Bombieri--Vaaler. -/

@[expose] public section
namespace AffineCurveCounting
open Matrix

theorem exists_independent_spanning_rows {t N : ℕ} (A : Matrix (Fin t) (Fin N) ℚ) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧
      LinearIndependent ℚ (A.submatrix a id).row ∧
      Submodule.span ℚ (Set.range (A.submatrix a id).row) =
        Submodule.span ℚ (Set.range A.row) ∧ s ≤ N := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' ℚ A.row
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let e := (Fintype.equivFin κ).symm
  have hli : LinearIndependent ℚ (A.submatrix (a ∘ e) id).row := by
    exact hi.comp e e.injective
  have hspan : Set.range (A.submatrix (a ∘ e) id).row = Set.range (A.row ∘ a) := by
    change Set.range ((A.row ∘ a) ∘ e) = _
    exact e.surjective.range_comp _
  refine ⟨Fintype.card κ, a ∘ e, ha.comp e.injective, hli, ?_, ?_⟩
  · rw [hspan, hs]
  · simpa using hli.fintype_card_le_finrank

/-- A nonzero relation on all columns forces every independent row family
to contain strictly fewer rows than columns. -/
theorem independent_rows_lt_of_kernel {s N : ℕ} (A : Matrix (Fin s) (Fin N) ℚ)
    (hA : LinearIndependent ℚ A.row) (v : Fin N → ℚ) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) : s < N := by
  have hle : s ≤ N := by simpa using hA.fintype_card_le_finrank
  by_contra h
  have he : s = N := by omega
  by_cases hs : s = 0
  · have hN : N = 0 := by omega
    apply hv
    funext j
    have hj := j.isLt
    omega
  let : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  have hspan : Submodule.span ℚ (Set.range A.row) = ⊤ :=
    hA.span_eq_top_of_card_eq_finrank (by simpa using he)
  apply hv
  funext j
  have hz := dotProduct_eq_zero_of_mem_span A v hker
    (r := Pi.single j 1) (by rw [hspan]; trivial)
  simpa using hz

theorem exists_independent_spanning_rows_lt {t N : ℕ}
    (A : Matrix (Fin t) (Fin N) ℚ) (v : Fin N → ℚ) (hv : v ≠ 0)
    (hker : A *ᵥ v = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧
      LinearIndependent ℚ (A.submatrix a id).row ∧
      Submodule.span ℚ (Set.range (A.submatrix a id).row) =
        Submodule.span ℚ (Set.range A.row) ∧ s < N := by
  obtain ⟨s, a, ha, hi, hs, _⟩ := exists_independent_spanning_rows A
  refine ⟨s, a, ha, hi, hs, independent_rows_lt_of_kernel _ hi v hv ?_⟩
  ext i
  exact congrFun hker (a i)

end AffineCurveCounting
