module

public import AffineCurveCounting.LocalDeterminant
import all ArithmeticHeights.BombieriVaaler
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Block

/-! Combining maximal-minor divisibility across row blocks. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Matrix Module Finset

/-- Every integer matrix factors through a square matrix with the same column
lattice. The two factorizations record both inclusions without rank hypotheses. -/
theorem integer_square_column_factorization {k N : ℕ} (A : Matrix (Fin k) (Fin N) ℤ) :
    ∃ (B : Matrix (Fin k) (Fin k) ℤ) (R : Matrix (Fin k) (Fin N) ℤ)
      (C : Matrix (Fin N) (Fin k) ℤ), A = B * R ∧ B = A * C := by
  classical
  let L := LinearMap.range A.mulVecLin
  obtain ⟨r, snf⟩ := L.smithNormalForm (Pi.basisFun ℤ (Fin k))
  let T : (Fin k → ℤ) →ₗ[ℤ] L :=
    { toFun := fun x => snf.bN.equivFun.symm (fun i => snf.bM.repr x (snf.f i))
      map_add' := by
        intro x y
        rw [← map_add]
        congr 1
        ext i
        exact congrArg (fun v : Fin k →₀ ℤ => v (snf.f i)) (snf.bM.repr.map_add x y)
      map_smul' := by
        intro a x
        rw [← map_smul]
        congr 1
        ext i
        exact congrArg (fun v : Fin k →₀ ℤ => v (snf.f i)) (snf.bM.repr.map_smul a x) }
  have hT : Function.Surjective T := by
    intro y
    refine ⟨∑ i : Fin r, snf.bN.repr y i • snf.bM (snf.f i), ?_⟩
    change snf.bN.equivFun.symm _ = y
    apply (snf.bN.equivFun.symm_apply_eq).mpr
    funext j
    simp only [map_sum, map_smul, Basis.repr_self]
    simp [Basis.equivFun_apply]
    simp [Finsupp.single_apply, snf.f.injective.eq_iff]
  let B := LinearMap.toMatrix' (L.subtype.comp T)
  have hB (x : Fin k → ℤ) : B *ᵥ x = (T x : Fin k → ℤ) := by
    exact LinearMap.toMatrix'_mulVec (L.subtype.comp T) x
  have hAcol (j : Fin N) : A.col j ∈ L := by
    rw [show L = LinearMap.range A.mulVecLin from rfl, Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hR : ∀ j : Fin N, ∃ x : Fin k → ℤ, B *ᵥ x = A.col j := by
    intro j
    obtain ⟨x, hx⟩ := hT ⟨A.col j, hAcol j⟩
    exact ⟨x, (hB x).trans (congrArg Subtype.val hx)⟩
  choose R hR using hR
  have hC : ∀ j : Fin k, ∃ x : Fin N → ℤ, A *ᵥ x = B.col j := by
    intro j
    have hcol : B.col j = (T (Pi.single j 1) : Fin k → ℤ) := by
      simpa using hB (Pi.single j 1)
    rw [hcol]
    exact (T (Pi.single j 1)).property
  choose C hC using hC
  refine ⟨B, (fun i j => R j i), (fun i j => C j i), ?_, ?_⟩
  · ext i j
    exact (congrFun (hR j) i).symm
  · ext i j
    exact (congrFun (hC j) i).symm

/-- Divisibility of all maximal minors passes to the square column factor. -/
theorem dvd_det_square_column_factor {k N : ℕ} (A : Matrix (Fin k) (Fin N) ℤ)
    (C : Matrix (Fin N) (Fin k) ℤ) (d : ℤ)
    (hd : ∀ c : Fin k ↪o Fin N, d ∣ (A.submatrix id c).det) :
    d ∣ (A * C).det := by
  rw [Matrix.det_mul_eq_sum_det_submatrix]
  apply Finset.dvd_sum
  intro s _
  exact dvd_mul_of_dvd_left (hd _) _


lemma det_dependent_blockDiagonal {c : ℕ} (n : Fin c → ℕ)
    (B : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℤ) :
    (Matrix.blockDiagonal' B).det = ∏ i, (B i).det := by
  rw [(Matrix.blockTriangular_blockDiagonal' B).det_fintype]
  apply Finset.prod_congr rfl
  intro i _
  let e := (Equiv.sigmaSubtype (β := fun j => Fin (n j)) i).symm
  have he : ((Matrix.blockDiagonal' B).toSquareBlock Sigma.fst i).submatrix e e = B i := by
    ext j k
    exact Matrix.blockDiagonal'_apply_eq B i j k
  rw [← he, Matrix.det_submatrix_equiv_self]

/-- The product of common divisors of the maximal minors of disjoint row blocks
is a divisor of the full determinant. Empty and rank-deficient blocks are allowed. -/
theorem block_minor_divisors_dvd_det {c : ℕ} (n : Fin c → ℕ)
    (A : Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℤ) (d : Fin c → ℤ)
    (hd : ∀ i, ∀ j : Fin (n i) ↪o Fin (Fintype.card (Σ i, Fin (n i))),
      d i ∣ (A.submatrix (Sigma.mk i) ((Fintype.equivFin _).symm ∘ j)).det) :
    (∏ i, d i) ∣ A.det := by
  classical
  let e := Fintype.equivFin (Σ i, Fin (n i))
  let M := fun i => A.submatrix (Sigma.mk i) e.symm
  choose B R C hR hC using fun i => integer_square_column_factorization (M i)
  have hdiv (i : Fin c) : d i ∣ (B i).det := by
    rw [hC i]
    apply dvd_det_square_column_factor
    intro j
    exact hd i j
  let Q : Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℤ :=
    fun i j => R i.1 i.2 (e j)
  have hfac : Matrix.blockDiagonal' B * Q = A := by
    ext ⟨i, j⟩ l
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.blockDiagonal'_apply_eq]
      have hh := (congrArg (fun m => m j (e l)) (hR i)).symm
      simpa only [M, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.mul_apply, Q] using hh
    · intro k _ hki
      apply Finset.sum_eq_zero
      intro t _
      rw [Matrix.blockDiagonal'_apply_ne B j t hki.symm, zero_mul]
    · simp
  rw [← hfac, Matrix.det_mul, det_dependent_blockDiagonal]
  exact dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hdiv i)) _

/-- The residue-class exponents add in the determinant valuation. -/
theorem block_prime_powers_dvd_det {c : ℕ} (n : Fin c → ℕ)
    (A : Matrix (Σ i, Fin (n i)) (Σ i, Fin (n i)) ℤ) (p : ℤ) (e : Fin c → ℕ)
    (he : ∀ i, ∀ j : Fin (n i) ↪o Fin (Fintype.card (Σ i, Fin (n i))),
      p ^ e i ∣ (A.submatrix (Sigma.mk i) ((Fintype.equivFin _).symm ∘ j)).det) :
    p ^ (∑ i, e i) ∣ A.det := by
  simpa only [Finset.prod_pow_eq_pow_sum] using
    block_minor_divisors_dvd_det n A (fun i => p ^ e i) he


/-- Enumerate rows grouped by their residue-class label. -/
def partitionRowEquiv {c s : ℕ} (label : Fin s → Fin c) :
    (Σ i : Fin c, Fin (Fintype.card {j : Fin s // label j = i})) ≃ Fin s :=
  (Equiv.sigmaCongrRight fun i =>
    (Fintype.equivFin {j : Fin s // label j = i}).symm).trans (Equiv.sigmaFiberEquiv label)

def residueRows {c s : ℕ} (label : Fin s → Fin c) (i : Fin c) :
    Fin (Fintype.card {j : Fin s // label j = i}) → Fin s :=
  fun j => ((Fintype.equivFin {j : Fin s // label j = i}).symm j).val

lemma sum_residue_class_sizes {c s : ℕ} (label : Fin s → Fin c) :
    (∑ i : Fin c, Fintype.card {j : Fin s // label j = i}) = s := by
  have h := Fintype.card_congr (partitionRowEquiv label)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using h

/-- Divisibility of all local block minors combines for an arbitrary row
partition, without any assumption on the ordering of residue classes. -/
theorem residue_minor_divisors_dvd_det {c s : ℕ}
    (A : Matrix (Fin s) (Fin s) ℤ) (label : Fin s → Fin c) (d : Fin c → ℤ)
    (hd : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin s,
      d i ∣ (A.submatrix (residueRows label i) j).det) :
    (∏ i, d i) ∣ A.det := by
  classical
  let e := partitionRowEquiv label
  rw [← Matrix.det_submatrix_equiv_self e A]
  apply block_minor_divisors_dvd_det
  intro i j
  exact hd i (e ∘ (Fintype.equivFin _).symm ∘ j)

/-- The same product divides the gcd of all maximal minors of a rectangular
matrix, as required by the Bombieri--Vaaler bound. -/
theorem residue_minor_divisors_dvd_minorGcd {c s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℤ) (label : Fin s → Fin c) (d : Fin c → ℤ)
    (hd : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin N,
      d i ∣ (A.submatrix (residueRows label i) j).det) :
    (∏ i, d i) ∣ Int.Matrix.minorGcd A := by
  classical
  unfold Int.Matrix.minorGcd
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  apply residue_minor_divisors_dvd_det _ label d
  intro i j
  exact hd i _

theorem residue_prime_powers_dvd_minorGcd {c s N : ℕ}
    (A : Matrix (Fin s) (Fin N) ℤ) (label : Fin s → Fin c)
    (p : ℤ) (e : Fin c → ℕ)
    (he : ∀ i, ∀ j : Fin (Fintype.card {j : Fin s // label j = i}) → Fin N,
      p ^ e i ∣ (A.submatrix (residueRows label i) j).det) :
    p ^ (∑ i, e i) ∣ Int.Matrix.minorGcd A := by
  simpa only [Finset.prod_pow_eq_pow_sum] using
    residue_minor_divisors_dvd_minorGcd A label (fun i => p ^ e i) he

end
end AffineCurveCounting
