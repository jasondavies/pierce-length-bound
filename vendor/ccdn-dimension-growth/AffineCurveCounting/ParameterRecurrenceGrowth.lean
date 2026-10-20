module

public import AffineCurveCounting.RationalParameterPowerSpan

/-! If a filtration is eventually generated one step at a time by a parameter,
its linear growth has slope at most the function-field degree over K(t).
Common denominators affect only the fixed additive offset in the bound. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- Eventual generation by the parameter bounds filtered dimensions with
slope equal to the rank over its rational-function field. -/
theorem parameter_recurrence_growth_bound {K A F : Type*} [Field K]
    [AddCommGroup A] [Module K A] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Module.Finite (RatFunc K) F]
    (V : ℕ → Submodule K A) [∀ n, Module.Finite K (V n)]
    (L : A →ₗ[K] A) (φ : A →ₗ[K] F) (hφ : Function.Injective φ)
    (hL : ∀ x, φ (L x) = algebraMap (RatFunc K) F RatFunc.X * φ x)
    (N : ℕ) (hrec : ∀ n ≥ N, V (n + 1) = V n ⊔ (V n).map L) :
    ∃ D : ℕ, ∀ m, Module.finrank K (V (N + m)) ≤
      Module.finrank (RatFunc K) F * (D + m + 1) := by
  classical
  let b := Module.finBasis K (V N)
  let u := algebraMap (RatFunc K) F RatFunc.X
  let v := Module.finBasis (RatFunc K) F
  obtain ⟨q, hq, D, hD⟩ := finite_family_parameter_power_span (K := K) (fun i => φ (b i).val)
  let T := (LinearMap.mulLeft K q).comp φ
  have hT (x : A) : T x = q * φ x := rfl
  have hTi : Function.Injective T := fun x y h => hφ (mul_left_cancel₀ hq h)
  have hTL (x : A) : T (L x) = u * T x := by rw [hT, hL, hT]; ring
  have hbase {x : A} (hx : x ∈ V N) : T x ∈ parameterPowerSpan K u v D := by
    have he : T x = ∑ i, b.repr ⟨x, hx⟩ i • (q * φ (b i).val) := by
      have hh := congrArg (fun z : V N => T z.val) (b.sum_repr ⟨x, hx⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hT, Finset.mul_sum, mul_smul_comm] using hh.symm
    rw [he]
    apply (parameterPowerSpan K u v D).sum_mem
    intro i _
    exact (parameterPowerSpan K u v D).smul_mem _ (hD i)
  have hbound (m : ℕ) : ∀ x ∈ V (N + m), T x ∈ parameterPowerSpan K u v (D + m) := by
    induction m with
    | zero =>
      intro x hx
      exact hbase hx
    | succ m ih =>
      intro x hx
      rw [show N + (m + 1) = (N + m) + 1 by omega, hrec (N + m) (by omega)] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨z, hz, rfl⟩ := hz
      rw [map_add, hTL]
      apply (parameterPowerSpan K u v (D + (m + 1))).add_mem
      · exact parameterPowerSpan_mono u v (by omega) (ih y hy)
      · simpa only [Nat.add_assoc] using parameterPowerSpan_mul_mem u v (D + m) (ih z hz)
  refine ⟨D, ?_⟩
  intro m
  let Tm : V (N + m) →ₗ[K] parameterPowerSpan K u v (D + m) :=
    (T.comp (V (N + m)).subtype).codRestrict _ (fun x => hbound m x.val x.property)
  have hi : Function.Injective Tm := by
    intro x y h
    apply Subtype.ext
    apply hTi
    exact congrArg Subtype.val h
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  exact hd.trans (by simpa only [Fintype.card_fin, Nat.add_assoc] using
    parameterPowerSpan_finrank_le u v (D + m))

/-- The Hilbert slope is at most the parameter extension degree whenever the
coordinate filtration has the parameter-generation recurrence. -/
theorem parameter_recurrence_slope_le {K A F : Type*} [Field K]
    [AddCommGroup A] [Module K A] [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Module.Finite (RatFunc K) F]
    (V : ℕ → Submodule K A) [∀ n, Module.Finite K (V n)]
    (L : A →ₗ[K] A) (φ : A →ₗ[K] F) (hφ : Function.Injective φ)
    (hL : ∀ x, φ (L x) = algebraMap (RatFunc K) F RatFunc.X * φ x)
    (N : ℕ) (hrec : ∀ n ≥ N, V (n + 1) = V n ⊔ (V n).map L)
    (d : ℕ) (hdegree : ∃ M : ℕ, ∃ c : ℤ, ∀ n ≥ M,
      (Module.finrank K (V n) : ℤ) = (d : ℤ) * n + c) :
    d ≤ Module.finrank (RatFunc K) F := by
  obtain ⟨D, hD⟩ := parameter_recurrence_growth_bound V L φ hφ hL N hrec
  obtain ⟨M, c, hc⟩ := hdegree
  apply eventual_linear_slope_le
    (fun m => Module.finrank K (V (N + m)))
    (fun m => Module.finrank (RatFunc K) F * (D + m + 1)) d (Module.finrank (RatFunc K) F)
  · refine ⟨M, (d : ℤ) * N + c, ?_⟩
    intro m hm
    rw [hc (N + m) (by omega)]
    push_cast
    ring
  · refine ⟨0, (Module.finrank (RatFunc K) F : ℤ) * (D + 1), ?_⟩
    intro m _
    push_cast
    ring
  · exact hD

end
end AffineCurveCounting
