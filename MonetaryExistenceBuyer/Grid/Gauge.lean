import MonetaryExistenceBuyer.Grid.Defs
import MonetaryExistenceBuyer.Model

/-!
# The uniform value bound (`lem:gauge`)

Both the continuum version (concave `V` on `ℝ₊`) and the grid version (discretely concave `V`
on `𝒳`, grid transfers) of `σ V(b) ≤ u(V(b))`, hence `V ≤ L_*`.
-/

open Set Finset MeasureTheory

noncomputable section

namespace Molico

/-- `lem:gauge`, grid version. -/
theorem gauge_grid (P : Primitives) {N : ℕ} {V η : ℕ → ℝ} (hV : IncrSeq V N) (hV0 : V 0 = 0)
    (hη0 : ∀ l, 0 ≤ η l) (hη1 : ∑ l ∈ range (N + 1), η l = 1)
    (hbell : ∀ m ≤ N, V m = Grid.gT P.U.u P.β N η V m) {m : ℕ} (hm : m ≤ N) :
    P.σ * V m ≤ P.U.u (V m) ∧ V m ≤ P.Lstar := by
  have hle : V m ≤ P.β * (P.U.u (V m) + V m) := by
    conv_lhs => rw [hbell m hm, Grid.gT]
    refine mul_le_mul_of_nonneg_left ?_ P.β_pos.le
    calc ∑ l ∈ range (N + 1), η l * Grid.gH P.U.u N V m l
        ≤ ∑ l ∈ range (N + 1), η l * (P.U.u (V m) + V m) := by
          refine Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left ?_ (hη0 l)
          exact Grid.gH_le P.U hV hV0 hm (by rw [Finset.mem_range] at hl; omega)
      _ = P.U.u (V m) + V m := by rw [← Finset.sum_mul, hη1, one_mul]
  have h1 : P.σ * V m ≤ P.U.u (V m) := by
    have hβ := P.β_eq
    have hσ := P.σ_pos
    rw [hβ] at hle
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith)] at hle
    linarith
  exact ⟨h1, P.le_Lstar_of_σ_mul_le (hV.nonneg hV0 hm) h1⟩

/-- `lem:gauge`, continuum version. -/
theorem gauge_cont (P : Primitives) {V : ℝ → ℝ} {η : Measure ℝ} [IsProbabilityMeasure η]
    (hη : η (Iio 0) = 0) (hV : IsValueFn V) (hbell : ∀ m, 0 ≤ m → V m = bellT P.U.u P.β η V m)
    {b : ℝ} (hb : 0 ≤ b) : P.σ * V b ≤ P.U.u (V b) ∧ V b ≤ P.Lstar := by
  have hae : ∀ᵐ s ∂η, 0 ≤ s := by
    rw [ae_iff]
    have e : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [e]; exact hη
  have hle : V b ≤ P.β * (P.U.u (V b) + V b) := by
    conv_lhs => rw [hbell b hb, bellT]
    refine mul_le_mul_of_nonneg_left ?_ P.β_pos.le
    have := integral_mono_of_nonneg (μ := η) (f := fun s => bellH P.U.u V b s)
      (g := fun _ => P.U.u (V b) + V b)
      (by filter_upwards [hae] with s hs; exact bellH_nonneg P.U hV hb hs)
      (integrable_const _)
      (by filter_upwards [hae] with s hs; exact bellH_le P.U hV hb hs)
    simpa using this
  have h1 : P.σ * V b ≤ P.U.u (V b) := by
    have hβ := P.β_eq
    have hσ := P.σ_pos
    rw [hβ] at hle
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith)] at hle
    linarith
  exact ⟨h1, P.le_Lstar_of_σ_mul_le (hV.nonneg hb) h1⟩

end Molico
