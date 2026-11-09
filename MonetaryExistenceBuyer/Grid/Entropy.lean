import MonetaryExistenceBuyer.Grid.Defs

/-!
# Share entropy (`lem:entropy`)

For an approximant equilibrium with joint meeting measure `Γ` and size-biased meeting law
`Λ = (b+s) Γ / (2M)` (`def:sizebias`), the binary share entropy
`χ(x) = x log x + (1-x) log(1-x)` is conserved on average:
`∫ [χ(r̂) - χ(r)] dΛ = 0`, where `r = b/(b+s)` and `r̂ = B/(b+s)` are the buyer's pre- and
post-trade wealth shares.

In Lean, `Real.log 0 = 0`, so `χ 0 = χ 1 = 0` automatically.
-/

open Finset

noncomputable section

namespace Molico

/-- `χ(x) = x log x + (1-x) log(1-x)`. -/
def χ (x : ℝ) : ℝ := x * Real.log x + (1 - x) * Real.log (1 - x)

/-- The integrand `(b + s) [χ(r̂) - χ(r)]` of the size-biased entropy balance at a meeting with
buyer index `m`, seller index `l`, transfer index `j`, mesh `h`. -/
def entropyIntegrand (h : ℝ) (m l j : ℕ) : ℝ :=
  let b : ℝ := m * h
  let s : ℝ := l * h
  let B : ℝ := ((m - j : ℕ) : ℝ) * h
  (b + s) * (χ (B / (b + s)) - χ (b / (b + s)))

/-! ### Pointwise identity -/

/-- `x log (x / T) = x log x - x log T` for `T ≠ 0` (trivially true at `x = 0`). -/
lemma mul_log_div_eq (x T : ℝ) (hT : T ≠ 0) :
    x * Real.log (x / T) = x * Real.log x - x * Real.log T := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hx hT]; ring

/-- `T χ(x/T) = x log x + y log y - T log T` when `x + y = T ≠ 0`. -/
lemma mul_χ_div (x y T : ℝ) (hT : T ≠ 0) (hxy : x + y = T) :
    T * χ (x / T) = x * Real.log x + y * Real.log y - T * Real.log T := by
  have h1 : 1 - x / T = y / T := by
    rw [eq_div_iff hT, sub_mul, one_mul, div_mul_cancel₀ x hT]; linarith
  have h2 : T * (x / T) = x := by field_simp
  have h3 : T * (y / T) = y := by field_simp
  unfold χ
  rw [h1, mul_add, ← mul_assoc, ← mul_assoc, h2, h3, mul_log_div_eq x T hT,
    mul_log_div_eq y T hT, ← hxy]
  ring

/-- `(b + s) [χ(B/(b+s)) - χ(b/(b+s))] = φ(B) + φ(S) - φ(b) - φ(s)` with `φ(x) = x log x`,
whenever `B + S = b + s` (all reals; the case `b + s = 0` uses `log (-x) = log x`). -/
lemma entropy_pointwise (B S b s : ℝ) (hT : B + S = b + s) :
    (b + s) * (χ (B / (b + s)) - χ (b / (b + s))) =
      (B * Real.log B + S * Real.log S) - (b * Real.log b + s * Real.log s) := by
  by_cases h0 : b + s = 0
  · have hS : S = -B := by linarith
    have hs : s = -b := by linarith
    rw [h0, hS, hs, Real.log_neg_eq_log, Real.log_neg_eq_log]; ring
  · rw [mul_sub, mul_χ_div B S (b + s) h0 hT, mul_χ_div b s (b + s) h0 rfl]; ring

/-- `φ(k h) = (k h) log (k h)` in index form. -/
def gphi (h : ℝ) (k : ℕ) : ℝ := ((k : ℝ) * h) * Real.log ((k : ℝ) * h)

lemma entropyIntegrand_eq {N m l j : ℕ} (hm : m ≤ N) (hl : l ≤ N) (hj : j ∈ Grid.feas N m l)
    (h : ℝ) :
    entropyIntegrand h m l j = (gphi h (m - j) + gphi h (l + j)) - (gphi h m + gphi h l) := by
  rw [Grid.mem_feas hm hl] at hj
  unfold entropyIntegrand gphi
  exact entropy_pointwise (((m - j : ℕ) : ℝ) * h) (((l + j : ℕ) : ℝ) * h) ((m : ℝ) * h)
    ((l : ℝ) * h) (by push_cast [hj.1]; ring)

/-- `lem:entropy`, eq. `eq:entropy`: `∫ [χ(r̂) - χ(r)] dΛ = 0` with
`Λ = (b + s) Γ / (2M)`. -/
theorem entropy {P : Primitives} {h : ℝ} {N : ℕ} {V η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ}
    (hE : Grid.IsApproxEq P h N V η κ) :
    (2 * P.M)⁻¹ * ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), ∑ j ∈ Grid.feas N m l,
      η m * η l * κ m l j * entropyIntegrand h m l j = 0 := by
  obtain ⟨_, hlaw, hκ, _, _, hstat⟩ := hE
  -- Step 1: rewrite the integrand as a difference of `φ` at landing and starting points.
  have e : ∀ m ∈ range (N + 1), ∀ l ∈ range (N + 1), ∑ j ∈ Grid.feas N m l,
      η m * η l * κ m l j * entropyIntegrand h m l j =
      ∑ j ∈ Grid.feas N m l, η m * η l * κ m l j * (gphi h (m - j) + gphi h (l + j)) -
        η m * η l * (gphi h m + gphi h l) := by
    intro m hm l hl
    have hm' := mem_range.1 hm
    have hl' := mem_range.1 hl
    calc ∑ j ∈ Grid.feas N m l, η m * η l * κ m l j * entropyIntegrand h m l j
        = ∑ j ∈ Grid.feas N m l, (η m * η l * κ m l j * (gphi h (m - j) + gphi h (l + j)) -
            η m * η l * κ m l j * (gphi h m + gphi h l)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [entropyIntegrand_eq (by omega) (by omega) hj, mul_sub]
      _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
            hκ.sum_one m (by omega) l (by omega), mul_one]
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl => e m hm l hl]
  simp_rw [Finset.sum_sub_distrib]
  -- Step 2: post-trade side, via stationarity `η = Ψ_κ(η)`.
  have h2 : ∑ k ∈ range (N + 1), η k * gphi h k =
      ∑ k ∈ range (N + 1), Grid.gPsi N η κ k * gphi h k :=
    Finset.sum_congr rfl fun k hk => by rw [← hstat k (by rw [mem_range] at hk; omega)]
  have h1 : ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), ∑ j ∈ Grid.feas N m l,
      η m * η l * κ m l j * (gphi h (m - j) + gphi h (l + j)) =
      2 * ∑ k ∈ range (N + 1), η k * gphi h k := by
    rw [h2, Grid.sum_gPsi_mul, ← mul_assoc, show (2:ℝ) * 2⁻¹ = 1 by norm_num, one_mul]
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl =>
      Finset.sum_congr rfl fun j hj => ?_
    rw [Grid.landing_sum hm hl hj (gphi h)]
  -- Step 3: pre-trade side, via `∑ η = 1`.
  have h3 : ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), η m * η l * (gphi h m + gphi h l) =
      2 * ∑ k ∈ range (N + 1), η k * gphi h k := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have e1 : ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), η m * η l * gphi h m =
        ∑ m ∈ range (N + 1), η m * gphi h m := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum, hlaw.sum_one]; ring
    have e2 : ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), η m * η l * gphi h l =
        ∑ l ∈ range (N + 1), η l * gphi h l := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul, hlaw.sum_one]; ring
    rw [e1, e2]; ring
  rw [h1, h3, sub_self, mul_zero]

end Molico
