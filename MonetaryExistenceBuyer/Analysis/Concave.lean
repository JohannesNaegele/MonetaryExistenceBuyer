import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Deriv

/-!
# Elementary facts on concave nondecreasing functions on `[0, ∞)`
-/

open Set

namespace Molico

variable {f : ℝ → ℝ}

/-- Concavity through the origin: `t f(x) ≤ f(t x)` for `t ∈ [0,1]` when `f(0) ≥ 0`. -/
theorem concave_mul_le (hf : ConcaveOn ℝ (Ici 0) f) (hf0 : 0 ≤ f 0) {t x : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hx : 0 ≤ x) : t * f x ≤ f (t * x) := by
  have h := hf.2 (show x ∈ Ici (0:ℝ) from hx) (self_mem_Ici) ht0
    (show 0 ≤ 1 - t by linarith) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero] at h
  nlinarith

/-- Slope bound through the origin: `f(y) - f(x) ≤ (y - x) f(x)/x` for `0 < x ≤ y`, `f(0) ≥ 0`. -/
theorem concave_sub_le_div (hf : ConcaveOn ℝ (Ici 0) f) (hf0 : 0 ≤ f 0) {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) : f y - f x ≤ (y - x) * f x / x := by
  rcases hxy.eq_or_lt with rfl | hxy'
  · simp
  have h := hf.slope_anti_adjacent (self_mem_Ici)
    (show y ∈ Ici (0:ℝ) from by simp only [mem_Ici]; linarith) hx hxy'
  have hyx : 0 < y - x := by linarith
  rw [div_le_div_iff₀ hyx (by simpa using hx)] at h
  rw [le_div_iff₀ hx]
  nlinarith

/-- A concave nondecreasing function with values in `[0, B]` is `B/a`-Lipschitz on `[a, ∞)`. -/
theorem concave_lipschitz (hf : ConcaveOn ℝ (Ici 0) f) (hmono : MonotoneOn f (Ici 0)) {B : ℝ}
    (hB : ∀ x, 0 ≤ x → 0 ≤ f x ∧ f x ≤ B) {a : ℝ} (ha : 0 < a) {x y : ℝ} (hax : a ≤ x)
    (hxy : x ≤ y) : 0 ≤ f y - f x ∧ f y - f x ≤ B / a * (y - x) := by
  have hx : 0 < x := ha.trans_le hax
  have hy : 0 < y := hx.trans_le hxy
  refine ⟨sub_nonneg.2 (hmono (show x ∈ Ici (0:ℝ) from hx.le) (show y ∈ Ici (0:ℝ) from hy.le)
    hxy), ?_⟩
  have h1 := concave_sub_le_div hf (hB 0 le_rfl).1 hx hxy
  obtain ⟨hfx0, hfxB⟩ := hB x hx.le
  have hB0 : 0 ≤ B := hfx0.trans hfxB
  have h2 : (y - x) * f x / x ≤ (y - x) * B / x :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfxB (by linarith)) hx.le
  have h3 : (y - x) * B / x ≤ (y - x) * B / a :=
    div_le_div_of_nonneg_left (mul_nonneg (by linarith) hB0) ha hax
  calc f y - f x ≤ (y - x) * B / a := h1.trans (h2.trans h3)
    _ = B / a * (y - x) := by ring
end Molico
