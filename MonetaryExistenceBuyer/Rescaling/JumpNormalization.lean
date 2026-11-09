import MonetaryExistenceBuyer.Rescaling.Defs

/-!
# Normalization inside a jump (`cor:jumpnormalization`)

Fix a bad sequence (`def:bad`), i.e. a selected sequence whose Helly limit `V` has a jump
`J₀ = V(0+) > 0` at the origin, and a normalization level `a ∈ (0, J₀)`. Then the construction of
`def:normalization` is well-defined for all large `n`: for every fixed `x > 0` the values
`V_n(x) → V(x) ≥ J₀ > a`, so the first crossing `e_n = min{x ∈ 𝒳_n : V_n(x) ≥ a}` exists and
satisfies `e_n ≤ h_n ⌈x/h_n⌉ < x + h_n`. Hence `e_n → 0`, and together with `R_n → ∞` also
`R_n / e_n → ∞` (`cor:jumpnormalization`).

The crossing lemmas are also used (as `private` lemmas) in `MonetaryExistenceBuyer/Rescaling/Props.lean`;
they are reproduced here.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### The crossing -/

private lemma scale_nonneg (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.scale a n :=
  mul_nonneg (S.h_pos n).le (Nat.cast_nonneg _)

/-- For fixed `x > 0`, eventually `⌈x/h_n⌉₊` is a grid index with `V_n ≥ a`, because
`V_n(x) → V(x) ≥ J₀ > a`. -/
private lemma eventually_cross (S : SelectedSeq P) {a : ℝ} (haJ : a < S.jump) {x : ℝ}
    (hx : 0 < x) : ∀ᶠ n in atTop, ⌈x / S.h n⌉₊ ≤ S.N n ∧ a ≤ S.V n ⌈x / S.h n⌉₊ := by
  have hbdd : BddBelow (S.Vlim '' Ioi 0) :=
    ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact (S.limit_props.2.2.1 y (le_of_lt hy)).1⟩
  have hVx : a < S.Vlim x := haJ.trans_le (csInf_le hbdd ⟨x, hx, rfl⟩)
  filter_upwards [(S.V_conv.tendsto_at (show x ∈ Ioi (0:ℝ) from hx)).eventually_const_lt hVx,
    S.R_tendsto.eventually_gt_atTop x] with n hn hR
  have hh := S.h_pos n
  have hxi : x ≤ (⌈x / S.h n⌉₊ : ℝ) * S.h n := (div_le_iff₀ hh).1 (Nat.le_ceil _)
  have hiN : ⌈x / S.h n⌉₊ ≤ S.N n := Nat.ceil_le.2 ((div_le_iff₀ hh).2 hR.le)
  refine ⟨hiN, hn.le.trans ?_⟩
  rw [← interp_natCast (V := S.V n) hh hiN]
  exact interp_monotone hh (S.isApproxEq n).cone.incr hxi

/-- Eventually the crossing exists, so `crossIdx` is a crossing grid index, and it is positive. -/
private lemma eventually_good (S : SelectedSeq P) {a : ℝ} (ha : 0 < a) (haJ : a < S.jump) :
    ∀ᶠ n in atTop, S.crossIdx a n ≤ S.N n ∧ a ≤ S.V n (S.crossIdx a n) ∧ 0 < S.crossIdx a n := by
  filter_upwards [eventually_cross S haJ one_pos] with n hn
  have hmem : S.crossIdx a n ∈ {i | i ≤ S.N n ∧ a ≤ S.V n i} := Nat.sInf_mem ⟨_, hn⟩
  refine ⟨hmem.1, hmem.2, Nat.pos_of_ne_zero fun h0 => ?_⟩
  have h2 := hmem.2
  rw [h0, (S.isApproxEq n).cone.zero] at h2
  linarith

/-- `e_n ≤ h_n ⌈x/h_n⌉ < x + h_n` eventually. -/
private lemma eventually_scale_lt (S : SelectedSeq P) {a : ℝ} (haJ : a < S.jump) {x : ℝ}
    (hx : 0 < x) : ∀ᶠ n in atTop, S.scale a n < x + S.h n := by
  filter_upwards [eventually_cross S haJ hx] with n hn
  have hh := S.h_pos n
  have hle : S.crossIdx a n ≤ ⌈x / S.h n⌉₊ := Nat.sInf_le hn
  have hc : (⌈x / S.h n⌉₊ : ℝ) < x / S.h n + 1 := Nat.ceil_lt_add_one (div_nonneg hx.le hh.le)
  calc S.scale a n = S.h n * S.crossIdx a n := rfl
    _ ≤ S.h n * ⌈x / S.h n⌉₊ := mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hh.le
    _ < S.h n * (x / S.h n + 1) := mul_lt_mul_of_pos_left hc hh
    _ = x + S.h n := by field_simp

/-- `e_n → 0`. -/
private lemma scale_tendsto (S : SelectedSeq P) {a : ℝ} (haJ : a < S.jump) :
    Tendsto (S.scale a) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b hb => Eventually.of_forall fun n =>
    hb.trans_le (scale_nonneg S a n), fun b hb => ?_⟩
  filter_upwards [eventually_scale_lt S haJ (half_pos hb),
    S.h_tendsto.eventually_lt_const (half_pos hb)] with n h1 h2
  linarith

/-! ### `cor:jumpnormalization` -/

/-- `cor:jumpnormalization` (normalization inside a jump): for a bad sequence and a level
`0 < a < J₀`, the normalization scale satisfies `e_n → 0` and `R_n / e_n → ∞`
(with `R_n = N_n h_n`). -/
theorem SelectedSeq.jumpnormalization (S : SelectedSeq P) {a : ℝ} (ha : 0 < a) (haJ : a < S.jump) :
    Tendsto (S.scale a) atTop (𝓝 0) ∧
    Tendsto (fun n => (S.N n : ℝ) * S.h n / S.scale a n) atTop atTop := by
  refine ⟨scale_tendsto S haJ, ?_⟩
  -- eventually `e_n > 0`, so `e_n → 0` within `(0, ∞)` and `1/e_n → ∞`
  have hpos : ∀ᶠ n in atTop, S.scale a n ∈ Ioi (0:ℝ) := by
    filter_upwards [eventually_good S ha haJ] with n hn
    exact mul_pos (S.h_pos n) (by exact_mod_cast hn.2.2)
  have hinv : Tendsto (fun n => (S.scale a n)⁻¹) atTop atTop :=
    (tendsto_nhdsWithin_iff.2 ⟨scale_tendsto S haJ, hpos⟩).inv_tendsto_nhdsGT_zero
  simp_rw [div_eq_mul_inv]
  exact S.R_tendsto.atTop_mul_atTop₀ hinv

end Molico
