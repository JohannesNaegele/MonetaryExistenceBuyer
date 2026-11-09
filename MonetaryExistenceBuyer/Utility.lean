import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Admissible composite utility and the fixed primitives

Formalizes, from `existence-theorem.tex`:

* `ass:utility` — the admissible composite utility `u = U ∘ K⁻¹` (structure `AdmissibleUtility`);
* `def:effectivediscount`, `def:primitives` — the effective discount factor `β`, the mean money
  stock `M`, and the derived constants `σ, C_*, μ_c, c_min, L_*` (structure `Primitives`);
* `lem:utilitybounds` — the utility bounds.

The utility is a function `ℝ → ℝ`; only its values on `[0, ∞)` matter.
The marginal utility `u'₋` is the left derivative on `(0, ∞)`, extended to the origin by
`u'₋(0) := c₀ = u'₊(0)` (see `def:primitives`).
-/

open Set Filter Topology

noncomputable section

namespace Molico

/-- `ass:utility`: an admissible composite utility. -/
structure AdmissibleUtility where
  /-- The composite utility `u = U ∘ K⁻¹` (only its restriction to `[0,∞)` matters). -/
  u : ℝ → ℝ
  /-- (U1) -/
  u_zero : u 0 = 0
  /-- (U2) -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- (U3) -/
  strictMonoOn : StrictMonoOn u (Ici 0)
  /-- (U4) -/
  strictConcaveOn : StrictConcaveOn ℝ (Ici 0) u
  /-- (U5) the right derivative at the origin, `c₀ = u'₊(0) < ∞`. -/
  c0 : ℝ
  hasDerivWithinAt_zero : HasDerivWithinAt u c0 (Ici 0) 0
  /-- (U6) `u` is bounded, `u(x) ↑ ū < ∞`. -/
  ubar : ℝ
  tendsto_ubar : Tendsto u atTop (𝓝 ubar)

namespace AdmissibleUtility

variable (U : AdmissibleUtility)

/-- The marginal utility `u'₋`: the left derivative at positive arguments, and `c₀` at the
origin (`def:primitives`). -/
def marg (x : ℝ) : ℝ := if x ≤ 0 then U.c0 else derivWithin U.u (Iio x) x

lemma concaveOn : ConcaveOn ℝ (Ici 0) U.u := U.strictConcaveOn.concaveOn

lemma convexOn_neg : ConvexOn ℝ (Ici 0) (-U.u) := U.concaveOn.neg

lemma monotoneOn : MonotoneOn U.u (Ici 0) := U.strictMonoOn.monotoneOn

lemma nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ U.u x := by
  have := U.monotoneOn (self_mem_Ici) (show x ∈ Ici (0:ℝ) from hx) hx
  simpa [U.u_zero] using this

lemma pos {x : ℝ} (hx : 0 < x) : 0 < U.u x := by
  have := U.strictMonoOn (self_mem_Ici) (show x ∈ Ici (0:ℝ) from hx.le) hx
  simpa [U.u_zero] using this

lemma le_ubar {x : ℝ} (hx : 0 ≤ x) : U.u x ≤ U.ubar := by
  apply ge_of_tendsto U.tendsto_ubar
  filter_upwards [eventually_ge_atTop x] with y hy
  exact U.monotoneOn hx (hx.trans hy) hy

lemma lt_ubar {x : ℝ} (hx : 0 ≤ x) : U.u x < U.ubar :=
  (U.strictMonoOn hx (show x + 1 ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith)
    (by linarith)).trans_le (U.le_ubar (by linarith))

lemma ubar_pos : 0 < U.ubar := (U.pos one_pos).trans (U.lt_ubar zero_le_one)

/-- Slope from the origin bounded by the right derivative at the origin. -/
lemma slope_zero_le_c0 {x : ℝ} (hx : 0 < x) : U.u x / x ≤ U.c0 := by
  have h := U.convexOn_neg.le_slope_of_hasDerivWithinAt_Ioi (self_mem_Ici)
    (show x ∈ Ici (0:ℝ) from hx.le) hx
    ((U.hasDerivWithinAt_zero.neg).mono Ioi_subset_Ici_self)
  rw [slope_def_field] at h
  simp only [Pi.neg_apply, U.u_zero, neg_zero, sub_zero] at h
  rw [neg_div] at h
  linarith

lemma le_c0_mul {x : ℝ} (hx : 0 ≤ x) : U.u x ≤ U.c0 * x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [U.u_zero]
  · have := U.slope_zero_le_c0 hx
    rwa [div_le_iff₀ hx] at this

lemma c0_pos : 0 < U.c0 := by
  have h1 := U.slope_zero_le_c0 one_pos
  have h2 := U.pos one_pos
  rw [div_one] at h1
  linarith

/-- For a concave function on `[0,∞)`, increments over a fixed step decrease with the base point. -/
lemma _root_.Molico.concave_incr_anti {f : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici 0) f) {x y t : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ht : 0 ≤ t) :
    f (y + t) - f y ≤ f (x + t) - f x := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rcases hxy.eq_or_lt with rfl | hxy
  · rfl
  -- three-slope inequalities for the concave function `u`
  have hmem : ∀ z, 0 ≤ z → z ∈ Ici (0:ℝ) := fun z hz => hz
  by_cases hyt : y ≤ x + t
  · rcases hyt.eq_or_lt with hyt | hyt
    · -- y = x + t
      have h1 := hc.slope_anti_adjacent (hmem x hx) (hmem (y + t) (by linarith))
        (show x < y by linarith) (show y < y + t by linarith)
      have e1 : y + t - y = t := by ring
      have e2 : y - x = t := by linarith
      rw [e1, e2, div_le_div_iff_of_pos_right ht] at h1
      rw [← hyt]
      linarith
    · have h1 := hc.slope_anti_adjacent (hmem x hx) (hmem (x + t) (by linarith)) hxy hyt
      have h2 := hc.slope_anti_adjacent (hmem y (by linarith)) (hmem (y + t) (by linarith)) hyt
        (show x + t < y + t by linarith)
      -- slope on [x, y] ≥ slope on [y, x+t] ≥ slope on [x+t, y+t]
      have h3 : (f (x + t) - f y) / (x + t - y) ≤ (f y - f x) / (y - x) := h1
      have h4 : (f (y + t) - f (x + t)) / (y + t - (x + t)) ≤
          (f (x + t) - f y) / (x + t - y) := h2
      have hp1 : 0 < y - x := by linarith
      have hp2 : 0 < x + t - y := by linarith
      have e : y + t - (x + t) = y - x := by ring
      rw [e] at h4
      have h5 : (f (y + t) - f (x + t)) / (y - x) ≤ (f y - f x) / (y - x) :=
        h4.trans h3
      rw [div_le_div_iff_of_pos_right hp1] at h5
      linarith
  · replace hyt := not_le.mp hyt
    have h1 := hc.slope_anti_adjacent (hmem x hx) (hmem y (by linarith))
      (show x < x + t by linarith) hyt
    have h2 := hc.slope_anti_adjacent (hmem (x + t) (by linarith)) (hmem (y + t) (by linarith))
      hyt (show y < y + t by linarith)
    have e1 : x + t - x = t := by ring
    have e2 : y + t - y = t := by ring
    rw [e1] at h1
    rw [e2] at h2
    have h3 := h2.trans h1
    rw [div_le_div_iff_of_pos_right ht] at h3
    linarith

/-- For the utility, increments over a fixed step decrease with the base point. -/
lemma incr_anti {x y t : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ht : 0 ≤ t) :
    U.u (y + t) - U.u y ≤ U.u (x + t) - U.u x :=
  Molico.concave_incr_anti U.concaveOn hx hxy ht

/-- `u` is `c₀`-Lipschitz on `[0, ∞)`. -/
lemma sub_le_c0_mul {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    U.u y - U.u x ≤ U.c0 * (y - x) := by
  have := U.incr_anti (le_refl 0) hx (show 0 ≤ y - x by linarith)
  simp only [zero_add, U.u_zero, sub_zero, add_sub_cancel] at this
  linarith [U.le_c0_mul (show 0 ≤ y - x by linarith)]

/-! ### Secant bounds `eq:utilitysecants` -/

lemma marg_of_pos {x : ℝ} (hx : 0 < x) : U.marg x = derivWithin U.u (Iio x) x := by
  simp [marg, not_le.mpr hx]

lemma marg_zero : U.marg 0 = U.c0 := by simp [marg]

lemma interior_Ici_zero : interior (Ici (0:ℝ)) = Ioi 0 := interior_Ici

/-- Upper secant bound: `(u b - u a)/(b - a) ≤ u'₋(a)` for `0 ≤ a < b`. -/
lemma slope_le_marg {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (U.u b - U.u a) / (b - a) ≤ U.marg a := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [U.marg_zero, U.u_zero, sub_zero, sub_zero]
    exact U.slope_zero_le_c0 hab
  · have hint : a ∈ interior (Ici (0:ℝ)) := by rw [interior_Ici]; exact ha
    have h1 := U.convexOn_neg.leftDeriv_le_rightDeriv_of_mem_interior hint
    have h2 := U.convexOn_neg.rightDeriv_le_slope_of_mem_interior hint
      (show b ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith) hab
    have h3 := h1.trans h2
    rw [slope_def_field] at h3
    have e1 : derivWithin (-U.u) (Iio a) a = - derivWithin U.u (Iio a) a := derivWithin.neg
    rw [e1] at h3
    simp only [Pi.neg_apply] at h3
    rw [U.marg_of_pos ha]
    have : (-U.u b - -U.u a) / (b - a) = -((U.u b - U.u a) / (b - a)) := by ring
    linarith

/-- Lower secant bound: `u'₋(b) ≤ (u b - u a)/(b - a)` for `0 ≤ a < b`. -/
lemma marg_le_slope {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    U.marg b ≤ (U.u b - U.u a) / (b - a) := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hint : b ∈ interior (Ici (0:ℝ)) := by rw [interior_Ici]; exact hb
  have h := U.convexOn_neg.slope_le_leftDeriv_of_mem_interior (show a ∈ Ici (0:ℝ) from ha)
    hint hab
  rw [slope_def_field] at h
  have e1 : derivWithin (-U.u) (Iio b) b = - derivWithin U.u (Iio b) b := derivWithin.neg
  rw [e1] at h
  simp only [Pi.neg_apply] at h
  rw [U.marg_of_pos hb]
  have : (-U.u b - -U.u a) / (b - a) = -((U.u b - U.u a) / (b - a)) := by ring
  linarith

/-- Secant bounds in multiplied form. -/
lemma sub_le_marg_mul {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    U.u b - U.u a ≤ U.marg a * (b - a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have := U.slope_le_marg ha hab
  rwa [div_le_iff₀ (by linarith)] at this

lemma marg_mul_le_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    U.marg b * (b - a) ≤ U.u b - U.u a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have := U.marg_le_slope ha hab
  rwa [le_div_iff₀ (by linarith)] at this

lemma marg_antitoneOn : AntitoneOn U.marg (Ici 0) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · rfl
  exact (U.marg_le_slope hx hxy).trans (U.slope_le_marg hx hxy)

lemma marg_le_c0 {x : ℝ} (hx : 0 ≤ x) : U.marg x ≤ U.c0 := by
  rw [← U.marg_zero]; exact U.marg_antitoneOn self_mem_Ici hx hx

lemma marg_pos {x : ℝ} (hx : 0 ≤ x) : 0 < U.marg x := by
  have h1 := U.slope_le_marg hx (show x < x + 1 by linarith)
  have h2 : 0 < U.u (x + 1) - U.u x :=
    sub_pos.mpr (U.strictMonoOn hx (show x + 1 ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith)
      (by linarith))
  have : 0 < (U.u (x + 1) - U.u x) / (x + 1 - x) := div_pos h2 (by linarith)
  linarith

/-- Strict concavity through the origin: `u(x) < c₀ x` for `x > 0`. -/
lemma lt_c0_mul {x : ℝ} (hx : 0 < x) : U.u x < U.c0 * x := by
  -- midpoint strict concavity: u(x/2) > u(x)/2, and u(x/2) ≤ c₀ x/2
  have hmid := U.strictConcaveOn.2 (self_mem_Ici : (0:ℝ) ∈ Ici 0)
    (show x ∈ Ici (0:ℝ) from hx.le) (ne_of_lt hx) (show (0:ℝ) < 1/2 by norm_num)
    (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, U.u_zero] at hmid
  have h2 := U.le_c0_mul (show 0 ≤ 1/2 * x by positivity)
  nlinarith

/-- `u(x)/x` is strictly decreasing on `(0, ∞)`. -/
lemma strictAntiOn_div : StrictAntiOn (fun x => U.u x / x) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  -- strict concavity on [0, y] at the point x = (x/y) • y
  have ht : 0 < x / y := div_pos hx hy
  have ht1 : x / y < 1 := (div_lt_one hy).mpr hxy
  have h := U.strictConcaveOn.2 (self_mem_Ici : (0:ℝ) ∈ Ici 0)
    (show y ∈ Ici (0:ℝ) from hy.le) (ne_of_lt hy) (show 0 < 1 - x / y by linarith) ht
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, U.u_zero] at h
  have e : x / y * y = x := by field_simp
  rw [e] at h
  show U.u y / y < U.u x / x
  rw [div_lt_div_iff₀ hy hx]
  have : x / y * U.u y * y = x * U.u y := by field_simp
  nlinarith

lemma tendsto_div_zero : Tendsto (fun x => U.u x / x) (𝓝[>] 0) (𝓝 U.c0) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi (0:ℝ)) (lt_irrefl (0:ℝ))).mp
    (U.hasDerivWithinAt_zero.mono Ioi_subset_Ici_self)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x _
  simp [slope_def_field, U.u_zero]

lemma tendsto_div_atTop : Tendsto (fun x => U.u x / x) atTop (𝓝 0) := by
  have hb : Tendsto (fun x : ℝ => U.ubar / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_nonneg (U.nonneg hx.le) hx.le
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_le_div_of_nonneg_right (U.le_ubar hx.le) hx.le

lemma tendsto_marg_zero : Tendsto U.marg (𝓝[>] 0) (𝓝 U.c0) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- lower bound: compare with a secant `[x, t]` for a fixed small `t`
    have hb : (a + U.c0) / 2 < U.c0 := by linarith
    obtain ⟨t, ht, ht0⟩ := ((U.tendsto_div_zero.eventually (lt_mem_nhds hb)).and
      self_mem_nhdsWithin).exists
    replace ht0 : 0 < t := ht0
    have hg : Tendsto (fun x => (U.u t - U.u x) / (t - x)) (𝓝[>] 0) (𝓝 (U.u t / t)) := by
      have hu : Tendsto U.u (𝓝[>] 0) (𝓝 0) := by
        have := (U.continuousOn 0 self_mem_Ici).mono_left
          (nhdsWithin_mono _ Ioi_subset_Ici_self)
        simpa [U.u_zero] using this
      have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
        tendsto_id
      have := ((tendsto_const_nhds (x := U.u t)).sub hu).div
        ((tendsto_const_nhds (x := t)).sub hx) (by simp [ht0.ne'])
      rw [sub_zero, sub_zero] at this
      exact this
    have hlt : a < U.u t / t := by linarith
    filter_upwards [hg.eventually (lt_mem_nhds hlt), self_mem_nhdsWithin,
      (Ioo_mem_nhdsGT ht0)] with x hx hx0 hxt
    simp only [mem_Ioi] at hx0
    exact hx.trans_le (U.slope_le_marg hx0.le hxt.2)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (U.marg_le_c0 (le_of_lt hx)).trans_lt ha

lemma tendsto_marg_atTop : Tendsto U.marg atTop (𝓝 0) := by
  have hb := U.tendsto_div_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · filter_upwards [eventually_ge_atTop 0] with x hx
    exact (U.marg_pos hx).le
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have := U.marg_le_slope (le_refl 0) hx
    simpa [U.u_zero] using this

/-- The marginal utility is left continuous on `(0, ∞)` (`lem:utilitybounds`). -/
lemma marg_continuousWithinAt_Iic {x : ℝ} (hx : 0 < x) :
    ContinuousWithinAt U.marg (Iic x) x := by
  have hint : x ∈ interior (Ici (0:ℝ)) := by rw [interior_Ici]; exact hx
  -- the left derivative is the limit of left secants
  have hd := U.convexOn_neg.hasDerivWithinAt_leftDeriv_of_mem_interior hint
  rw [derivWithin.neg] at hd
  have hd' : HasDerivWithinAt U.u (U.marg x) (Iio x) x := by
    rw [U.marg_of_pos hx]; simpa using hd.neg
  have hsl := (hasDerivWithinAt_iff_tendsto_slope' (s := Iio x) (by simp)).mp hd'
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [self_mem_nhdsWithin, (Ioi_mem_nhds hx : Ioi (0:ℝ) ∈ 𝓝 x) |>
      mem_nhdsWithin_of_mem_nhds] with y hy hy0
    exact ha.trans_le (U.marg_antitoneOn (mem_Ici.2 (le_of_lt (mem_Ioi.1 hy0))) hx.le hy)
  · -- choose `b < x` with left secant slope `< a`, then use continuity of the secant in `y`
    obtain ⟨b, hb, hbx⟩ := ((hsl.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsLT hx)).exists
    replace hbx : 0 < b ∧ b < x := hbx
    have hb' : (U.u x - U.u b) / (x - b) < a := by
      rw [slope_def_field] at hb
      have : (U.u b - U.u x) / (b - x) = (U.u x - U.u b) / (x - b) := by
        rw [← neg_sub (U.u x), ← neg_sub x, neg_div_neg_eq]
      linarith
    have hcont : Tendsto (fun y => (U.u y - U.u b) / (y - b)) (𝓝[Iic x] x)
        (𝓝 ((U.u x - U.u b) / (x - b))) := by
      have hu : Tendsto U.u (𝓝[Iic x] x) (𝓝 (U.u x)) := by
        have hc := U.continuousOn x (show x ∈ Ici (0:ℝ) from hx.le)
        have hmem : Ici (0:ℝ) ∈ 𝓝 x := Ici_mem_nhds hx
        exact (hc.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
      exact (hu.sub tendsto_const_nhds).div ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub
        tendsto_const_nhds) (by linarith)
    filter_upwards [hcont.eventually (gt_mem_nhds hb'), (Ioi_mem_nhds hbx.2 : Ioi b ∈ 𝓝 x) |>
      mem_nhdsWithin_of_mem_nhds] with y hy hyb
    exact (U.marg_le_slope (le_of_lt hbx.1) hyb).trans_lt hy

/-- The marginal utility is upper semicontinuous on `[0, ∞)` (`lem:utilitybounds`). -/
lemma marg_upperSemicontinuousOn : UpperSemicontinuousOn U.marg (Ici 0) := by
  intro x hx y hy
  rcases (show (0:ℝ) ≤ x from hx).eq_or_lt with rfl | hx'
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (U.marg_le_c0 hz).trans_lt (by rwa [U.marg_zero] at hy)
  · have hl := (U.marg_continuousWithinAt_Iic hx').eventually (gt_mem_nhds hy)
    rw [eventually_nhdsWithin_iff] at hl
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hl] with z hz hz0
    rcases le_or_gt z x with hzx | hzx
    · exact hz hzx
    · exact (U.marg_antitoneOn hx hz0 hzx.le).trans_lt hy

end AdmissibleUtility

/-- `def:effectivediscount`, `def:primitives`: the fixed primitives of the existence proof.
`β` is the effective discount factor `π/(r+π)`; `active` is the activation condition
`eq:active`, `β c₀ > 1`. -/
structure Primitives where
  U : AdmissibleUtility
  β : ℝ
  M : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  M_pos : 0 < M
  active : 1 < β * U.c0

namespace Primitives

variable (P : Primitives)

/-- `σ = 1/β - 1`. -/
def σ : ℝ := 1 / P.β - 1

/-- `C_* = ū/σ`. -/
def Cstar : ℝ := P.U.ubar / P.σ

/-- `μ_c = σ/(c₀ - 1)`. -/
def μc : ℝ := P.σ / (P.U.c0 - 1)

/-- `c_min = min{1, u'₋(C_*)}`. -/
def cmin : ℝ := min 1 (P.U.marg P.Cstar)

lemma σ_pos : 0 < P.σ := by
  unfold σ
  have := P.β_lt_one
  have := P.β_pos
  rw [sub_pos, lt_div_iff₀ P.β_pos]; linarith

lemma one_add_σ : 1 + P.σ = 1 / P.β := by unfold σ; ring

lemma β_eq : P.β = 1 / (1 + P.σ) := by rw [one_add_σ]; field_simp

lemma c0_gt : 1 + P.σ < P.U.c0 := by
  rw [one_add_σ, div_lt_iff₀ P.β_pos]; linarith [P.active]

lemma c0_gt_one : 1 < P.U.c0 := by linarith [P.c0_gt, P.σ_pos]

lemma Cstar_pos : 0 < P.Cstar := div_pos P.U.ubar_pos P.σ_pos

lemma μc_pos : 0 < P.μc := div_pos P.σ_pos (by linarith [P.c0_gt_one])

lemma μc_lt_one : P.μc < 1 := by
  unfold μc; rw [div_lt_one (by linarith [P.c0_gt_one])]; linarith [P.c0_gt]

lemma exists_Lstar : ∃ L, 0 < L ∧ P.U.u L = P.σ * L := by
  have hσ : P.σ < P.U.c0 := by linarith [P.c0_gt]
  obtain ⟨t, ht, ht0⟩ := ((P.U.tendsto_div_zero.eventually (lt_mem_nhds hσ)).and
    self_mem_nhdsWithin).exists
  replace ht0 : 0 < t := ht0
  set X := max t (P.U.ubar / P.σ + 1) with hX
  have htX : t ≤ X := le_max_left _ _
  have hX1 : P.U.ubar / P.σ + 1 ≤ X := le_max_right _ _
  have hgt : 0 < P.U.u t - P.σ * t := by
    rw [lt_div_iff₀ ht0] at ht; linarith
  have hgX : P.U.u X - P.σ * X < 0 := by
    have h1 := P.U.le_ubar (show 0 ≤ X by linarith)
    have h2 : P.U.ubar < P.σ * X := by
      have := (div_lt_iff₀' P.σ_pos).mp (show P.U.ubar / P.σ < X by linarith)
      linarith
    linarith
  have hcont : ContinuousOn (fun x => P.U.u x - P.σ * x) (Icc t X) :=
    (P.U.continuousOn.mono fun z hz => (show (0:ℝ) ≤ z from ht0.le.trans hz.1)).sub
      (continuousOn_const.mul continuousOn_id)
  obtain ⟨L, hL, hL0⟩ := intermediate_value_Icc' htX hcont ⟨hgX.le, hgt.le⟩
  exact ⟨L, ht0.trans_le hL.1, by simp only at hL0; linarith⟩

/-- `L_*`: the unique positive solution of `u(L) = σ L`. -/
def Lstar : ℝ := Classical.choose P.exists_Lstar

lemma Lstar_pos : 0 < P.Lstar := (Classical.choose_spec P.exists_Lstar).1

lemma u_Lstar : P.U.u P.Lstar = P.σ * P.Lstar := (Classical.choose_spec P.exists_Lstar).2

/-- `u(x)/x > σ` below `L_*` and `< σ` above it. -/
lemma div_gt_σ_iff {x : ℝ} (hx : 0 < x) : P.σ < P.U.u x / x ↔ x < P.Lstar := by
  have hL : P.U.u P.Lstar / P.Lstar = P.σ := by
    rw [P.u_Lstar, mul_div_assoc, div_self P.Lstar_pos.ne', mul_one]
  constructor
  · intro h
    by_contra h'
    replace h' := not_lt.mp h'
    rcases h'.eq_or_lt with h' | h'
    · rw [← h', hL] at h; exact lt_irrefl _ h
    · have := P.U.strictAntiOn_div (show P.Lstar ∈ Ioi (0:ℝ) from P.Lstar_pos)
        (show x ∈ Ioi (0:ℝ) from hx) h'
      simp only at this
      linarith
  · intro h
    have := P.U.strictAntiOn_div (show x ∈ Ioi (0:ℝ) from hx)
      (show P.Lstar ∈ Ioi (0:ℝ) from P.Lstar_pos) h
    simp only at this
    linarith

/-- If `σ x ≤ u(x)` with `x ≥ 0`, then `x ≤ L_*` (used in `lem:gauge`). -/
lemma le_Lstar_of_σ_mul_le {x : ℝ} (hx : 0 ≤ x) (h : P.σ * x ≤ P.U.u x) : x ≤ P.Lstar := by
  rcases hx.eq_or_lt with rfl | hx
  · exact P.Lstar_pos.le
  by_contra h'
  replace h' := not_le.mp h'
  have := P.U.strictAntiOn_div (show P.Lstar ∈ Ioi (0:ℝ) from P.Lstar_pos)
    (show x ∈ Ioi (0:ℝ) from hx) h'
  simp only at this
  have hL : P.U.u P.Lstar / P.Lstar = P.σ := by
    rw [P.u_Lstar, mul_div_assoc, div_self P.Lstar_pos.ne', mul_one]
  rw [hL, div_lt_iff₀ hx] at this
  linarith

lemma Lstar_lt_Cstar : P.Lstar < P.Cstar := by
  unfold Cstar
  rw [lt_div_iff₀ P.σ_pos, mul_comm, ← P.u_Lstar]
  exact P.U.lt_ubar P.Lstar_pos.le

lemma marg_Cstar_pos : 0 < P.U.marg P.Cstar := P.U.marg_pos P.Cstar_pos.le

lemma cmin_pos : 0 < P.cmin := lt_min one_pos P.marg_Cstar_pos

lemma cmin_le_one : P.cmin ≤ 1 := min_le_left _ _

/-- `lem:utilitybounds`, eq. `eq:utilitybounds` and `eq:marginalbounds`. -/
theorem utilitybounds :
    1 + P.σ < P.U.c0 ∧ 0 < P.μc ∧ P.μc < 1 ∧ 0 < P.Lstar ∧ P.Lstar < P.Cstar ∧
    (∀ x, 0 ≤ x → x ≤ P.Cstar →
      0 < P.U.marg P.Cstar ∧ P.U.marg P.Cstar ≤ P.U.marg x ∧ P.U.marg x ≤ P.U.c0) :=
  ⟨P.c0_gt, P.μc_pos, P.μc_lt_one, P.Lstar_pos, P.Lstar_lt_Cstar, fun _ hx hxC =>
    ⟨P.marg_Cstar_pos, P.U.marg_antitoneOn hx P.Cstar_pos.le hxC, P.U.marg_le_c0 hx⟩⟩

end Primitives

end Molico
