import MonetaryExistenceBuyer.Limit.Defs

/-!
# The tail-seller estimate (`rem:tailseller`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

/-- `rem:tailseller`, continuum version, eq. `eq:escest`: for increasing concave `V ≤ L` with
`V(0) = 0`, `0 ≤ H_V(x,s) - V(x) ≤ c₀ (V(s+x) - V(s)) ≤ c₀ x V(s)/s ≤ c₀ x L / s`. -/
theorem tailseller_cont (U : AdmissibleUtility) {V : ℝ → ℝ} (hV : IsValueFn V) {L : ℝ}
    (hL : ∀ x, 0 ≤ x → V x ≤ L) {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    0 ≤ bellH U.u V x s - V x ∧
    bellH U.u V x s - V x ≤ U.c0 * (V (s + x) - V s) ∧
    U.c0 * (V (s + x) - V s) ≤ U.c0 * x * V s / s ∧
    U.c0 * x * V s / s ≤ U.c0 * x * L / s := by
  have hc0 := U.c0_pos
  refine ⟨sub_nonneg.2 (le_bellH U hV hx hs.le), ?_, ?_, ?_⟩
  · obtain ⟨d, hd, hdeq⟩ := exists_bellH_eq U hV hx hs.le
    rw [← hdeq]
    unfold obj
    have hg0 := hV.gain_nonneg hs.le hd.1
    have h1 := U.le_c0_mul hg0
    have h2 : gain V s d ≤ V (s + x) - V s := by
      unfold gain
      linarith [hV.le_of_le (show 0 ≤ s + d by linarith [hd.1])
        (show s + d ≤ s + x by linarith [hd.2])]
    have h3 : V (x - d) ≤ V x := hV.le_of_le (by linarith [hd.2]) (by linarith [hd.1])
    have h4 := mul_le_mul_of_nonneg_left h2 hc0.le
    linarith
  · rcases hx.eq_or_lt with rfl | hx'
    · simp
    · have h := hV.concaveOn.slope_anti_adjacent (self_mem_Ici : (0:ℝ) ∈ Ici 0)
        (show s + x ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith) hs
        (show s < s + x by linarith)
      rw [hV.zero, sub_zero, sub_zero, add_sub_cancel_left, div_le_div_iff₀ hx' hs] at h
      rw [show U.c0 * x * V s / s = U.c0 * (x * V s / s) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hc0.le
      rw [le_div_iff₀ hs]
      linarith
  · have h := mul_le_mul_of_nonneg_left (hL s hs.le) (mul_nonneg hc0.le hx)
    exact div_le_div_of_nonneg_right h hs.le

/-- Discrete concavity: an increment after index `l` is at most the average slope on `[0, l]`. -/
lemma IncrSeq.mul_step_le {N : ℕ} {V : ℕ → ℝ} (hV : IncrSeq V N) :
    ∀ l y : ℕ, l ≤ y → y + 1 ≤ N → (l : ℝ) * (V (y + 1) - V y) ≤ V l - V 0 := by
  intro l
  induction l with
  | zero => intro y _ _; simp
  | succ l ih =>
    intro y hly hy
    have h1 := ih y (by omega) hy
    have h2 := hV.step_anti (x := l) (y := y) (by omega) hy
    push_cast
    linarith

/-- Discrete concavity: `l (V(l+t) - V(l)) ≤ t (V(l) - V(0))`. -/
lemma IncrSeq.mul_incr_le {N : ℕ} {V : ℕ → ℝ} (hV : IncrSeq V N) (l : ℕ) :
    ∀ t : ℕ, l + t ≤ N → (l : ℝ) * (V (l + t) - V l) ≤ t * (V l - V 0) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := hV.mul_step_le l (l + t) (by omega) (by omega)
    rw [← add_assoc]
    push_cast
    linarith

/-- `rem:tailseller`, grid version (index form; the mesh cancels): for `V : 𝒳 → [0, L]`
increasing and discretely concave with `V(0) = 0`, buyer index `x` and seller index `l ≥ 1`,
`0 ≤ H_V(x,s) - V(x) ≤ c₀ (V(min(l+x, N)) - V(l)) ≤ c₀ x V(l)/l ≤ c₀ x L / l`. -/
theorem tailseller_grid (U : AdmissibleUtility) {N : ℕ} {V : ℕ → ℝ} (hV : IncrSeq V N)
    (hV0 : V 0 = 0) {L : ℝ} (hL : ∀ i ≤ N, V i ≤ L) {x l : ℕ} (hx : x ≤ N) (hl1 : 1 ≤ l)
    (hl : l ≤ N) :
    0 ≤ Grid.gH U.u N V x l - V x ∧
    Grid.gH U.u N V x l - V x ≤ U.c0 * (V (min (l + x) N) - V l) ∧
    U.c0 * (V (min (l + x) N) - V l) ≤ U.c0 * x * V l / l ∧
    U.c0 * x * V l / l ≤ U.c0 * x * L / l := by
  have hc0 := U.c0_pos
  have hlpos : (0:ℝ) < l := by exact_mod_cast hl1
  refine ⟨sub_nonneg.2 (Grid.le_gH U hV0 hx hl), ?_, ?_, ?_⟩
  · obtain ⟨j, hj, hjeq⟩ := Grid.exists_gH_eq U (V := V) hx hl
    rw [← hjeq, Grid.gobj]
    rw [Grid.mem_feas hx hl] at hj
    have hg0 : 0 ≤ V (l + j) - V l := by
      linarith [hV.le_of_le (show l ≤ l + j by omega) hj.2]
    have h1 := U.le_c0_mul hg0
    have h2 : V (l + j) - V l ≤ V (min (l + x) N) - V l := by
      linarith [hV.le_of_le (show l + j ≤ min (l + x) N by omega) (min_le_right _ _)]
    have h3 : V (x - j) ≤ V x := hV.le_of_le (by omega) hx
    have h4 := mul_le_mul_of_nonneg_left h2 hc0.le
    linarith
  · obtain ⟨t, ht⟩ : ∃ t, min (l + x) N = l + t := ⟨min (l + x) N - l, by omega⟩
    have htx : (t:ℝ) ≤ x := by exact_mod_cast (show t ≤ x by omega)
    have hQ := hV.mul_incr_le l t (by omega)
    rw [hV0, sub_zero] at hQ
    have hVl := hV.nonneg hV0 hl
    rw [ht, show U.c0 * x * V l / l = U.c0 * (x * V l / l) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    rw [le_div_iff₀ hlpos]
    nlinarith
  · have h := mul_le_mul_of_nonneg_left (hL l hl) (mul_nonneg hc0.le (Nat.cast_nonneg x))
    exact div_le_div_of_nonneg_right h hlpos.le

end Molico
