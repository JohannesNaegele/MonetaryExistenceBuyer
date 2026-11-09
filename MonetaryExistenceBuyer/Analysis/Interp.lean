import MonetaryExistenceBuyer.Limit.Basic

/-!
# Piecewise-linear interpolation of grid functions

Properties of `interp h N V`: the extension of a grid function `V` (values at `i h`,
`0 ≤ i ≤ N`) to `ℝ` by linear interpolation on `[0, N h]` and constant continuation (`def:selected`).
-/

open Set Filter Topology

noncomputable section

namespace Molico

variable {h : ℝ} {N : ℕ} {V : ℕ → ℝ}

/-- `interp` agrees with `V` at grid points. -/
theorem interp_natCast (hh : 0 < h) {i : ℕ} (hi : i ≤ N) : interp h N V (i * h) = V i := by
  unfold interp
  split_ifs with hN
  · have h1 : (N : ℝ) ≤ i := le_of_mul_le_mul_right hN hh
    have h2 : N ≤ i := by exact_mod_cast h1
    have h3 : i = N := le_antisymm hi h2
    rw [h3]
  · rw [max_eq_left (mul_nonneg (Nat.cast_nonneg i) hh.le), mul_div_cancel_right₀ _ hh.ne',
      Nat.floor_natCast]
    ring

/-- `interp` is constant `V N` on `[N h, ∞)`. -/
theorem interp_of_le (hh : 0 < h) {x : ℝ} (hx : N * h ≤ x) : interp h N V x = V N := by
  unfold interp
  rw [ite_eq_left hx]

/-- `interp` is constant `V 0` on `(-∞, 0]`. -/
theorem interp_of_nonpos (hh : 0 < h) {x : ℝ} (hx : x ≤ 0) : interp h N V x = V 0 := by
  unfold interp
  split_ifs with hN
  · have hN0 : N = 0 := by
      by_contra hne
      have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hne)
      nlinarith [mul_pos this hh]
    rw [hN0]
  · rw [max_eq_right hx]
    simp

/-- On a grid cell `[i h, (i+1) h]`, `interp` is the linear interpolation of `V i`, `V (i+1)`. -/
theorem interp_eq_on_cell (hh : 0 < h) {i : ℕ} (hi : i < N) {x : ℝ}
    (hx : x ∈ Icc ((i : ℝ) * h) ((i + 1 : ℝ) * h)) :
    interp h N V x = V i + (x / h - i) * (V (i + 1) - V i) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hiN : ((i : ℝ) + 1) ≤ N := by exact_mod_cast hi
  have hxh1 : (i : ℝ) ≤ x / h := by rw [le_div_iff₀ hh]; exact hx1
  have hxh2 : x / h ≤ (i : ℝ) + 1 := by rw [div_le_iff₀ hh]; exact hx2
  have hx0 : 0 ≤ x := le_trans (mul_nonneg (Nat.cast_nonneg i) hh.le) hx1
  unfold interp
  split_ifs with hN
  · have h1 : (N : ℝ) ≤ x / h := by rw [le_div_iff₀ hh]; exact hN
    have h2 : (N : ℝ) = i + 1 := by linarith
    have h3 : N = i + 1 := by exact_mod_cast h2
    have h4 : x / h = i + 1 := by linarith
    subst h3
    rw [h4]
    ring
  · rw [max_eq_left hx0]
    rcases hxh2.lt_or_eq with hlt | heq
    · have hfl : ⌊x / h⌋₊ = i := (Nat.floor_eq_iff (by positivity)).2 ⟨hxh1, hlt⟩
      rw [hfl]
    · have hfl : ⌊x / h⌋₊ = i + 1 := by
        rw [heq]; exact_mod_cast Nat.floor_natCast (R := ℝ) (i + 1)
      rw [hfl, heq]
      push_cast
      ring

/-- Sum representation of the interpolant: `V 0 + ∑_{i < N} (V (i+1) - V i) · c(x/h - i)`,
with the unit ramp `c(t) = max 0 (min t 1)`. -/
def interpSum (h : ℝ) (N : ℕ) (V : ℕ → ℝ) (x : ℝ) : ℝ :=
  V 0 + ∑ i ∈ Finset.range N, (V (i + 1) - V i) * max 0 (min (x / h - i) 1)

/-- `interp` is a sum of ramps (`interpSum`). -/
theorem interp_eq_interpSum (hh : 0 < h) (x : ℝ) : interp h N V x = interpSum h N V x := by
  unfold interpSum
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [interp_of_nonpos hh hx0]
    have hxh : x / h ≤ 0 := div_nonpos_of_nonpos_of_nonneg hx0 hh.le
    have : ∀ i ∈ Finset.range N, (V (i + 1) - V i) * max 0 (min (x / h - i) 1) = 0 := by
      intro i _
      rw [max_eq_left (min_le_of_left_le (by linarith [Nat.cast_nonneg (α := ℝ) i]))]
      ring
    rw [Finset.sum_eq_zero this, add_zero]
  rcases le_or_gt ((N : ℝ) * h) x with hxN | hxN
  · rw [interp_of_le hh hxN]
    have hNx : (N : ℝ) ≤ x / h := by rw [le_div_iff₀ hh]; exact hxN
    have : ∀ i ∈ Finset.range N,
        (V (i + 1) - V i) * max 0 (min (x / h - i) 1) = V (i + 1) - V i := by
      intro i hi
      have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hi
      rw [min_eq_right (by linarith), max_eq_right zero_le_one, mul_one]
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub]
    ring
  · have ht0 : 0 ≤ x / h := div_nonneg hx0.le hh.le
    have hk1 : (⌊x / h⌋₊ : ℝ) ≤ x / h := Nat.floor_le ht0
    have hk2 : x / h < ⌊x / h⌋₊ + 1 := Nat.lt_floor_add_one _
    have hkN : ⌊x / h⌋₊ < N := by
      have : x / h < N := by rw [div_lt_iff₀ hh]; exact hxN
      exact_mod_cast hk1.trans_lt this
    rw [interp_eq_on_cell hh hkN ⟨(le_div_iff₀ hh).1 hk1, (div_le_iff₀ hh).1 hk2.le⟩]
    set k := ⌊x / h⌋₊ with hk
    rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ N by omega), Finset.sum_range_succ]
    have h1 : ∀ i ∈ Finset.range k,
        (V (i + 1) - V i) * max 0 (min (x / h - i) 1) = V (i + 1) - V i := by
      intro i hi
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hi
      rw [min_eq_right (by linarith), max_eq_right zero_le_one, mul_one]
    have h2 : ∀ i ∈ Finset.Ico (k + 1) N,
        (V (i + 1) - V i) * max 0 (min (x / h - i) 1) = 0 := by
      intro i hi
      have : (k : ℝ) + 1 ≤ i := by exact_mod_cast (Finset.mem_Ico.1 hi).1
      rw [max_eq_left (min_le_of_left_le (by linarith))]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, Finset.sum_range_sub,
      min_eq_left (by linarith), max_eq_right (by linarith)]
    ring

theorem continuous_interpSum : Continuous (interpSum h N V) := by
  unfold interpSum
  fun_prop

theorem continuous_interp (hh : 0 < h) : Continuous (interp h N V) := by
  rw [show interp h N V = interpSum h N V from funext (interp_eq_interpSum hh)]
  exact continuous_interpSum

theorem interpSum_monotone (hh : 0 < h) (hV : IncrSeq V N) : Monotone (interpSum h N V) := by
  intro x y hxy
  unfold interpSum
  gcongr with i hi
  · exact sub_nonneg.2 (hV.mono i (Finset.mem_range.1 hi))

theorem interp_monotone (hh : 0 < h) (hV : IncrSeq V N) : Monotone (interp h N V) := by
  rw [show interp h N V = interpSum h N V from funext (interp_eq_interpSum hh)]
  exact interpSum_monotone hh hV

/-- Summing unit ramps: `∑_{i ≤ k} max 0 (min (t - i) 1) = min t (k + 1)` for `t ≥ 0`. -/
theorem sum_range_ramp {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), max 0 (min (t - i) 1) = min t (k + 1) := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, sub_zero]
    exact max_eq_right (le_min ht zero_le_one)
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    simp only [min_def, max_def]
    split_ifs <;> linarith

theorem interp_concaveOn (hh : 0 < h) (hV : IncrSeq V N) : ConcaveOn ℝ (Ici 0) (interp h N V) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, ∀ j, e j = if j < N then V (j + 1) - V j else 0 :=
    ⟨_, fun _ => rfl⟩
  have hc : ∀ k ∈ Finset.range N, 0 ≤ e k - e (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [he, he, ite_eq_left hk]
    split_ifs with hk1
    · have := hV.concave k (by omega)
      have e2 : k + 1 + 1 = k + 2 := by omega
      rw [e2]
      linarith
    · have := hV.mono k hk
      linarith
  have hd : ∀ i ∈ Finset.range N, ∑ k ∈ Finset.Ico i N, (e k - e (k + 1)) = V (i + 1) - V i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.sum_Ico_eq_sub _ hi.le, Finset.sum_range_sub', Finset.sum_range_sub', he i, he N,
      ite_eq_left hi, ite_eq_right (lt_irrefl N)]
    ring
  -- the concave representative `V 0 + ∑_k c_k min (x/h) (k+1)` with `c_k ≥ 0`
  let G : ℝ → ℝ := fun x => V 0 + ∑ k ∈ Finset.range N, (e k - e (k + 1)) * min (x / h) (k + 1)
  have hG : ConcaveOn ℝ (Ici 0) G := by
    refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, G]
    have key : ∀ k ∈ Finset.range N,
        a * ((e k - e (k + 1)) * min (x / h) (k + 1)) +
          b * ((e k - e (k + 1)) * min (y / h) (k + 1)) ≤
        (e k - e (k + 1)) * min ((a * x + b * y) / h) (k + 1) := by
      intro k hk
      have hm : a * min (x / h) (k + 1) + b * min (y / h) (k + 1) ≤
          min ((a * x + b * y) / h) (k + 1) := by
        apply le_min
        · have h1 : a * min (x / h) (k + 1) ≤ a * (x / h) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) ha
          have h2 : b * min (y / h) (k + 1) ≤ b * (y / h) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hb
          have h3 : (a * x + b * y) / h = a * (x / h) + b * (y / h) := by ring
          linarith
        · have h1 : a * min (x / h) (k + 1) ≤ a * ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) ha
          have h2 : b * min (y / h) (k + 1) ≤ b * ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hb
          have h3 : a * ((k : ℝ) + 1) + b * ((k : ℝ) + 1) = (k : ℝ) + 1 := by
            rw [← add_mul, hab, one_mul]
          linarith
      calc a * ((e k - e (k + 1)) * min (x / h) (k + 1)) +
            b * ((e k - e (k + 1)) * min (y / h) (k + 1))
          = (e k - e (k + 1)) * (a * min (x / h) (k + 1) + b * min (y / h) (k + 1)) := by ring
        _ ≤ (e k - e (k + 1)) * min ((a * x + b * y) / h) (k + 1) :=
          mul_le_mul_of_nonneg_left hm (hc k hk)
    have hs := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have hV0 : V 0 = a * V 0 + b * V 0 := by rw [← add_mul, hab, one_mul]
    linarith
  refine hG.congr fun x hx => ?_
  have ht : 0 ≤ x / h := div_nonneg hx hh.le
  simp only [G]
  rw [interp_eq_interpSum hh, interpSum]
  congr 1
  calc ∑ k ∈ Finset.range N, (e k - e (k + 1)) * min (x / h) (k + 1)
      = ∑ k ∈ Finset.range N, (e k - e (k + 1)) *
          ∑ i ∈ Finset.range (k + 1), max 0 (min (x / h - i) 1) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sum_range_ramp ht]
    _ = ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range (k + 1),
          (e k - e (k + 1)) * max 0 (min (x / h - i) 1) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.Ico i N,
          (e k - e (k + 1)) * max 0 (min (x / h - i) 1) := by
        refine Finset.sum_comm' fun k i => ?_
        simp only [Finset.mem_range, Finset.mem_Ico]
        omega
    _ = ∑ i ∈ Finset.range N, (V (i + 1) - V i) * max 0 (min (x / h - i) 1) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← Finset.sum_mul, hd i hi]

theorem interp_mem_Icc (hh : 0 < h) (hV : IncrSeq V N) (x : ℝ) :
    V 0 ≤ interp h N V x ∧ interp h N V x ≤ V N := by
  have hm := interp_monotone hh hV
  constructor
  · calc V 0 = interp h N V (min x 0) := (interp_of_nonpos hh (min_le_right _ _)).symm
      _ ≤ interp h N V x := hm (min_le_left _ _)
  · calc interp h N V x ≤ interp h N V (max x (N * h)) := hm (le_max_left _ _)
      _ = V N := interp_of_le hh (le_max_right _ _)

/-- On a grid cell, `interp` is sandwiched between the endpoint values. -/
theorem interp_sandwich (hh : 0 < h) (hV : IncrSeq V N) {i : ℕ} (hi : i < N) {x : ℝ}
    (hx : x ∈ Icc ((i : ℝ) * h) ((i + 1 : ℝ) * h)) :
    V i ≤ interp h N V x ∧ interp h N V x ≤ V (i + 1) := by
  have hm := interp_monotone hh hV
  constructor
  · calc V i = interp h N V (i * h) := (interp_natCast hh hi.le).symm
      _ ≤ interp h N V x := hm hx.1
  · calc interp h N V x ≤ interp h N V (((i + 1 : ℕ) : ℝ) * h) := hm (by push_cast; exact hx.2)
      _ = V (i + 1) := interp_natCast hh hi

end Molico
