import MonetaryExistenceBuyer.Saturation.Defs

/-!
# Tightness (`prop:count`)

Proof structure (`existence-theorem.tex`, proof of `prop:count`):
* `count_strictMono`: with asymptotic saturation, `W` is strictly increasing on `(0, ∞)`;
* `count_gain`, `count_shift_loss`: the shift-gain estimate `eq:shiftgain` and the
  concavity-through-the-origin loss estimate `eq:shiftloss`, in index form;
* `count_gridB`, `count_gridS`: the shifted transfers `d ∓ e_n λ_n` strictly improve the grid
  objective (cases `B` and `S` of Step 1);
* `count_noTriple`: no optimal grid triple lies in the open event `E^B_{n,T} ∪ E^S_{n,T}`;
* `count_step1_open`, `count_step1`: Step 1, `Γ̂({b = ∞} ∩ {min(B, S) < ∞}) = 0`;
* Step 2 (the identity `ϖ = ϖ² / 2 + ϖ / 2`) in the proof of `NormalizedLimit.count`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### Grid estimates -/

/-- Increments after `p` are at most the increment at `p`: `V(p+k) - V(p) ≤ k (V(p+1) - V(p))`. -/
private lemma count_incr_le_mul {V : ℕ → ℝ} {N : ℕ} (hV : IncrSeq V N) {p : ℕ} :
    ∀ k : ℕ, p + k ≤ N → V (p + k) - V p ≤ k * (V (p + 1) - V p) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := hV.step_anti (x := p) (y := p + k) (by omega) (by omega)
    rw [← add_assoc]
    push_cast
    linarith

/-- Increments before `p` are at least the increment at `p`: `i (V(p+1) - V(p)) ≤ V(i)`. -/
private lemma count_mul_slope_le {V : ℕ → ℝ} {N : ℕ} (hV : IncrSeq V N) (hV0 : V 0 = 0)
    {p : ℕ} (hp : p + 1 ≤ N) : ∀ i : ℕ, i ≤ p → (i : ℝ) * (V (p + 1) - V p) ≤ V i := by
  intro i
  induction i with
  | zero => intro _; simp [hV0]
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := hV.step_anti (x := i) (y := p) (by omega) hp
    push_cast
    linarith

/-- Concavity through the origin in index form (`eq:shiftloss`): `p (V(p+k) - V(p)) ≤ k V(p)`. -/
private lemma count_shift_loss {V : ℕ → ℝ} {N : ℕ} (hV : IncrSeq V N) (hV0 : V 0 = 0)
    {p k : ℕ} (hpk : p + k ≤ N) : (p : ℝ) * (V (p + k) - V p) ≤ k * V p := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h1 := count_incr_le_mul hV k hpk
  have h2 := count_mul_slope_le hV hV0 (p := p) (by omega) p le_rfl
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (p : ℝ) * (V (p + k) - V p) ≤ p * (k * (V (p + 1) - V p)) :=
        mul_le_mul_of_nonneg_left h1 hp
    _ = k * (p * (V (p + 1) - V p)) := by ring
    _ ≤ k * V p := mul_le_mul_of_nonneg_left h2 hk'

/-- The shift-gain estimate `eq:shiftgain` in index form: for a grid point `i h ≤ x` and a shift
`k h ≥ t ≥ 0`, the grid increment `V(i+k) - V(i)` dominates `V_n(x + t) - V_n(x)`. -/
private lemma count_gain {h : ℝ} (hh : 0 < h) {N : ℕ} {V : ℕ → ℝ} (hV : IncrSeq V N)
    {i k : ℕ} (hik : i + k ≤ N) {x t : ℝ} (hix : (i : ℝ) * h ≤ x) (hkt : t ≤ k * h) :
    interp h N V (x + t) - interp h N V x ≤ V (i + k) - V i := by
  have hf := interp_concaveOn hh hV
  have hmono := interp_monotone hh hV
  have h1 := concave_incr_anti hf (x := i * h) (y := x) (t := k * h) (by positivity) hix
    (by positivity)
  have h2 := hmono (show x + t ≤ x + k * h by linarith)
  have e1 : interp h N V ((i : ℝ) * h + k * h) = V (i + k) := by
    rw [← interp_natCast hh hik (V := V)]
    push_cast
    ring_nf
  have e2 : interp h N V ((i : ℝ) * h) = V i := interp_natCast hh (by omega)
  rw [e1, e2] at h1
  linarith

/-- Case `B` of Step 1 (grid form): if the buyer can gain `γ` by keeping `k` more grid steps,
while the seller's loss is controlled by concavity through the origin, then the transfer `j` is
not optimal. -/
private lemma count_gridB {N : ℕ} {V : ℕ → ℝ} (hV : Grid.InCone P.Cstar N V)
    {m l j k : ℕ} (hm : m ≤ N) (hl : l ≤ N) (hj : j ∈ Grid.feas N m l)
    (hopt : Grid.gobj P.U.u V m l j = Grid.gH P.U.u N V m l) {γ : ℝ} (hkj : k ≤ j)
    (hgain : γ ≤ V (m - j + k) - V (m - j))
    (hloss : P.U.c0 * k * P.Cstar < γ * ((j - k : ℕ) : ℝ)) : False := by
  have hjf := (Grid.mem_feas hm hl).1 hj
  set p := j - k with hp_def
  have hpk : p + k = j := by omega
  have hpf : p ∈ Grid.feas N m l := (Grid.mem_feas hm hl).2 ⟨by omega, by omega⟩
  have hle := Grid.gobj_le_gH P.U hm hl hpf (V := V)
  rw [← hopt] at hle
  simp only [Grid.gobj] at hle
  have hmp : m - p = m - j + k := by omega
  rw [hmp] at hle
  -- the seller's loss
  have hV0 := hV.zero
  have hVi := hV.incr
  have hx0 : 0 ≤ V (l + p) - V l := by
    linarith [hVi.le_of_le (show l ≤ l + p by omega) (by omega)]
  have hxy : V (l + p) - V l ≤ V (l + j) - V l := by
    linarith [hVi.le_of_le (show l + p ≤ l + j by omega) (by omega)]
  have hu := P.U.sub_le_c0_mul hx0 hxy
  have hinc : V (l + j) - V (l + p) ≤ V (p + k) - V p := by
    have := hVi.incr_anti (x := p) (y := l + p) (t := k) (by omega) (by omega)
    rw [show l + p + k = l + j by omega] at this
    exact this
  rw [hpk] at hinc
  have hsl := count_shift_loss hVi hV0 (p := p) (k := k) (by omega)
  rw [hpk] at hsl
  have hVp : V p ≤ P.Cstar := hV.le p (by omega)
  have hc0 := P.U.c0_pos
  have hpnn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hknn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- `γ ≤ c₀ (V(j) - V(p))`
  have hγ : γ ≤ P.U.c0 * (V j - V p) := by
    have : P.U.c0 * (V (l + j) - V l - (V (l + p) - V l)) ≤ P.U.c0 * (V j - V p) := by
      apply mul_le_mul_of_nonneg_left _ hc0.le
      linarith
    linarith
  have h1 : γ * p ≤ P.U.c0 * (p * (V j - V p)) := by
    have := mul_le_mul_of_nonneg_right hγ hpnn
    linarith
  have h2 : P.U.c0 * (p * (V j - V p)) ≤ P.U.c0 * (k * P.Cstar) := by
    apply mul_le_mul_of_nonneg_left _ hc0.le
    exact hsl.trans (mul_le_mul_of_nonneg_left hVp hknn)
  linarith

/-- Case `S` of Step 1 (grid form): if the seller can gain `u'₋(C_*) γ` by receiving `k` more grid
steps, while the buyer's loss is controlled by concavity through the origin, then the transfer `j`
is not optimal. -/
private lemma count_gridS {N : ℕ} {V : ℕ → ℝ} (hV : Grid.InCone P.Cstar N V)
    {m l j k : ℕ} (hm : m ≤ N) (hl : l ≤ N)
    (hopt : Grid.gobj P.U.u V m l j = Grid.gH P.U.u N V m l) {γ : ℝ}
    (hjk : j + k ≤ m) (hN : l + j + k ≤ N)
    (hgain : γ ≤ V (l + j + k) - V (l + j))
    (hloss : k * P.Cstar < P.U.marg P.Cstar * γ * ((m - j - k : ℕ) : ℝ)) : False := by
  set p := m - j - k with hp_def
  have hpk : p + k = m - j := by omega
  have hjf : j + k ∈ Grid.feas N m l := (Grid.mem_feas hm hl).2 ⟨by omega, by omega⟩
  have hle := Grid.gobj_le_gH P.U hm hl hjf (V := V)
  rw [← hopt] at hle
  simp only [Grid.gobj] at hle
  rw [show m - (j + k) = p by omega, show l + (j + k) = l + j + k by omega] at hle
  have hV0 := hV.zero
  have hVi := hV.incr
  -- the seller's gain
  have ha0 : 0 ≤ V (l + j) - V l := by
    linarith [hVi.le_of_le (show l ≤ l + j by omega) (by omega)]
  have hab : V (l + j) - V l ≤ V (l + j + k) - V l := by
    linarith [hVi.le_of_le (show l + j ≤ l + j + k by omega) hN]
  have hb : V (l + j + k) - V l ≤ P.Cstar := by
    linarith [hV.le (l + j + k) hN, hVi.nonneg hV0 hl]
  have hu := P.U.marg_mul_le_sub ha0 hab
  have hmarg : P.U.marg P.Cstar ≤ P.U.marg (V (l + j + k) - V l) :=
    P.U.marg_antitoneOn (ha0.trans hab) (show (0 : ℝ) ≤ P.Cstar from P.Cstar_pos.le) hb
  have hgain' : 0 ≤ V (l + j + k) - V (l + j) := by
    have := hVi.le_of_le (show l + j ≤ l + j + k by omega) hN
    linarith
  have hmpos := P.marg_Cstar_pos
  have hsg : P.U.marg P.Cstar * γ ≤
      P.U.u (V (l + j + k) - V l) - P.U.u (V (l + j) - V l) := by
    have e : V (l + j + k) - V l - (V (l + j) - V l) = V (l + j + k) - V (l + j) := by ring
    rw [e] at hu
    calc P.U.marg P.Cstar * γ ≤ P.U.marg P.Cstar * (V (l + j + k) - V (l + j)) :=
          mul_le_mul_of_nonneg_left hgain hmpos.le
      _ ≤ P.U.marg (V (l + j + k) - V l) * (V (l + j + k) - V (l + j)) :=
          mul_le_mul_of_nonneg_right hmarg hgain'
      _ ≤ _ := hu
  -- the buyer's loss
  have hsl := count_shift_loss hVi hV0 (p := p) (k := k) (by omega)
  rw [hpk] at hsl
  have hVp : V p ≤ P.Cstar := hV.le p (by omega)
  have hpnn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hknn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hγ : P.U.marg P.Cstar * γ ≤ V (m - j) - V p := by linarith
  have h1 : P.U.marg P.Cstar * γ * p ≤ p * (V (m - j) - V p) := by
    have := mul_le_mul_of_nonneg_right hγ hpnn
    linarith
  have h2 : (p : ℝ) * (V (m - j) - V p) ≤ k * P.Cstar :=
    hsl.trans (mul_le_mul_of_nonneg_left hVp hknn)
  linarith

/-- Step 1 at a fixed grid (both cases): with the shift `k = ⌈e/h⌉` (so that `e ≤ k h ≤ Λ e`,
i.e. `1 ≤ λ_n ≤ Λ` in normalized units), no optimal triple `(m, l, j)` has normalized buyer
wealth `m h / e > T` and normalized landing `(m - j) h / e < K` or `(l + j) h / e < K`. -/
private lemma count_noTriple {N : ℕ} {V : ℕ → ℝ} (hV : Grid.InCone P.Cstar N V)
    {h e K Λ T γ : ℝ} (hh : 0 < h) (he : 0 < e) (hγ : 0 < γ)
    (hgain : γ ≤ interp h N V (e * K + e) - interp h N V (e * K))
    (hΛ : e + h ≤ Λ * e) (hNK : (K + Λ) * e ≤ N * h)
    (hTB : P.U.c0 * Λ * P.Cstar ≤ γ * (T - K - Λ))
    (hTS : Λ * P.Cstar ≤ P.U.marg P.Cstar * γ * (T - K - Λ)) (hT : K + Λ < T)
    {m l j : ℕ} (hm : m ≤ N) (hl : l ≤ N) (hj : j ∈ Grid.feas N m l)
    (hopt : Grid.gobj P.U.u V m l j = Grid.gH P.U.u N V m l)
    (hmT : T * e < m * h) (hK : ((m : ℝ) - j) * h < K * e ∨ ((l : ℝ) + j) * h < K * e) :
    False := by
  have hjf := (Grid.mem_feas hm hl).1 hj
  set k : ℕ := ⌈e / h⌉₊ with hk_def
  have hk1 : e ≤ k * h := by
    have := Nat.le_ceil (e / h)
    rwa [div_le_iff₀ hh] at this
  have hk2 : (k : ℝ) * h ≤ Λ * e := by
    have h1 : (k : ℝ) < e / h + 1 := Nat.ceil_lt_add_one (div_nonneg he.le hh.le)
    have h2 : (k : ℝ) * h < (e / h + 1) * h := mul_lt_mul_of_pos_right h1 hh
    rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] at h2
    linarith
  have hC0 : 0 ≤ P.Cstar := P.Cstar_pos.le
  have hc0 : 0 < P.U.c0 := P.U.c0_pos
  have hmarg := P.marg_Cstar_pos
  have hD : Λ * e < (T - K) * e := mul_lt_mul_of_pos_right (by linarith) he
  have hD' : 0 < T - K - Λ := by linarith
  -- the generic shift gain
  have gain : ∀ i : ℕ, i + k ≤ N → (i : ℝ) * h ≤ e * K → γ ≤ V (i + k) - V i := fun i hik hi =>
    hgain.trans (count_gain hh hV.incr hik hi hk1)
  rcases hK with hB | hS
  · -- Case `B`: keep `k` more grid steps, `d' = d - e_n λ_n`
    have hkj' : (k : ℝ) * h < j * h := by
      have e1 : (T - K) * e = T * e - K * e := by ring
      have e3 : ((m : ℝ) - j) * h = m * h - j * h := by ring
      rw [e3] at hB; linarith
    have hkj : k ≤ j := by
      have : (k : ℝ) < j := lt_of_mul_lt_mul_right hkj' hh.le
      exact_mod_cast this.le
    have hcast : ((j - k : ℕ) : ℝ) = j - k := Nat.cast_sub hkj
    refine count_gridB hV hm hl hj hopt hkj (gain (m - j) (by omega) ?_) ?_
    · rw [Nat.cast_sub hjf.1]
      have e3 : ((m : ℝ) - j) * h = m * h - j * h := by ring
      have e4 : e * K = K * e := by ring
      linarith
    · rw [hcast]
      -- `c₀ k C h ≤ c₀ Λ C e ≤ γ (T - K - Λ) e < γ (j - k) h`
      have h1 : P.U.c0 * k * P.Cstar * h ≤ P.U.c0 * Λ * P.Cstar * e := by
        have := mul_le_mul_of_nonneg_left hk2 (mul_nonneg hc0.le hC0)
        have e1 : P.U.c0 * k * P.Cstar * h = P.U.c0 * P.Cstar * (k * h) := by ring
        have e2 : P.U.c0 * Λ * P.Cstar * e = P.U.c0 * P.Cstar * (Λ * e) := by ring
        rw [e1, e2]; exact this
      have h2 : P.U.c0 * Λ * P.Cstar * e ≤ γ * (T - K - Λ) * e :=
        mul_le_mul_of_nonneg_right hTB he.le
      have h3 : γ * (T - K - Λ) * e < γ * ((j - k) * h) := by
        have : (T - K - Λ) * e < (j - k) * h := by
          have e1 : (T - K - Λ) * e = T * e - K * e - Λ * e := by ring
          have e2 : ((j : ℝ) - k) * h = j * h - k * h := by ring
          have e3 : ((m : ℝ) - j) * h = m * h - j * h := by ring
          rw [e1, e2]; rw [e3] at hB; linarith
        have := mul_lt_mul_of_pos_left this hγ
        linarith
      have h4 : P.U.c0 * k * P.Cstar * h < γ * (j - k) * h := by
        have e1 : γ * (j - k) * h = γ * ((j - k) * h) := by ring
        rw [e1]; linarith
      exact lt_of_mul_lt_mul_right h4 hh.le
  · -- Case `S`: transfer `k` more grid steps, `d' = d + e_n λ_n`
    have hjK : (j : ℝ) * h < K * e := by
      have : (0 : ℝ) ≤ l * h := by positivity
      have e3 : ((l : ℝ) + j) * h = l * h + j * h := by ring
      linarith
    have hkm' : (k : ℝ) * h < (m - j) * h := by
      have e1 : (T - K) * e = T * e - K * e := by ring
      have e3 : ((m : ℝ) - j) * h = m * h - j * h := by ring
      linarith
    have hkm : j + k ≤ m := by
      have : (k : ℝ) < m - j := lt_of_mul_lt_mul_right hkm' hh.le
      have : ((j + k : ℕ) : ℝ) < m := by push_cast; linarith
      exact_mod_cast this.le
    have hN' : l + j + k ≤ N := by
      have : ((l + j + k : ℕ) : ℝ) * h < N * h := by
        push_cast
        have e1 : ((l : ℝ) + j + k) * h = (l + j) * h + k * h := by ring
        have e2 : (K + Λ) * e = K * e + Λ * e := by ring
        linarith
      have := lt_of_mul_lt_mul_right this hh.le
      exact_mod_cast this.le
    have hcast : ((m - j - k : ℕ) : ℝ) = m - j - k := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hjf.1]
    refine count_gridS hV hm hl hopt hkm hN' (gain (l + j) hN' ?_) ?_
    · push_cast
      have e4 : e * K = K * e := by ring
      linarith
    · rw [hcast]
      -- `k C h ≤ Λ C e ≤ u'₋(C) γ (T - K - Λ) e < u'₋(C) γ (m - j - k) h`
      have h1 : k * P.Cstar * h ≤ Λ * P.Cstar * e := by
        have := mul_le_mul_of_nonneg_left hk2 hC0
        have e1 : (k : ℝ) * P.Cstar * h = P.Cstar * (k * h) := by ring
        have e2 : Λ * P.Cstar * e = P.Cstar * (Λ * e) := by ring
        rw [e1, e2]; exact this
      have h2 : Λ * P.Cstar * e ≤ P.U.marg P.Cstar * γ * (T - K - Λ) * e :=
        mul_le_mul_of_nonneg_right hTS he.le
      have h3 : P.U.marg P.Cstar * γ * (T - K - Λ) * e <
          P.U.marg P.Cstar * γ * ((m - j - k) * h) := by
        have : (T - K - Λ) * e < (m - j - k) * h := by
          have e1 : (T - K - Λ) * e = T * e - K * e - Λ * e := by ring
          have e2 : ((m : ℝ) - j - k) * h = m * h - j * h - k * h := by ring
          rw [e1, e2]; linarith
        have := mul_lt_mul_of_pos_left this (mul_pos hmarg hγ)
        linarith
      have h4 : k * P.Cstar * h < P.U.marg P.Cstar * γ * (m - j - k) * h := by
        have e1 : P.U.marg P.Cstar * γ * (m - j - k) * h =
            P.U.marg P.Cstar * γ * ((m - j - k) * h) := by ring
        rw [e1]; linarith
      exact lt_of_mul_lt_mul_right h4 hh.le

/-! ### Step 1 -/

/-- Without a finite-wealth saturation, `W` is strictly increasing on `(0, ∞)`: if `W(x) = W(y)` for
`0 < x < y`, then concavity and monotonicity force `W ≡ W(x)` on `[x, ∞)`, so `W(x) = L`. -/
private lemma count_strictMono {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (hmono : MonotoneOn NL.Wbar (Ici 0)) (hconc : ConcaveOn ℝ (Ici 0) NL.Wbar)
    (hnp : ¬ NL.HasFiniteSaturation) {x y : ℝ} (hx : 0 < x) (hxy : x < y) : NL.W x < NL.W y := by
  have hW : ∀ z, 0 < z → NL.Wbar z = NL.W z := fun z hz => by
    simp [NormalizedLimit.Wbar, hz.ne']
  have hy : 0 < y := hx.trans hxy
  by_contra hcon
  replace hcon := not_lt.1 hcon
  have hle : NL.W x ≤ NL.W y := by
    rw [← hW x hx, ← hW y hy]; exact hmono hx.le hy.le hxy.le
  have heq : NL.W y = NL.W x := le_antisymm hcon hle
  have hub : ∀ z, 0 < z → NL.W z ≤ NL.W x := by
    intro z hz
    rcases le_or_gt z y with hzy | hzy
    · rw [← heq, ← hW z hz, ← hW y hy]; exact hmono hz.le hy.le hzy
    · have h1 := hconc.slope_anti_adjacent (show x ∈ Ici (0 : ℝ) from hx.le)
        (show z ∈ Ici (0 : ℝ) from hz.le) hxy hzy
      rw [hW x hx, hW y hy, hW z hz, heq, sub_self, zero_div] at h1
      have h2 := (div_le_iff₀ (show 0 < z - y by linarith)).1 h1
      linarith
  apply hnp
  refine ⟨x, hx, ?_⟩
  unfold NormalizedLimit.Lsup
  have hG : IsGreatest (NL.W '' Ioi 0) (NL.W x) :=
    ⟨⟨x, hx, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hub z hz⟩
  exact hG.csSup_eq.symm

/-- Step 1 for a fixed level `K > 0`: there is `T` such that the open event
`{b > T, min(B, S) < K}` is `Γ̂`-null. Prelimit, no optimal triple lies in it for large `n`
(`count_noTriple`), and the Portmanteau inequality for open sets passes this to the limit. -/
private lemma count_step1_open {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation) {K : ℝ} (hK : 0 < K) :
    ∃ T : ℝ, NL.Γh {q | ENNReal.ofReal T < q.1 ∧
      (q.2.2.2.1 < ENNReal.ofReal K ∨ q.2.2.2.2 < ENNReal.ofReal K)} = 0 := by
  obtain ⟨he0, -, -, hmono, hconc, -⟩ := NL.props ha haJ
  set γ : ℝ := (NL.W (K + 1) - NL.W K) / 2 with hγ_def
  have hγ : 0 < γ := by
    have := count_strictMono NL hmono hconc hnp hK (show K < K + 1 by linarith)
    rw [hγ_def]; linarith
  have hδ0 : 0 ≤ NL.δ := by rcases NL.lattice with ⟨h0, -⟩ | ⟨h0, -⟩ <;> linarith
  set Λ : ℝ := NL.δ + 2 with hΛ_def
  have hΛ0 : 0 ≤ Λ := by linarith
  have hC0 : 0 ≤ P.Cstar := P.Cstar_pos.le
  have hc0 : 0 < P.U.c0 := P.U.c0_pos
  have hmarg := P.marg_Cstar_pos
  set D : ℝ := P.U.c0 * Λ * P.Cstar / γ + Λ * P.Cstar / (P.U.marg P.Cstar * γ) + 1
    with hD_def
  have hD1 : 0 ≤ P.U.c0 * Λ * P.Cstar / γ := by positivity
  have hD2 : 0 ≤ Λ * P.Cstar / (P.U.marg P.Cstar * γ) := by positivity
  set T : ℝ := K + Λ + D with hT_def
  have hTKΛ : T - K - Λ = D := by rw [hT_def]; ring
  have hTB : P.U.c0 * Λ * P.Cstar ≤ γ * (T - K - Λ) := by
    rw [hTKΛ]
    have e1 : γ * (P.U.c0 * Λ * P.Cstar / γ) = P.U.c0 * Λ * P.Cstar := by field_simp
    have e2 : γ * D = γ * (P.U.c0 * Λ * P.Cstar / γ) +
        γ * (Λ * P.Cstar / (P.U.marg P.Cstar * γ)) + γ := by rw [hD_def]; ring
    have : 0 ≤ γ * (Λ * P.Cstar / (P.U.marg P.Cstar * γ)) := mul_nonneg hγ.le hD2
    linarith
  have hTS : Λ * P.Cstar ≤ P.U.marg P.Cstar * γ * (T - K - Λ) := by
    rw [hTKΛ]
    have e1 : P.U.marg P.Cstar * γ * (Λ * P.Cstar / (P.U.marg P.Cstar * γ)) = Λ * P.Cstar := by
      field_simp
    have e2 : P.U.marg P.Cstar * γ * D =
        P.U.marg P.Cstar * γ * (P.U.c0 * Λ * P.Cstar / γ) +
        P.U.marg P.Cstar * γ * (Λ * P.Cstar / (P.U.marg P.Cstar * γ)) +
        P.U.marg P.Cstar * γ := by rw [hD_def]; ring
    have : 0 ≤ P.U.marg P.Cstar * γ * (P.U.c0 * Λ * P.Cstar / γ) :=
      mul_nonneg (mul_pos hmarg hγ).le hD1
    have : 0 ≤ P.U.marg P.Cstar * γ := (mul_pos hmarg hγ).le
    linarith
  have hT : K + Λ < T := by rw [hT_def]; linarith
  have hTpos : 0 < T := by linarith
  -- eventual facts along the subsequence
  have hconvK := NL.W_conv.tendsto_at (show K ∈ Ioi (0 : ℝ) from hK)
  have hconvK1 := NL.W_conv.tendsto_at (show K + 1 ∈ Ioi (0 : ℝ) by
    simp only [mem_Ioi]; linarith)
  have E1 : ∀ᶠ n in atTop, γ ≤ S.Wn a (NL.φ n) (K + 1) - S.Wn a (NL.φ n) K :=
    (hconvK1.sub hconvK).eventually_const_le (by rw [hγ_def]; linarith)
  have E2 : ∀ᶠ n in atTop, S.δn a (NL.φ n) ≤ NL.δ + 1 := by
    rcases NL.lattice with ⟨h0, ht⟩ | ⟨h0, ht⟩
    · exact ht.eventually (Iic_mem_nhds (by rw [h0]; norm_num))
    · exact Eventually.of_forall fun n => by rw [ht n]; linarith
  have E3 : ∀ᶠ n in atTop, (K + Λ) * S.scale a (NL.φ n) ≤ S.N (NL.φ n) * S.h (NL.φ n) := by
    have h1 : Tendsto (fun n => (K + Λ) * S.scale a (NL.φ n)) atTop (𝓝 0) := by
      simpa using he0.const_mul (K + Λ)
    have h2 := (S.R_tendsto.comp NL.φ_mono.tendsto_atTop).eventually_ge_atTop 1
    filter_upwards [h1.eventually (Iic_mem_nhds one_pos), h2] with n hn1 hn2
    exact (show (K + Λ) * S.scale a (NL.φ n) ≤ 1 from hn1).trans hn2
  set U : Set (ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞) := {q | ENNReal.ofReal T < q.1 ∧
      (q.2.2.2.1 < ENNReal.ofReal K ∨ q.2.2.2.2 < ENNReal.ofReal K)} with hU_def
  have c1 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.1 := by fun_prop
  have c4 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.2.2.1 := by fun_prop
  have c5 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.2.2.2 := by fun_prop
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const c1).inter
      ((isOpen_lt c4 continuous_const).union (isOpen_lt c5 continuous_const))
  refine ⟨T, ?_⟩
  have hΓprob : ∀ n, IsProbabilityMeasure (S.Γhat a (NL.φ n)) := fun n => by
    have : IsProbabilityMeasure (S.Γn (NL.φ n)) :=
      gridMeeting_isProb (S.h_pos _) (S.isApproxEq _)
    unfold SelectedSeq.Γhat; infer_instance
  have hlim := WeakConv.measure_open_le hΓprob NL.Γh_prob NL.Γh_conv hUo (c := 0) ?_
  · exact nonpos_iff_eq_zero.1 hlim
  filter_upwards [E1, E2, E3] with n h1 h2 h3
  have hE := S.isApproxEq (NL.φ n)
  have hh : 0 < S.h (NL.φ n) := S.h_pos _
  have he0' : 0 ≤ S.scale a (NL.φ n) := mul_nonneg hh.le (Nat.cast_nonneg _)
  have hmeas : Measurable fun p : ℝ × ℝ × ℝ =>
      (ENNReal.ofReal (p.1 / S.scale a (NL.φ n)), ENNReal.ofReal (p.2.1 / S.scale a (NL.φ n)),
        ENNReal.ofReal (p.2.2 / S.scale a (NL.φ n)),
        ENNReal.ofReal ((p.1 - p.2.2) / S.scale a (NL.φ n)),
        ENNReal.ofReal ((p.2.1 + p.2.2) / S.scale a (NL.φ n))) := by
    fun_prop
  rw [SelectedSeq.Γhat, Measure.map_apply hmeas hUo.measurableSet]
  refine le_of_eq (measure_eq_zero_iff_ae_notMem.2 ?_)
  filter_upwards [ae_gridMeeting hE] with p hp hpU
  obtain ⟨m, l, j, hm, hl, hj, -, -, -, hopt, rfl⟩ := hp
  simp only [Set.mem_preimage, hU_def, Set.mem_ofPred_eq] at hpU
  obtain ⟨hT1, hBS⟩ := hpU
  rw [ENNReal.ofReal_lt_ofReal_iff'] at hT1
  have he : 0 < S.scale a (NL.φ n) := by
    rcases he0'.eq_or_lt with h0 | h0
    · rw [← h0, div_zero] at hT1; linarith [hT1.1]
    · exact h0
  have hmT := (lt_div_iff₀ he).1 hT1.1
  have hK' : ((m : ℝ) - j) * S.h (NL.φ n) < K * S.scale a (NL.φ n) ∨
      ((l : ℝ) + j) * S.h (NL.φ n) < K * S.scale a (NL.φ n) := by
    rcases hBS with hB | hS
    · left
      rw [ENNReal.ofReal_lt_ofReal_iff'] at hB
      have := (div_lt_iff₀ he).1 hB.1
      rw [sub_mul]; exact this
    · right
      rw [ENNReal.ofReal_lt_ofReal_iff'] at hS
      have := (div_lt_iff₀ he).1 hS.1
      rw [add_mul]; exact this
  have hgain : γ ≤ interp (S.h (NL.φ n)) (S.N (NL.φ n)) (S.V (NL.φ n))
      (S.scale a (NL.φ n) * K + S.scale a (NL.φ n)) -
      interp (S.h (NL.φ n)) (S.N (NL.φ n)) (S.V (NL.φ n)) (S.scale a (NL.φ n) * K) := by
    have e1 : S.scale a (NL.φ n) * (K + 1) = S.scale a (NL.φ n) * K + S.scale a (NL.φ n) := by
      ring
    simp only [SelectedSeq.Wn, SelectedSeq.Vn] at h1
    rwa [e1] at h1
  have hΛ : S.scale a (NL.φ n) + S.h (NL.φ n) ≤ Λ * S.scale a (NL.φ n) := by
    rw [SelectedSeq.δn, div_le_iff₀ he] at h2
    rw [hΛ_def]; linarith
  exact count_noTriple hE.cone hh he hγ hgain hΛ h3 hTB hTS hT hm hl hj hopt hmT hK'

/-- Step 1, eq. `eq:step1`: `Γ̂`-a.s., `b = ∞` forces `B = S = ∞`. -/
private lemma count_step1 {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation) :
    ∀ᵐ q ∂NL.Γh, q.1 = ⊤ → q.2.2.2.1 = ⊤ ∧ q.2.2.2.2 = ⊤ := by
  have hK : ∀ K : ℕ, ∃ T : ℝ, NL.Γh {q | ENNReal.ofReal T < q.1 ∧
      (q.2.2.2.1 < ENNReal.ofReal ((K : ℝ) + 1) ∨ q.2.2.2.2 < ENNReal.ofReal ((K : ℝ) + 1))} = 0 :=
    fun K => count_step1_open NL ha haJ hnp (by positivity)
  choose T hT using hK
  have hae := ae_all_iff.2 fun K => measure_eq_zero_iff_ae_notMem.1 (hT K)
  filter_upwards [hae] with q hq hb
  have hKle : ∀ K : ℕ, (K : ℝ≥0∞) ≤ ENNReal.ofReal ((K : ℝ) + 1) := fun K => by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hTlt : ∀ K : ℕ, ENNReal.ofReal (T K) < q.1 := fun K => by
    rw [hb]; exact ENNReal.ofReal_lt_top
  by_contra hcon
  rw [not_and_or] at hcon
  rcases hcon with h | h
  · obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt h
    exact hq K ⟨hTlt K, Or.inl (hK.trans_le (hKle K))⟩
  · obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt h
    exact hq K ⟨hTlt K, Or.inr (hK.trans_le (hKle K))⟩

/-! ### Step 2 -/

/-- `prop:count` (almost surely finite normalized wealth): every normalized limit with asymptotic saturation satisfies
`α({z < ∞}) = 1`. -/
theorem NormalizedLimit.count {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation) :
    NL.α {p | p.1 = ⊤} = 0 := by
  obtain ⟨hprod, hstat, hgeom⟩ := NL.flowpassage ha haJ
  have h1 := count_step1 NL ha haJ hnp
  have := NL.Γh_prob
  have := NL.α_prob
  have hwprob : IsProbabilityMeasure NL.αw := by unfold NormalizedLimit.αw; infer_instance
  set F : Set ℝ≥0∞ := {x | x < ⊤} with hF
  have hFm : MeasurableSet F := measurableSet_lt measurable_id measurable_const
  -- `Γ̂`-a.s.: `{B < ∞} = {b < ∞}` and `{S < ∞} = {b < ∞, z < ∞}`
  have hBae : {q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ | q.2.2.2.1 < ⊤} =ᵐ[NL.Γh]
      {q | q.1 < ⊤} := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hgeom, h1] with q hg hs
    show q.2.2.2.1 < ⊤ ↔ q.1 < ⊤
    constructor
    · intro hB
      by_contra hb
      rw [not_lt, top_le_iff] at hb
      rw [(hs hb).1] at hB
      exact lt_irrefl _ hB
    · intro hb; exact hg.2.1.trans_lt hb
  have hSae : {q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ | q.2.2.2.2 < ⊤} =ᵐ[NL.Γh]
      {q | q.1 < ⊤ ∧ q.2.1 < ⊤} := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hgeom, h1] with q hg hs
    show q.2.2.2.2 < ⊤ ↔ q.1 < ⊤ ∧ q.2.1 < ⊤
    constructor
    · intro hS
      refine ⟨?_, hg.2.2.1.trans_lt hS⟩
      by_contra hb
      rw [not_lt, top_le_iff] at hb
      rw [(hs hb).2] at hS
      exact lt_irrefl _ hS
    · rintro ⟨hb, hz⟩
      have : q.2.2.2.1 + q.2.2.2.2 < ⊤ := by
        rw [hg.2.2.2]; exact ENNReal.add_lt_top.2 ⟨hb, hz⟩
      exact (ENNReal.add_lt_top.1 this).2
  -- the `(b, z)`-marginal is `α^w ⊗ α^w`
  have hmb : NL.Γh {q | q.1 < ⊤} = NL.αw F := by
    have := congrArg (fun ν : Measure (ℝ≥0∞ × ℝ≥0∞) => ν (F ×ˢ univ)) hprod
    rw [Measure.map_apply (by fun_prop) (hFm.prod MeasurableSet.univ), Measure.prod_prod,
      measure_univ, mul_one] at this
    rw [← this]
    congr 1
    ext q
    simp [hF]
  have hmbz : NL.Γh {q | q.1 < ⊤ ∧ q.2.1 < ⊤} = NL.αw F * NL.αw F := by
    have := congrArg (fun ν : Measure (ℝ≥0∞ × ℝ≥0∞) => ν (F ×ˢ F)) hprod
    rw [Measure.map_apply (by fun_prop) (hFm.prod hFm), Measure.prod_prod] at this
    rw [← this]
    rfl
  -- stationarity `α^w = ½ B_# Γ̂ + ½ S_# Γ̂`
  have hwF : NL.αw F = 2⁻¹ * NL.Γh {q | q.2.2.2.1 < ⊤} + 2⁻¹ * NL.Γh {q | q.2.2.2.2 < ⊤} := by
    have := congrArg (fun ν : Measure ℝ≥0∞ => ν F) hstat
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at this
    rw [Measure.map_apply (by fun_prop) hFm, Measure.map_apply (by fun_prop) hFm] at this
    exact this
  rw [measure_congr hBae, measure_congr hSae, hmb, hmbz] at hwF
  -- `ϖ ≥ μ_c > 0` by `prop:non-escape`
  have hpos : 0 < NL.αw F := by
    have hle : NL.α {p | p.1 ≤ ENNReal.ofReal (P.U.c0 * P.Cstar / a)} ≤ NL.αw F := by
      rw [NormalizedLimit.αw, Measure.map_apply measurable_fst hFm]
      apply measure_mono
      intro p hp
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hF] at hp ⊢
      exact hp.trans_lt ENNReal.ofReal_lt_top
    exact (ENNReal.ofReal_pos.2 P.μc_pos).trans_le ((NL.nonEscape ha haJ).trans hle)
  -- `ϖ = ϖ/2 + ϖ²/2` and `ϖ > 0` give `ϖ = 1`
  have hw1 : NL.αw F = 1 := by
    have hfin : NL.αw F ≠ ⊤ := measure_ne_top _ _
    have hr := congrArg ENNReal.toReal hwF
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_mul] at hr
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hr
    have hrpos : 0 < (NL.αw F).toReal := ENNReal.toReal_pos hpos.ne' hfin
    have hr1 : (NL.αw F).toReal = 1 := by
      have : (NL.αw F).toReal * ((NL.αw F).toReal - 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    rw [← ENNReal.ofReal_toReal hfin, hr1, ENNReal.ofReal_one]
  -- conclusion
  have hc : NL.αw Fᶜ = 0 := (prob_compl_eq_zero_iff hFm).2 hw1
  rw [NormalizedLimit.αw, Measure.map_apply measurable_fst hFm.compl] at hc
  convert hc using 2
  ext p
  simp [hF, lt_top_iff_ne_top]

end Molico
