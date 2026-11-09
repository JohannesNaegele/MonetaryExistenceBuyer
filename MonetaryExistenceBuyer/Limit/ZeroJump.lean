import MonetaryExistenceBuyer.Limit.HalfLevel
import MonetaryExistenceBuyer.Limit.TailSeller
import MonetaryExistenceBuyer.Prelim.Device

/-!
# The zero-jump branch (`thm:zerojump`)

If the limit has no jump at the origin, the limit objects form a stationary monetary
equilibrium in relaxed strategies (of mean `∫ x dη ∈ (0, M]`).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### Step 0: the value functions -/

/-- The interpolants take values in `[0, L_*]`. -/
private lemma zj_Vn_bd (S : SelectedSeq P) (n : ℕ) (x : ℝ) :
    0 ≤ S.Vn n x ∧ S.Vn n x ≤ P.Lstar := by
  have h1 := interp_mem_Icc (S.h_pos n) (S.isApproxEq n).cone.incr x
  rw [(S.isApproxEq n).cone.zero] at h1
  exact ⟨h1.1, h1.2.trans (S.floor n).2⟩

private lemma zj_Vn_mono (S : SelectedSeq P) (n : ℕ) : MonotoneOn (S.Vn n) (Ici 0) :=
  (interp_monotone (S.h_pos n) (S.isApproxEq n).cone.incr).monotoneOn _

private lemma zj_Vn_conc (S : SelectedSeq P) (n : ℕ) : ConcaveOn ℝ (Ici 0) (S.Vn n) :=
  interp_concaveOn (S.h_pos n) (S.isApproxEq n).cone.incr

private lemma zj_Vn_zero (S : SelectedSeq P) (n : ℕ) : S.Vn n 0 = 0 := by
  show interp _ _ _ 0 = 0
  rw [interp_of_nonpos (S.h_pos n) le_rfl, (S.isApproxEq n).cone.zero]

/-- Grid values are values of the interpolant. -/
private lemma zj_V_eq (S : SelectedSeq P) (n : ℕ) {i : ℕ} (hi : i ≤ S.N n) :
    S.V n i = S.Vn n (i * S.h n) :=
  (interp_natCast (S.h_pos n) hi).symm

/-- Small values near the origin (no jump). -/
private lemma zj_Vlim_small (S : SelectedSeq P) (h0 : S.jump = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ x0 > 0, ∀ t, 0 ≤ t → t ≤ x0 → S.Vlim t < ε := by
  have hne : (S.Vlim '' Ioi 0).Nonempty := ⟨_, mem_image_of_mem _ (mem_Ioi.2 (one_pos : (0:ℝ) < 1))⟩
  have hlt : sInf (S.Vlim '' Ioi 0) < ε := by
    have : S.jump = sInf (S.Vlim '' Ioi 0) := rfl
    linarith
  obtain ⟨_, ⟨x0, hx0, rfl⟩, hlt'⟩ := exists_lt_of_csInf_lt hne hlt
  refine ⟨x0, hx0, fun t ht htx => lt_of_le_of_lt ?_ hlt'⟩
  exact S.limit_props.1 ht (show x0 ∈ Ici (0:ℝ) from mem_Ici.2 (le_of_lt hx0)) htx

private lemma zj_Vlim_continuousOn (S : SelectedSeq P) (h0 : S.jump = 0) :
    ContinuousOn S.Vlim (Ici 0) := by
  intro x hx
  rcases (show (0:ℝ) ≤ x from hx).eq_or_lt with rfl | hpos
  · rw [ContinuousWithinAt, S.Vlim_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨x0, hx0, hsmall⟩ := zj_Vlim_small S h0 hε
    filter_upwards [Ico_mem_nhdsGE hx0] with t ht
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (S.limit_props.2.2.1 t ht.1).1]
    exact hsmall t ht.1 ht.2.le
  · have hc := (concave_limit_props (B := P.Lstar) (zj_Vn_mono S) (zj_Vn_conc S)
      (fun n x _ => zj_Vn_bd S n x) S.V_conv).2.2.1
    exact (hc.continuousAt (Ioi_mem_nhds hpos)).continuousWithinAt

/-- The limit value function is admissible (`def:eq`). -/
private lemma zj_Vlim_value (S : SelectedSeq P) (h0 : S.jump = 0) : IsValueFn S.Vlim where
  zero := S.Vlim_zero
  continuousOn := zj_Vlim_continuousOn S h0
  monotoneOn := S.limit_props.1
  concaveOn := S.limit_props.2.1
  bddAbove := ⟨P.Lstar, by rintro _ ⟨x, hx, rfl⟩; exact (S.limit_props.2.2.1 x hx).2⟩

private lemma zj_Vlim_le (S : SelectedSeq P) {x : ℝ} (hx : 0 ≤ x) : S.Vlim x ≤ P.Lstar :=
  (S.limit_props.2.2.1 x hx).2

/-- `V > 0` on `(0, ∞)`. -/
private lemma zj_Vlim_pos (S : SelectedSeq P) (hnz : ∃ x > 0, S.Vlim x ≠ 0) :
    ∀ t, 0 < t → 0 < S.Vlim t := by
  obtain ⟨x, hx, hVx⟩ := hnz
  have hVx' : 0 < S.Vlim x := lt_of_le_of_ne (S.limit_props.2.2.1 x hx.le).1 (Ne.symm hVx)
  intro t ht
  rcases le_total t x with htx | htx
  · have := concave_mul_le S.limit_props.2.1 (by rw [S.Vlim_zero]) (div_nonneg ht.le hx.le)
      ((div_le_one hx).2 htx) hx.le
    rw [div_mul_cancel₀ t hx.ne'] at this
    exact lt_of_lt_of_le (mul_pos (div_pos ht hx) hVx') this
  · exact lt_of_lt_of_le hVx' (S.limit_props.1 (show x ∈ Ici (0:ℝ) from hx.le)
      (show t ∈ Ici (0:ℝ) from hx.le.trans htx) htx)

/-- Step 0: locally uniform convergence on `[0, ∞)`. -/
private lemma zj_Vn_tlu (S : SelectedSeq P) (h0 : S.jump = 0) :
    TendstoLocallyUniformlyOn S.Vn S.Vlim atTop (Ici 0) := by
  have hj : Tendsto S.Vlim (𝓝[>] 0) (𝓝 0) := by
    have := ((zj_Vlim_continuousOn S h0) 0 self_mem_Ici).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    rw [ContinuousWithinAt, S.Vlim_zero] at this
    exact this
  exact tendstoLocallyUniformlyOn_Ici_of_noJump (B := P.Lstar) (zj_Vn_mono S) (zj_Vn_conc S)
    (fun n x _ => zj_Vn_bd S n x) (zj_Vn_zero S) S.V_conv S.Vlim_zero hj

private lemma zj_Vn_unif (S : SelectedSeq P) (h0 : S.jump = 0) (T : ℝ) :
    TendstoUniformlyOn S.Vn S.Vlim atTop (Icc 0 T) :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).1
    ((zj_Vn_tlu S h0).mono Icc_subset_Ici_self)

/-- Convergence along converging arguments and a subsequence of levels. -/
private lemma zj_Vn_tendsto (S : SelectedSeq P) (h0 : S.jump = 0) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {xs : ℕ → ℝ} {x : ℝ} (hxs0 : ∀ j, 0 ≤ xs j)
    (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun j => S.Vn (ψ j) (xs j)) atTop (𝓝 (S.Vlim x)) := by
  have hx : 0 ≤ x := ge_of_tendsto' hxs hxs0
  have htlu : TendstoLocallyUniformlyOn (fun j => S.Vn (ψ j)) S.Vlim atTop (Ici 0) :=
    fun u hu y hy => by
      obtain ⟨t, ht, hev⟩ := zj_Vn_tlu S h0 u hu y hy
      exact ⟨t, ht, hψ.eventually hev⟩
  exact htlu.tendsto_comp ((zj_Vlim_continuousOn S h0) x hx) hx
    (tendsto_nhdsWithin_iff.2 ⟨hxs, Eventually.of_forall hxs0⟩)

/-- Uniform continuity of `V` on compact intervals. -/
private lemma zj_Vlim_uc (S : SelectedSeq P) (h0 : S.jump = 0) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |x - y| < ρ → |S.Vlim x - S.Vlim y| < ε := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    ((zj_Vlim_continuousOn S h0).mono (fun y (hy : y ∈ Icc 0 T) => (hy.1 : y ∈ Ici 0)))
  obtain ⟨ρ, hρ, h⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  exact ⟨ρ, hρ, fun x hx y hy hxy => by
    have := h x hx y hy (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this⟩

/-- `u` is `c₀`-Lipschitz on `[0, ∞)`. -/
private lemma zj_u_lip (U : AdmissibleUtility) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |U.u a - U.u b| ≤ U.c0 * |a - b| := by
  rcases le_total a b with hab | hab
  · rw [abs_of_nonpos (sub_nonpos.2 (U.monotoneOn ha hb hab)), abs_of_nonpos (sub_nonpos.2 hab)]
    have := U.sub_le_c0_mul ha hab
    linarith
  · rw [abs_of_nonneg (sub_nonneg.2 (U.monotoneOn hb ha hab)), abs_of_nonneg (sub_nonneg.2 hab)]
    exact U.sub_le_c0_mul hb hab

/-! ### Step 1: the maximized payoffs converge -/

/-- Step 1 (uniform form): on index pairs with wealth in `[0, T]`, the grid maximized payoff is
uniformly close to the continuum one at the same wealth pair. -/
private lemma zj_step1 (S : SelectedSeq P) (h0 : S.jump = 0) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ i l : ℕ, i ≤ S.N n → l ≤ S.N n → (i : ℝ) * S.h n ≤ T →
      (l : ℝ) * S.h n ≤ T →
      |Grid.gH P.U.u (S.N n) (S.V n) i l - bellH P.U.u S.Vlim (i * S.h n) (l * S.h n)| < ε := by
  have hV := zj_Vlim_value S h0
  have hc0 := P.U.c0_pos
  set δ := ε / (3 * P.U.c0 + 3) with hδ
  have hδpos : 0 < δ := div_pos hε (by linarith)
  have hδε : (3 * P.U.c0 + 2) * δ < ε := by
    rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]; nlinarith
  obtain ⟨ρ, hρ, huc⟩ := zj_Vlim_uc S h0 (2 * T + 1) hδpos
  have hA := Metric.tendstoUniformlyOn_iff.1 (zj_Vn_unif S h0 (2 * T + 1)) δ hδpos
  have hB := S.h_tendsto.eventually (gt_mem_nhds hρ)
  have hC := S.R_tendsto.eventually_gt_atTop (2 * T + 1)
  filter_upwards [hA, hB, hC] with n hA hB hC i l hi hl hiT hlT
  have hh := S.h_pos n
  have hincr := (S.isApproxEq n).cone.incr
  set h := S.h n with hhdef
  set x : ℝ := i * h with hx
  set s : ℝ := l * h with hs
  have hx0 : 0 ≤ x := by positivity
  have hs0 : 0 ≤ s := by positivity
  have close : ∀ y, 0 ≤ y → y ≤ 2 * T + 1 → |S.Vn n y - S.Vlim y| < δ := fun y hy0 hy1 => by
    have := hA y ⟨hy0, hy1⟩
    rwa [Real.dist_eq, abs_sub_comm] at this
  rw [abs_sub_lt_iff]
  constructor
  · -- upper bound: the grid optimum is a continuum competitor
    obtain ⟨j, hj, hjeq⟩ := Grid.exists_gH_eq P.U (V := S.V n) hi hl
    have hj' := (Grid.mem_feas hi hl).1 hj
    set d : ℝ := j * h with hd
    have hd0 : 0 ≤ d := by positivity
    have hdx : d ≤ x := mul_le_mul_of_nonneg_right (by exact_mod_cast hj'.1) hh.le
    have e1 : S.V n (l + j) = S.Vn n (s + d) := by
      rw [zj_V_eq S n hj'.2]; congr 1; push_cast; ring
    have e2 : S.V n l = S.Vn n s := zj_V_eq S n hl
    have e3 : S.V n (i - j) = S.Vn n (x - d) := by
      rw [zj_V_eq S n (by omega)]; congr 1; rw [Nat.cast_sub hj'.1]; ring
    have c1 := abs_lt.1 (close (s + d) (by positivity) (by linarith))
    have c2 := abs_lt.1 (close s hs0 (by linarith))
    have c3 := abs_lt.1 (close (x - d) (by linarith) (by linarith))
    have hg0 : 0 ≤ S.V n (l + j) - S.V n l := sub_nonneg.2 (hincr.le_of_le (by omega) hj'.2)
    have hu := zj_u_lip P.U hg0 (hV.gain_nonneg hs0 hd0)
    have hob := obj_le_bellH P.U hV hx0 hs0 ⟨hd0, hdx⟩
    rw [← hjeq, Grid.gobj]
    unfold obj gain at hob
    rw [e1, e2] at hu ⊢
    rw [e3]
    have hab : |S.Vn n (s + d) - S.Vn n s - (S.Vlim (s + d) - S.Vlim s)| < 2 * δ := by
      rw [abs_lt]; constructor <;> linarith
    have hm := mul_le_mul_of_nonneg_left hab.le hc0.le
    have hu' := (abs_le.1 (hu.trans hm)).2
    have := mul_pos hc0 hδpos
    unfold gain at hu'
    linarith
  · -- lower bound: round a continuum optimum down to the grid
    obtain ⟨d, hd, hdeq⟩ := exists_bellH_eq P.U hV hx0 hs0
    set k := ⌊d / h⌋₊ with hk
    have hk1 : (k : ℝ) * h ≤ d := (le_div_iff₀ hh).1 (Nat.floor_le (div_nonneg hd.1 hh.le))
    have hk2 : d < (k : ℝ) * h + h := by
      have := Nat.lt_floor_add_one (d / h)
      rw [div_lt_iff₀ hh] at this; linarith
    have hki : k ≤ i := Nat.floor_le_of_le ((div_le_iff₀ hh).2 hd.2)
    have hlk : l + k ≤ S.N n := by
      have h1 : ((l + k : ℕ) : ℝ) * h < (S.N n : ℝ) * h := by
        rw [Nat.cast_add, add_mul]; linarith [hd.2]
      exact_mod_cast (lt_of_mul_lt_mul_right h1 hh.le).le
    have hkf : k ∈ Grid.feas (S.N n) i l := (Grid.mem_feas hi hl).2 ⟨hki, hlk⟩
    have hle := Grid.gobj_le_gH P.U (V := S.V n) hi hl hkf
    set e : ℝ := k * h with he
    have he0 : 0 ≤ e := by positivity
    have e1 : S.V n (l + k) = S.Vn n (s + e) := by
      rw [zj_V_eq S n hlk]; congr 1; push_cast; ring
    have e2 : S.V n l = S.Vn n s := zj_V_eq S n hl
    have e3 : S.V n (i - k) = S.Vn n (x - e) := by
      rw [zj_V_eq S n (by omega)]; congr 1; rw [Nat.cast_sub hki]; ring
    have c1 := abs_lt.1 (close (s + e) (by positivity) (by linarith [hd.2]))
    have c2 := abs_lt.1 (close s hs0 (by linarith))
    have c3 := abs_lt.1 (close (x - e) (by linarith [hd.2]) (by linarith))
    have u1 := abs_lt.1 (huc (s + e) ⟨by positivity, by linarith [hd.2]⟩ (s + d)
      ⟨by linarith [hd.1], by linarith [hd.2]⟩ (by rw [abs_lt]; constructor <;> linarith))
    have u2 := abs_lt.1 (huc (x - e) ⟨by linarith [hd.2], by linarith⟩ (x - d)
      ⟨by linarith [hd.2], by linarith [hd.1]⟩ (by rw [abs_lt]; constructor <;> linarith))
    have hg0 : 0 ≤ S.V n (l + k) - S.V n l := sub_nonneg.2 (hincr.le_of_le (by omega) hlk)
    have hu := zj_u_lip P.U hg0 (hV.gain_nonneg hs0 hd.1)
    rw [← hdeq]
    unfold obj gain
    unfold Grid.gobj at hle
    rw [e1, e2, e3] at hle
    rw [e1, e2] at hu
    have hab : |S.Vn n (s + e) - S.Vn n s - (S.Vlim (s + d) - S.Vlim s)| < 3 * δ := by
      rw [abs_lt]; constructor <;> linarith
    have hm := mul_le_mul_of_nonneg_left hab.le hc0.le
    have hu' := (abs_le.1 (hu.trans hm)).1
    have := mul_pos hc0 hδpos
    unfold gain at hu'
    linarith

/-! ### Step 2: the Bellman equation passes -/

private lemma zj_ηlim_nonneg (S : SelectedSeq P) : ∀ᵐ x ∂S.ηlim, 0 ≤ x := by
  rw [ae_iff]
  have e : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [e]; exact S.limit_props.2.2.2.1

/-- Step 2, uniform comparison: for buyer indices `i_n` with `i_n h_n ≤ m` and `i_n h_n → m`,
the grid maximized payoffs `H_n(i_n, ·)` are eventually uniformly close to `H_V(m, ·)` (in its
continuous version `G(m, ·)`). The tail of sellers is controlled by `rem:tailseller`. -/
private lemma zj_step2_unif (S : SelectedSeq P) (h0 : S.jump = 0) {G : ℝ × ℝ → ℝ}
    (hG : Continuous G) (hGeq : ∀ m s, 0 ≤ m → 0 ≤ s → G (m, s) = bellH P.U.u S.Vlim m s)
    {m : ℝ} (hm : 0 ≤ m) {i : ℕ → ℕ} (him : ∀ n, (i n : ℝ) * S.h n ≤ m)
    (hit : Tendsto (fun n => (i n : ℝ) * S.h n) atTop (𝓝 m)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, i n ≤ S.N n ∧ ∀ l ≤ S.N n,
      |Grid.gH P.U.u (S.N n) (S.V n) (i n) l - G (m, l * S.h n)| < ε := by
  have hV := zj_Vlim_value S h0
  have hc0 := P.U.c0_pos
  have hL := P.Lstar_pos
  set e := ε / 3 with he
  have hepos : 0 < e := by positivity
  set S0 := P.U.c0 * (m + 1) * P.Lstar / e + 1 with hS0
  have hS0pos : 0 < S0 := by positivity
  have hS0e : P.U.c0 * (m + 1) * P.Lstar / S0 < e := by
    rw [div_lt_iff₀ hS0pos, hS0, mul_add e, mul_div_cancel₀ _ hepos.ne']; linarith
  -- a uniform bound for the tail terms
  have htail : ∀ y z : ℝ, 0 ≤ y → y ≤ m → S0 < z → P.U.c0 * y * P.Lstar / z < e := by
    intro y z hy hym hz
    refine lt_of_le_of_lt (div_le_div₀ (by positivity) ?_ hS0pos hz.le) hS0e
    have := mul_le_mul_of_nonneg_left (show y ≤ m + 1 by linarith) hc0.le
    nlinarith
  have ha := Metric.tendsto_nhds.1 (zj_Vn_tendsto S h0 tendsto_id
    (fun n => mul_nonneg (Nat.cast_nonneg _) (S.h_pos n).le) hit) e hepos
  have hb := zj_step1 S h0 (S0 + m) hepos
  have hGuc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (s := Icc (0:ℝ) (S0 + m) ×ˢ Icc (0:ℝ) (S0 + m)) hG.continuousOn
  obtain ⟨ρ, hρ, hGuc⟩ := Metric.uniformContinuousOn_iff.1 hGuc e hepos
  have hc := Metric.tendsto_nhds.1 hit ρ hρ
  have hd := S.R_tendsto.eventually_gt_atTop m
  filter_upwards [ha, hb, hc, hd] with n ha hb hc hd
  have hh := S.h_pos n
  have hiN : i n ≤ S.N n := by
    have : (i n : ℝ) * S.h n < S.N n * S.h n := (him n).trans_lt hd
    exact_mod_cast (lt_of_mul_lt_mul_right this hh.le).le
  refine ⟨hiN, fun l hl => ?_⟩
  have hs0 : 0 ≤ (l : ℝ) * S.h n := by positivity
  have hx0 : 0 ≤ (i n : ℝ) * S.h n := by positivity
  have hxm := him n
  rw [hGeq m _ hm hs0]
  by_cases hS : (l : ℝ) * S.h n ≤ S0
  · -- bulk: Step 1 and uniform continuity of `G`
    have h1 := hb (i n) l hiN hl (by linarith) (by linarith)
    have h2 := hGuc ((i n : ℝ) * S.h n, (l : ℝ) * S.h n)
      ⟨⟨hx0, by linarith⟩, ⟨hs0, by linarith⟩⟩ (m, (l : ℝ) * S.h n)
      ⟨⟨hm, by linarith⟩, ⟨hs0, by linarith⟩⟩
      (by rw [Prod.dist_eq, dist_self]; exact max_lt hc hρ)
    rw [Real.dist_eq, hGeq _ _ hx0 hs0, hGeq _ _ hm hs0] at h2
    calc |Grid.gH P.U.u (S.N n) (S.V n) (i n) l - bellH P.U.u S.Vlim m (l * S.h n)|
        ≤ |Grid.gH P.U.u (S.N n) (S.V n) (i n) l -
            bellH P.U.u S.Vlim ((i n : ℝ) * S.h n) (l * S.h n)| +
          |bellH P.U.u S.Vlim ((i n : ℝ) * S.h n) (l * S.h n) -
            bellH P.U.u S.Vlim m (l * S.h n)| := abs_sub_le _ _ _
      _ < e + e := add_lt_add h1 h2
      _ ≤ ε := by linarith
  · -- tail: `rem:tailseller` on the grid and in the continuum
    replace hS := not_le.1 hS
    have hl1 : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with h | h
      · subst h; simp only [Nat.cast_zero, zero_mul] at hS; linarith
      · exact h
    have hlpos : (0:ℝ) < l := by exact_mod_cast hl1
    have hsp : 0 < (l : ℝ) * S.h n := by positivity
    have hT1 := tailseller_grid P.U (S.isApproxEq n).cone.incr (S.isApproxEq n).cone.zero
      (L := P.Lstar) (fun j hj => by rw [zj_V_eq S n hj]; exact (zj_Vn_bd S n _).2) hiN hl1 hl
    have hT2 := tailseller_cont P.U hV (L := P.Lstar) (fun x hx => zj_Vlim_le S hx) hm hsp
    have e1 : P.U.c0 * (i n : ℝ) * P.Lstar / l =
        P.U.c0 * ((i n : ℝ) * S.h n) * P.Lstar / (l * S.h n) := by
      field_simp
    have t1 := htail _ _ hx0 hxm hS
    have t2 := htail _ _ hm le_rfl hS
    rw [← e1] at t1
    have hVi := ha
    rw [Real.dist_eq, id, ← zj_V_eq S n hiN] at hVi
    have k1 := abs_lt.1 hVi
    rw [abs_lt]
    constructor <;> linarith [hT1.1, hT1.2.1, hT1.2.2.1, hT1.2.2.2, hT2.1, hT2.2.1, hT2.2.2.1,
      hT2.2.2.2]

/-- Step 2: the limit objects satisfy the Bellman equation `V = T_η V` on `[0, ∞)`. -/
private lemma zj_step2 (S : SelectedSeq P) (h0 : S.jump = 0) {m : ℝ} (hm : 0 ≤ m) :
    S.Vlim m = bellT P.U.u P.β S.ηlim S.Vlim m := by
  have hV := zj_Vlim_value S h0
  obtain ⟨G, hG, hGb, hGeq⟩ := exists_continuous_bellH P.U hV
  set i : ℕ → ℕ := fun n => ⌊m / S.h n⌋₊ with hidef
  have him : ∀ n, (i n : ℝ) * S.h n ≤ m := fun n =>
    (le_div_iff₀ (S.h_pos n)).1 (Nat.floor_le (div_nonneg hm (S.h_pos n).le))
  have him' : ∀ n, m - S.h n < (i n : ℝ) * S.h n := fun n => by
    have := Nat.lt_floor_add_one (m / S.h n)
    rw [div_lt_iff₀ (S.h_pos n)] at this
    simp only [hidef]; linarith
  have hit : Tendsto (fun n => (i n : ℝ) * S.h n) atTop (𝓝 m) := by
    have h1 : Tendsto (fun n => m - S.h n) atTop (𝓝 m) := by
      simpa using (tendsto_const_nhds (x := m)).sub S.h_tendsto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun n => (him' n).le)
      him
  -- the bounded continuous function `G(m, ·)`
  let g : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun s => G (m, s))
      (hG.comp (Continuous.prodMk continuous_const continuous_id)) (P.U.ubar + hV.sup)
      (fun s => by rw [Real.norm_eq_abs, abs_of_nonneg (hGb _).1]; exact (hGb _).2)
  have t2 : Tendsto (fun n => ∫ s, g s ∂gridMeasure (S.h n) (S.N n) (S.η n)) atTop
      (𝓝 (∫ s, g s ∂S.ηlim)) := S.η_conv g
  have t1 := zj_Vn_tendsto S h0 tendsto_id
    (fun n => mul_nonneg (Nat.cast_nonneg _) (S.h_pos n).le) hit
  have hdiff : Tendsto (fun n => S.Vn (id n) ((i n : ℝ) * S.h n) -
      P.β * ∫ s, g s ∂gridMeasure (S.h n) (S.N n) (S.η n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [zj_step2_unif S h0 hG hGeq hm him hit (half_pos hε)] with n hn
    obtain ⟨hiN, hn⟩ := hn
    have hη := (S.isApproxEq n).law
    rw [id, ← zj_V_eq S n hiN, (S.isApproxEq n).bellman (i n) hiN, Grid.gT,
      integral_gridMeasure hη.nonneg, Real.dist_eq, sub_zero, ← mul_sub,
      ← Finset.sum_sub_distrib, abs_mul, abs_of_pos P.β_pos]
    have hsum : |∑ l ∈ Finset.range (S.N n + 1), (S.η n l * Grid.gH P.U.u (S.N n) (S.V n) (i n) l -
        S.η n l * g (l * S.h n))| ≤ ε / 2 := by
      calc _ ≤ ∑ l ∈ Finset.range (S.N n + 1), |S.η n l * Grid.gH P.U.u (S.N n) (S.V n) (i n) l -
            S.η n l * g (l * S.h n)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l ∈ Finset.range (S.N n + 1), S.η n l * (ε / 2) := by
            refine Finset.sum_le_sum fun l hl => ?_
            rw [← mul_sub, abs_mul, abs_of_nonneg (hη.nonneg l)]
            exact mul_le_mul_of_nonneg_left
              (hn l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))).le (hη.nonneg l)
        _ = ε / 2 := by rw [← Finset.sum_mul, hη.sum_one, one_mul]
    calc P.β * _ ≤ 1 * (ε / 2) :=
          mul_le_mul P.β_lt_one.le hsum (abs_nonneg _) zero_le_one
      _ < ε := by linarith
  have hlim := tendsto_nhds_unique (t1.sub (t2.const_mul P.β)) hdiff
  have hint : ∫ s, g s ∂S.ηlim = ∫ s, bellH P.U.u S.Vlim m s ∂S.ηlim :=
    integral_congr_ae ((zj_ηlim_nonneg S).mono fun s hs => hGeq m s hm hs)
  rw [bellT, ← hint]
  linarith

/-! ### Step 3: the meeting measures pass -/

/-- Meeting triples with nonnegative wealths, `{b ≥ 0, s ≥ 0, 0 ≤ d ≤ b}` (a closed set). -/
private def zjQ : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ p.1}

private lemma zjQ_closed : IsClosed zjQ := by
  show IsClosed ({p : ℝ × ℝ × ℝ | 0 ≤ p.1} ∩ ({p | 0 ≤ p.2.1} ∩ ({p | 0 ≤ p.2.2} ∩
    {p | p.2.2 ≤ p.1})))
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter
      ((isClosed_le continuous_const (continuous_snd.comp continuous_snd)).inter
        (isClosed_le (continuous_snd.comp continuous_snd) continuous_fst)))

private lemma zj_Γn_prob (S : SelectedSeq P) (n : ℕ) : IsProbabilityMeasure (S.Γn n) :=
  gridMeeting_isProb (S.h_pos n) (S.isApproxEq n)

private lemma zj_ηn_prob (S : SelectedSeq P) (n : ℕ) : IsProbabilityMeasure (S.ηn n) :=
  gridMeasure_isProb (S.isApproxEq n).law

private lemma zj_Γn_Q (S : SelectedSeq P) (n : ℕ) : S.Γn n zjQᶜ = 0 := by
  have hae : ∀ᵐ p ∂S.Γn n, _ := ae_gridMeeting (S.isApproxEq n)
  have : ∀ᵐ p ∂S.Γn n, p ∈ zjQ := by
    filter_upwards [hae] with p hp
    obtain ⟨m, l, j, hm, hl, hj, -, -, -, -, hp⟩ := hp
    subst hp
    have hj' := (Grid.mem_feas hm hl).1 hj
    have hh := S.h_pos n
    exact ⟨by positivity, by positivity, by positivity,
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj'.1) hh.le⟩
  exact mem_ae_iff.1 this

/-- The meeting measures are tight: their `(b,s)`-marginals are `η_n ⊗ η_n` (Markov) and
`0 ≤ d ≤ b`. -/
private lemma zj_Γn_tight (S : SelectedSeq P) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set (ℝ × ℝ × ℝ), IsCompact K ∧ ∀ n, S.Γn n Kᶜ ≤ ε := by
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun n => by rw [htop]; exact le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  set A := 2 * P.M / ε.toReal with hA
  have hApos : 0 < A := div_pos (by linarith [P.M_pos]) he
  refine ⟨Icc 0 A ×ˢ Icc 0 A ×ˢ Icc 0 A, isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc),
    fun n => ?_⟩
  have mP : Measurable pairBS := by unfold pairBS; fun_prop
  have hsub : (Icc 0 A ×ˢ Icc 0 A ×ˢ Icc 0 A)ᶜ ⊆
      zjQᶜ ∪ pairBS ⁻¹' (Ioi A ×ˢ univ) ∪ pairBS ⁻¹' (univ ×ˢ Ioi A) := by
    intro p hp
    by_contra hcon
    simp only [mem_union, mem_compl_iff, mem_preimage, pairBS, mem_prod, mem_Ioi, mem_univ,
      and_true, true_and, not_or, not_not, not_lt] at hcon
    obtain ⟨⟨⟨q1, q2, q3, q4⟩, h1⟩, h2⟩ := hcon
    exact hp ⟨⟨q1, h1⟩, ⟨q2, h2⟩, ⟨q3, q4.trans h1⟩⟩
  have hmarg : (S.Γn n).map pairBS = (S.ηn n).prod (S.ηn n) :=
    gridMeeting_marginal (S.h_pos n) (S.isApproxEq n)
  have := zj_ηn_prob S n
  have h1 : S.Γn n (pairBS ⁻¹' (Ioi A ×ˢ univ)) = S.ηn n (Ioi A) := by
    rw [← Measure.map_apply mP (measurableSet_Ioi.prod MeasurableSet.univ), hmarg,
      Measure.prod_prod, measure_univ, mul_one]
  have h2 : S.Γn n (pairBS ⁻¹' (univ ×ˢ Ioi A)) = S.ηn n (Ioi A) := by
    rw [← Measure.map_apply mP (MeasurableSet.univ.prod measurableSet_Ioi), hmarg,
      Measure.prod_prod, measure_univ, one_mul]
  have hM : S.ηn n (Ioi A) ≤ ENNReal.ofReal (ε.toReal / 2) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity), ← measureReal_def]
    calc (S.ηn n).real (Ioi A) ≤ P.M / A :=
          gridMeasure_Ioi_le (S.h_pos n).le (S.isApproxEq n).law hApos
      _ = ε.toReal / 2 := by have := P.M_pos.ne'; rw [hA]; field_simp
  calc S.Γn n (Icc 0 A ×ˢ Icc 0 A ×ˢ Icc 0 A)ᶜ
      ≤ S.Γn n (zjQᶜ ∪ pairBS ⁻¹' (Ioi A ×ˢ univ) ∪ pairBS ⁻¹' (univ ×ˢ Ioi A)) :=
        measure_mono hsub
    _ ≤ S.Γn n zjQᶜ + S.Γn n (pairBS ⁻¹' (Ioi A ×ˢ univ)) +
          S.Γn n (pairBS ⁻¹' (univ ×ˢ Ioi A)) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ 0 + ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal (ε.toReal / 2) := by
        rw [zj_Γn_Q S n, h1, h2]; gcongr
    _ = ε := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
          ENNReal.ofReal_toReal htop]

/-- Weak convergence of the mixtures `½ μ_n + ½ ν_n`. -/
private lemma zj_weakConv_half {μs νs : ℕ → Measure ℝ} {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμs : ∀ n, IsFiniteMeasure (μs n)) (hνs : ∀ n, IsFiniteMeasure (νs n))
    (h1 : WeakConv μs μ) (h2 : WeakConv νs ν) :
    WeakConv (fun n => (2⁻¹ : ℝ≥0∞) • μs n + (2⁻¹ : ℝ≥0∞) • νs n)
      ((2⁻¹ : ℝ≥0∞) • μ + (2⁻¹ : ℝ≥0∞) • ν) := by
  intro f
  have h2ne : (2⁻¹ : ℝ≥0∞) ≠ ⊤ := ENNReal.inv_ne_top.2 two_ne_zero
  have key : ∀ a b : Measure ℝ, IsFiniteMeasure a → IsFiniteMeasure b →
      ∫ x, f x ∂((2⁻¹ : ℝ≥0∞) • a + (2⁻¹ : ℝ≥0∞) • b) =
        2⁻¹ * ∫ x, f x ∂a + 2⁻¹ * ∫ x, f x ∂b := by
    intro a b ha hb
    rw [integral_add_measure ((f.integrable a).smul_measure h2ne)
      ((f.integrable b).smul_measure h2ne), integral_smul_measure, integral_smul_measure]
    simp
  have e1 : (fun n => ∫ x, f x ∂((2⁻¹ : ℝ≥0∞) • μs n + (2⁻¹ : ℝ≥0∞) • νs n)) =
      fun n => 2⁻¹ * ∫ x, f x ∂μs n + 2⁻¹ * ∫ x, f x ∂νs n :=
    funext fun n => key _ _ (hμs n) (hνs n)
  rw [e1, key μ ν inferInstance inferInstance]
  exact ((h1 f).const_mul _).add ((h2 f).const_mul _)

/-- The optimal grid triples at level `n`. -/
private def zjE (S : SelectedSeq P) (n : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ m l j : ℕ, m ≤ S.N n ∧ l ≤ S.N n ∧ j ≤ m ∧ l + j ≤ S.N n ∧
    Grid.gobj P.U.u (S.V n) m l j = Grid.gH P.U.u (S.N n) (S.V n) m l ∧
    p = ((m : ℝ) * S.h n, (l : ℝ) * S.h n, (j : ℝ) * S.h n)}

/-- Step 3, argmax: a weak limit of the meeting measures is carried by optimal triples
(`lem:device` (b) and Step 1). -/
private lemma zj_argmax (S : SelectedSeq P) (h0 : S.jump = 0) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {Γ : Measure (ℝ × ℝ × ℝ)} (hΓ : IsProbabilityMeasure Γ)
    (hconv : WeakConv (fun n => S.Γn (φ n)) Γ) :
    ∀ᵐ p ∂Γ, obj P.U.u S.Vlim p.1 p.2.1 p.2.2 = bellH P.U.u S.Vlim p.1 p.2.1 := by
  have hV := zj_Vlim_value S h0
  obtain ⟨G, hG, -, hGeq⟩ := exists_continuous_bellH P.U hV
  have hE : ∀ k, S.Γn (φ k) (zjE S (φ k))ᶜ = 0 := by
    intro k
    have hae : ∀ᵐ p ∂S.Γn (φ k), _ := ae_gridMeeting (S.isApproxEq (φ k))
    refine mem_ae_iff.1 ?_
    filter_upwards [hae] with p hp
    obtain ⟨m, l, j, hm, hl, hj, -, -, -, hopt, hp⟩ := hp
    have hj' := (Grid.mem_feas hm hl).1 hj
    simp only [zjE, mem_ofPred_eq]
    exact ⟨m, l, j, hm, hl, hj'.1, hj'.2, hopt, hp⟩
  have hlim := hconv.measure_compl_limsup (fun n => zj_Γn_prob S (φ n)) hΓ hE
  have hae : ∀ᵐ p ∂Γ, p ∈ ⋂ k, closure (⋃ n ≥ k, zjE S (φ n)) := mem_ae_iff.2 hlim
  filter_upwards [hae] with p hp
  obtain ⟨nj, y, hnj, hyE, hy⟩ := device_b_points hp
  simp only [zjE, mem_ofPred_eq] at hyE
  choose mi li ji hmi hli hji hlj hopt hyeq using hyE
  have hψ : Tendsto (fun j => φ (nj j)) atTop atTop := hφ.tendsto_atTop.comp hnj
  -- coordinates
  have hy1 : Tendsto (fun j => (y j).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hy
  have hy2 : Tendsto (fun j => (y j).2.1) atTop (𝓝 p.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto p).comp hy
  have hy3 : Tendsto (fun j => (y j).2.2) atTop (𝓝 p.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto p).comp hy
  have hc1 : ∀ j, (y j).1 = mi j * S.h (φ (nj j)) := fun j => by rw [hyeq j]
  have hc2 : ∀ j, (y j).2.1 = li j * S.h (φ (nj j)) := fun j => by rw [hyeq j]
  have hc3 : ∀ j, (y j).2.2 = ji j * S.h (φ (nj j)) := fun j => by rw [hyeq j]
  have hnn1 : ∀ j, 0 ≤ (y j).1 := fun j => by
    rw [hc1]; exact mul_nonneg (Nat.cast_nonneg _) (S.h_pos _).le
  have hnn2 : ∀ j, 0 ≤ (y j).2.1 := fun j => by
    rw [hc2]; exact mul_nonneg (Nat.cast_nonneg _) (S.h_pos _).le
  have hnn3 : ∀ j, 0 ≤ (y j).2.2 := fun j => by
    rw [hc3]; exact mul_nonneg (Nat.cast_nonneg _) (S.h_pos _).le
  have hnn13 : ∀ j, 0 ≤ (y j).1 - (y j).2.2 := fun j => by
    rw [hc1, hc3, ← sub_mul]
    exact mul_nonneg (sub_nonneg.2 (by exact_mod_cast hji j)) (S.h_pos _).le
  have hp1 : 0 ≤ p.1 := ge_of_tendsto' hy1 hnn1
  have hp2 : 0 ≤ p.2.1 := ge_of_tendsto' hy2 hnn2
  have hp3 : 0 ≤ p.2.2 := ge_of_tendsto' hy3 hnn3
  -- (a) the grid objectives converge to the continuum objective
  have ho : Tendsto (fun j => Grid.gobj P.U.u (S.V (φ (nj j))) (mi j) (li j) (ji j)) atTop
      (𝓝 (obj P.U.u S.Vlim p.1 p.2.1 p.2.2)) := by
    have e : ∀ j, Grid.gobj P.U.u (S.V (φ (nj j))) (mi j) (li j) (ji j) =
        P.U.u (S.Vn (φ (nj j)) ((y j).2.1 + (y j).2.2) - S.Vn (φ (nj j)) (y j).2.1) +
          S.Vn (φ (nj j)) ((y j).1 - (y j).2.2) := by
      intro j
      unfold Grid.gobj
      rw [zj_V_eq S _ (hlj j), zj_V_eq S _ (hli j),
        zj_V_eq S _ (le_trans (Nat.sub_le _ _) (hmi j)), hc1, hc2, hc3, Nat.cast_add,
        Nat.cast_sub (hji j), add_mul, sub_mul]
    rw [funext e]
    have tA := zj_Vn_tendsto S h0 hψ (fun j => add_nonneg (hnn2 j) (hnn3 j)) (hy2.add hy3)
    have tB := zj_Vn_tendsto S h0 hψ hnn2 hy2
    have tC := zj_Vn_tendsto S h0 hψ hnn13 (hy1.sub hy3)
    have hgain : 0 ≤ S.Vlim (p.2.1 + p.2.2) - S.Vlim p.2.1 := hV.gain_nonneg hp2 hp3
    have tU : Tendsto (fun j => P.U.u (S.Vn (φ (nj j)) ((y j).2.1 + (y j).2.2) -
        S.Vn (φ (nj j)) (y j).2.1)) atTop
        (𝓝 (P.U.u (S.Vlim (p.2.1 + p.2.2) - S.Vlim p.2.1))) :=
      (P.U.continuousOn _ hgain).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tA.sub tB,
        Eventually.of_forall fun j => sub_nonneg.2 (zj_Vn_mono S _ (hnn2 j)
          (add_nonneg (hnn2 j) (hnn3 j)) (le_add_of_nonneg_right (hnn3 j)))⟩)
    exact tU.add tC
  -- (b) the grid maximized payoffs converge to the continuum one (Step 1)
  have hH : Tendsto (fun j => Grid.gH P.U.u (S.N (φ (nj j))) (S.V (φ (nj j))) (mi j) (li j))
      atTop (𝓝 (bellH P.U.u S.Vlim p.1 p.2.1)) := by
    have tG : Tendsto (fun j => G ((y j).1, (y j).2.1)) atTop (𝓝 (G (p.1, p.2.1))) :=
      (hG.tendsto _).comp (hy1.prodMk_nhds hy2)
    rw [hGeq _ _ hp1 hp2] at tG
    have tD : Tendsto (fun j => Grid.gH P.U.u (S.N (φ (nj j))) (S.V (φ (nj j))) (mi j) (li j) -
        G ((y j).1, (y j).2.1)) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hT1 := hy1.eventually (gt_mem_nhds (show p.1 < p.1 + p.2.1 + 1 by linarith))
      have hT2 := hy2.eventually (gt_mem_nhds (show p.2.1 < p.1 + p.2.1 + 1 by linarith))
      filter_upwards [hψ.eventually (zj_step1 S h0 (p.1 + p.2.1 + 1) hε), hT1, hT2]
        with j hj h1 h2
      rw [Real.dist_eq, sub_zero, hGeq _ _ (hnn1 j) (hnn2 j), hc1, hc2]
      exact hj (mi j) (li j) (hmi j) (hli j) (by rw [← hc1]; linarith)
        (by rw [← hc2]; linarith)
    simpa using tD.add tG
  rw [funext hopt] at ho
  exact tendsto_nhds_unique ho hH

/-! ### Noncondensation and positive monetary trade -/

/-- Noncondensation `η ≠ δ₀`: if the law were `δ₀`, full transfer against the atom would give
`V(x) ≥ β u(V(x))`, contradicting `β c₀ > 1` for small `V(x) > 0`. -/
private lemma zj_mean_pos (U : AdmissibleUtility) {β : ℝ} (hβ : 0 < β) (hβc : 1 < β * U.c0)
    {V : ℝ → ℝ} (hV : IsValueFn V) (hpos : ∀ t, 0 < t → 0 < V t) {η : Measure ℝ}
    [IsProbabilityMeasure η] (hη0 : η (Iio 0) = 0) (hint : Integrable id η)
    (hbell : ∀ m, 0 ≤ m → V m = bellT U.u β η V m) : 0 < ∫ x, x ∂η := by
  have hnn : ∀ᵐ x ∂η, 0 ≤ x := by
    rw [ae_iff]
    have e : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
    rw [e]; exact hη0
  refine lt_of_le_of_ne (integral_nonneg_of_ae hnn) (fun h => ?_)
  have hzero : ∀ᵐ x ∂η, x = 0 := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h.symm
  -- `V(m) ≥ β u(V(m))`
  have key : ∀ m, 0 ≤ m → β * U.u (V m) ≤ V m := by
    intro m hm
    have hc : ∫ s, bellH U.u V m s ∂η = bellH U.u V m 0 := by
      have e : (fun s => bellH U.u V m s) =ᵐ[η] fun _ => bellH U.u V m 0 :=
        hzero.mono fun s hs => by simp only [hs]
      rw [integral_congr_ae e]
      simp
    have hVm : V m = β * bellH U.u V m 0 := by
      have := hbell m hm
      rwa [bellT, hc] at this
    have h1 := obj_le_bellH U hV hm le_rfl ⟨hm, le_rfl⟩
    simp only [obj, gain, zero_add, hV.zero, sub_zero, sub_self, add_zero] at h1
    calc β * U.u (V m) ≤ β * bellH U.u V m 0 := mul_le_mul_of_nonneg_left h1 hβ.le
      _ = V m := hVm.symm
  -- small positive values of `V`
  have hlim : Tendsto V (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => hpos t ht⟩
    have := (hV.continuousOn 0 self_mem_Ici).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    rw [ContinuousWithinAt, hV.zero] at this
    exact this
  have hc : 1 / β < U.c0 := by rw [div_lt_iff₀ hβ]; linarith
  have hev := (U.tendsto_div_zero.comp hlim).eventually (lt_mem_nhds hc)
  obtain ⟨t, ht1, ht2⟩ := (hev.and self_mem_nhdsWithin).exists
  have hVt := hpos t ht2
  have h2 := key t (le_of_lt ht2)
  simp only [Function.comp] at ht1
  rw [div_lt_div_iff₀ hβ hVt] at ht1
  nlinarith

/-- Positive monetary trade: otherwise `H_V(b,s) = V(b)` on the support, hence `V = β V`
`η`-a.e., so `V` vanishes `η`-a.e., which forces `η = δ₀`. -/
private lemma zj_monetary (U : AdmissibleUtility) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {V : ℝ → ℝ} (hV : IsValueFn V) (hpos : ∀ t, 0 < t → 0 < V t) {η : Measure ℝ}
    [IsProbabilityMeasure η] (hη0 : η (Iio 0) = 0) (hmean : 0 < ∫ x, x ∂η)
    (hbell : ∀ m, 0 ≤ m → V m = bellT U.u β η V m) {Γ : Measure (ℝ × ℝ × ℝ)}
    (hQ : Γ zjQᶜ = 0) (hmarg : Γ.map pairBS = η.prod η)
    (hargmax : ∀ᵐ p ∂Γ, obj U.u V p.1 p.2.1 p.2.2 = bellH U.u V p.1 p.2.1) :
    Γ {p | 0 < p.2.2 ∧ 0 < gain V p.2.1 p.2.2} ≠ 0 := by
  intro h0
  obtain ⟨G, hG, hGb, hGeq⟩ := exists_continuous_bellH U hV
  set E : Set (ℝ × ℝ) := {q | G q ≤ posPart V q.1} with hEdef
  have hEc : IsClosed E := isClosed_le hG ((continuous_posPart hV.continuousOn).comp continuous_fst)
  have hnn : ∀ᵐ x ∂η, 0 ≤ x := by
    rw [ae_iff]
    have e : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
    rw [e]; exact hη0
  have hQae : ∀ᵐ p ∂Γ, p ∈ zjQ := mem_ae_iff.2 hQ
  have hno : ∀ᵐ p ∂Γ, ¬ (0 < p.2.2 ∧ 0 < gain V p.2.1 p.2.2) := by
    rw [ae_iff]; simpa using h0
  -- `H_V(b,s) = V(b)` `Γ`-a.e.
  have hΓE : ∀ᵐ p ∂Γ, pairBS p ∈ E := by
    filter_upwards [hQae, hno, hargmax] with p hp hno hopt
    obtain ⟨hb, hs, hd0, hdb⟩ := hp
    show G (p.1, p.2.1) ≤ posPart V p.1
    rw [hGeq _ _ hb hs, posPart_eq hb, ← hopt]
    unfold obj
    rcases hd0.eq_or_lt with hd | hd
    · rw [← hd]; simp [gain, U.u_zero]
    · have hg : gain V p.2.1 p.2.2 ≤ 0 := not_lt.1 (fun hg => hno ⟨hd, hg⟩)
      rw [le_antisymm hg (hV.gain_nonneg hs hd0), U.u_zero, zero_add]
      exact hV.le_of_le (by linarith) (by linarith)
  have hprodE : ∀ᵐ q ∂(η.prod η), q ∈ E := by
    rw [← hmarg]
    exact (ae_map_iff (by unfold pairBS; fun_prop) hEc.measurableSet).2 hΓE
  have hb : ∀ᵐ b ∂η, ∀ᵐ s ∂η, (b, s) ∈ E := Measure.ae_ae_of_ae_prod hprodE
  -- `V(b) = 0`, hence `b = 0`, `η`-a.e.
  have hV0 : ∀ᵐ b ∂η, b = 0 := by
    filter_upwards [hb, hnn] with b hbE hb0
    have hle : ∫ s, bellH U.u V b s ∂η ≤ V b := by
      have e : ∫ s, bellH U.u V b s ∂η = ∫ s, G (b, s) ∂η :=
        integral_congr_ae (hnn.mono fun s hs => (hGeq b s hb0 hs).symm)
      rw [e]
      have hGi : Integrable (fun s => G (b, s)) η :=
        Integrable.of_bound
          (hG.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
          (U.ubar + hV.sup) (Eventually.of_forall fun s => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hGb _).1]; exact (hGb _).2)
      calc ∫ s, G (b, s) ∂η ≤ ∫ _s, posPart V b ∂η :=
            integral_mono_ae hGi (integrable_const _) hbE
        _ = V b := by simp [posPart_eq hb0]
    have hbell' := hbell b hb0
    rw [bellT] at hbell'
    by_contra hne
    have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hne)
    have := hpos b hbpos
    have := mul_le_mul_of_nonneg_left hle hβ0.le
    nlinarith
  have : ∫ x, x ∂η = 0 := by
    rw [integral_congr_ae hV0]; simp
  linarith

/-- `thm:zerojump`: if the chosen Helly limit satisfies `V(0+) = 0` (and `V ≢ 0`, by
`thm:halflevel`), then the limit value function and law, together with a weak limit `Γ` of the
meeting measures, form a stationary monetary equilibrium in relaxed strategies of mean
`∫ x dη ∈ (0, M]`. The money rescaling of `rem:norm` (`IsEquilibrium.rescale`) then restores
mean `M`. -/
theorem zerojump (S : SelectedSeq P) (h0 : S.jump = 0) (hnz : ∃ x > 0, S.Vlim x ≠ 0) :
    ∃ Γ, IsEquilibrium P.U.u P.β (∫ x, x ∂S.ηlim) S.Vlim S.ηlim Γ := by
  have hV := zj_Vlim_value S h0
  have hpos := zj_Vlim_pos S hnz
  have hηprob := S.ηlim_prob
  have hη0 := S.limit_props.2.2.2.1
  have hint := S.limit_props.2.2.2.2.1
  have hbell : ∀ m, 0 ≤ m → S.Vlim m = bellT P.U.u P.β S.ηlim S.Vlim m :=
    fun m hm => zj_step2 S h0 hm
  -- Step 3: a weak limit of the meeting measures (Prokhorov)
  obtain ⟨φ, hφ, Γ, hΓ, hconv⟩ := exists_subseq_weakConv (zj_Γn_prob S) (zj_Γn_tight S)
  have := hΓ
  have hηφ : WeakConv (fun n => S.ηn (φ n)) S.ηlim := S.η_conv.comp hφ
  have hQ : Γ zjQᶜ = 0 := by
    have h1 : (1 : ℝ≥0∞) ≤ Γ zjQ :=
      hconv.le_measure_closed (fun n => zj_Γn_prob S (φ n)) hΓ zjQ_closed
        (Eventually.of_forall fun n => by
          have := zj_Γn_prob S (φ n)
          rw [(prob_compl_eq_zero_iff zjQ_closed.measurableSet).1 (zj_Γn_Q S (φ n))])
    exact (prob_compl_eq_zero_iff zjQ_closed.measurableSet).2 (le_antisymm prob_le_one h1)
  have hmeet : Γ meetingSetᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 fun p hp => ⟨hp.2.2.1, hp.2.2.2⟩) hQ
  -- the marginal
  have hmarg : Γ.map pairBS = S.ηlim.prod S.ηlim := by
    have mP : Continuous pairBS := by unfold pairBS; fun_prop
    have h1 := hconv.map (fun n => zj_Γn_prob S (φ n)) hΓ mP
    have e : ∀ n, (S.Γn (φ n)).map pairBS = (S.ηn (φ n)).prod (S.ηn (φ n)) := fun n =>
      gridMeeting_marginal (S.h_pos _) (S.isApproxEq _)
    simp only [e] at h1
    have h2 := hηφ.prod (fun n => zj_ηn_prob S (φ n)) hηprob (fun n => zj_ηn_prob S (φ n))
      hηprob hηφ
    exact WeakConv.unique (fun n => by have := zj_ηn_prob S (φ n); infer_instance)
      inferInstance inferInstance h1 h2
  -- stationarity
  have hstat : S.ηlim = (2⁻¹ : ℝ≥0∞) • Γ.map postB + (2⁻¹ : ℝ≥0∞) • Γ.map postS := by
    have mB : Continuous postB := by unfold postB; fun_prop
    have mS : Continuous postS := by unfold postS; fun_prop
    have hB := hconv.map (fun n => zj_Γn_prob S (φ n)) hΓ mB
    have hS := hconv.map (fun n => zj_Γn_prob S (φ n)) hΓ mS
    have hmix := zj_weakConv_half
      (fun n => by have := zj_Γn_prob S (φ n); infer_instance)
      (fun n => by have := zj_Γn_prob S (φ n); infer_instance) hB hS
    have e : ∀ n, (2⁻¹ : ℝ≥0∞) • (S.Γn (φ n)).map postB + (2⁻¹ : ℝ≥0∞) • (S.Γn (φ n)).map postS
        = S.ηn (φ n) := fun n => (gridMeeting_stationary (S.h_pos _) (S.isApproxEq _)).symm
    simp only [e] at hmix
    have hprob : IsProbabilityMeasure
        ((2⁻¹ : ℝ≥0∞) • Γ.map postB + (2⁻¹ : ℝ≥0∞) • Γ.map postS) :=
      ⟨by simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
        ENNReal.inv_two_add_inv_two]⟩
    exact WeakConv.unique (fun n => zj_ηn_prob S (φ n)) hηprob hprob hηφ hmix
  have hargmax := zj_argmax S h0 hφ hΓ hconv
  have hmean := zj_mean_pos P.U P.β_pos P.active hV hpos hη0 hint hbell
  exact ⟨Γ,
    { value := hV
      isProb_η := hηprob
      η_nonneg := hη0
      isProb_Γ := hΓ
      Γ_meeting := hmeet
      bellman := hbell
      marginal := hmarg
      argmax := hargmax
      stationary := hstat
      integrable_id := hint
      mean := rfl
      mean_pos := hmean
      monetary := fun h0 => zj_monetary P.U P.β_pos P.β_lt_one hV hpos hη0 hmean hbell hQ hmarg
        hargmax (measure_mono_null (fun p hp => hp.2) h0) }⟩

end Molico
