import MonetaryExistenceBuyer.Limit.Props

/-!
# Half-level compactness (`thm:halflevel`)

Proof structure (following the paper):
* Step 1: if `V ≡ 0` on `(0,∞)`, rescale `V_n` at the point `r_n` where it reaches the fixed
  level `ℓ₀` (intermediate value theorem; `r_n → ∞`) and extract a Helly limit `W` of
  `W_n(y) = V_n(r_n y)` with `W(1) = ℓ₀`.
* Step 2 (`wsplit`): `W(a + b) ≥ β (u(W(a)) + W(b))` for `a, b > 0`, `a + b ≤ 1`
  (`eq:Wsplit`, with `y = a + b`, `z = a`), from the grid Bellman equation and Markov.
* Step 3 (`step3`): both cases for the jump `J = W(0+)` are contradictory.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

/-- The interpolants are monotone, concave on `[0,∞)`, with values in `[0, L_*]`. -/
private lemma Vn_basic (S : SelectedSeq P) (n : ℕ) :
    Monotone (S.Vn n) ∧ ConcaveOn ℝ (Ici 0) (S.Vn n) ∧
      (∀ x, 0 ≤ S.Vn n x ∧ S.Vn n x ≤ P.Lstar) := by
  refine ⟨interp_monotone (S.h_pos n) (S.isApproxEq n).cone.incr,
    interp_concaveOn (S.h_pos n) (S.isApproxEq n).cone.incr, fun x => ?_⟩
  have h1 := interp_mem_Icc (S.h_pos n) (S.isApproxEq n).cone.incr (V := S.V n) (N := S.N n) x
  rw [(S.isApproxEq n).cone.zero] at h1
  exact ⟨h1.1, h1.2.trans (S.floor n).2⟩

/-- The rescalings `y ↦ V_n(r_n y)` are monotone, concave, with values in `[0, L_*]`. -/
private lemma resc_facts (S : SelectedSeq P) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) :
    (∀ n, MonotoneOn (fun y => S.Vn n (r n * y)) (Ici 0)) ∧
    (∀ n, ConcaveOn ℝ (Ici 0) (fun y => S.Vn n (r n * y))) ∧
    (∀ n y, 0 ≤ y → 0 ≤ S.Vn n (r n * y) ∧ S.Vn n (r n * y) ≤ P.Lstar) := by
  refine ⟨fun n x _ y _ hxy => (Vn_basic S n).1 (mul_le_mul_of_nonneg_left hxy (hr n).le),
    fun n => ⟨convex_Ici 0, fun x hx y hy s t hs ht hst => ?_⟩,
    fun n y _ => (Vn_basic S n).2.2 _⟩
  have hx' : r n * x ∈ Ici (0:ℝ) := mul_nonneg (hr n).le hx
  have hy' : r n * y ∈ Ici (0:ℝ) := mul_nonneg (hr n).le hy
  have := (Vn_basic S n).2.1.2 hx' hy' hs ht hst
  simp only [smul_eq_mul] at this ⊢
  convert this using 2
  ring

/-- Floored grid points: `⌊c r_n / h_n⌋ h_n / r_n → c` when `r_n → ∞`. -/
private lemma tendsto_floor_div (S : SelectedSeq P) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hrinf : Tendsto r atTop atTop) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n => (⌊c * r n / S.h n⌋₊ : ℝ) * S.h n / r n) atTop (𝓝 c) := by
  have hhr : Tendsto (fun n => S.h n / r n) atTop (𝓝 0) := by
    have := S.h_tendsto.mul (tendsto_inv_atTop_zero.comp hrinf)
    simpa [div_eq_mul_inv] using this
  have hlow : Tendsto (fun n => c - S.h n / r n) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).sub hhr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · have hh := S.h_pos n
    have hrn := hr n
    have h1 := Nat.lt_floor_add_one (c * r n / S.h n)
    rw [div_lt_iff₀ hh] at h1
    have e : c - S.h n / r n = (c * r n - S.h n) / r n := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hrn.le
    linarith
  · have hh := S.h_pos n
    have h1 := Nat.floor_le (div_nonneg (mul_nonneg hc (hr n).le) hh.le)
    rw [div_le_iff₀ (hr n)]
    calc (⌊c * r n / S.h n⌋₊ : ℝ) * S.h n ≤ c * r n / S.h n * S.h n :=
          mul_le_mul_of_nonneg_right h1 hh.le
      _ = c * r n := div_mul_cancel₀ _ hh.ne'

/-- Convergence at grid indices `k_n` with `k_n h_n / r_n → c > 0`. -/
private lemma tendsto_V_idx (S : SelectedSeq P) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) {W : ℝ → ℝ}
    (hW : TendstoLocallyUniformlyOn (fun n y => S.Vn n (r n * y)) W atTop (Ioi 0))
    {k : ℕ → ℕ} (hk : ∀ n, k n ≤ S.N n) {c : ℝ} (hc : 0 < c)
    (hkc : Tendsto (fun n => (k n : ℝ) * S.h n / r n) atTop (𝓝 c)) :
    Tendsto (fun n => S.V n (k n)) atTop (𝓝 (W c)) := by
  obtain ⟨hm, hcv, hb⟩ := resc_facts S hr
  have := tendsto_comp_of_concave hm hcv hb hW hc hkc
  refine this.congr (fun n => ?_)
  rw [show r n * ((k n : ℝ) * S.h n / r n) = (k n : ℝ) * S.h n by
    field_simp [(hr n).ne']]
  exact interp_natCast (S.h_pos n) (hk n)

/-- The Bellman estimate at a fixed approximant: a buyer at grid index `i` transferring `j` to
every seller of wealth at most `K` (Markov: `η_n([0,K]) ≥ 1 - M/K`). -/
private lemma bellman_bound (S : SelectedSeq P) (n : ℕ) {i j : ℕ} (hiN : i ≤ S.N n)
    (hji : j ≤ i) {K : ℝ} (hK0 : 0 < K)
    (hfeas : ∀ l : ℕ, (l : ℝ) * S.h n ≤ K → l + j ≤ S.N n) :
    P.β * (P.U.u (max (S.V n j - S.Vn n K) 0) + S.V n (i - j)) * (1 - P.M / K) ≤ S.V n i := by
  have hE := S.isApproxEq n
  set q := P.U.u (max (S.V n j - S.Vn n K) 0) + S.V n (i - j) with hq
  have hq0 : 0 ≤ q :=
    add_nonneg (P.U.nonneg (le_max_right _ _)) (hE.cone.incr.nonneg hE.cone.zero (by omega))
  rw [hE.bellman i hiN, Grid.gT, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ P.β_pos.le
  have hsum : q * (1 - P.M / K) =
      ∑ l ∈ Finset.range (S.N n + 1), S.η n l * (q * (1 - l * S.h n / K)) := by
    have e : ∀ l, S.η n l * (q * (1 - l * S.h n / K)) =
        q * S.η n l - q / K * (S.η n l * (l * S.h n)) := by
      intro l; field_simp
    rw [Finset.sum_congr rfl (fun l _ => e l), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hE.law.sum_one, hE.law.mean]
    field_simp
  rw [hsum]
  refine Finset.sum_le_sum (fun l hl => ?_)
  have hl' : l ≤ S.N n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  refine mul_le_mul_of_nonneg_left ?_ (hE.law.nonneg l)
  have hlh : 0 ≤ (l : ℝ) * S.h n / K :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.h_pos n).le) hK0.le
  by_cases hlK : (l : ℝ) * S.h n ≤ K
  · have hlj := hfeas l hlK
    have hjfeas : j ∈ Grid.feas (S.N n) i l := (Grid.mem_feas hiN hl').2 ⟨hji, hlj⟩
    have h1 := Grid.gobj_le_gH P.U hiN hl' hjfeas (V := S.V n)
    have h2 : max (S.V n j - S.Vn n K) 0 ≤ S.V n (l + j) - S.V n l := by
      have hjl : S.V n j ≤ S.V n (l + j) := hE.cone.incr.le_of_le (by omega) hlj
      have hll : S.V n l ≤ S.V n (l + j) := hE.cone.incr.le_of_le (by omega) hlj
      have hlK' : S.V n l ≤ S.Vn n K := by
        have := (Vn_basic S n).1 hlK
        rwa [show S.Vn n (l * S.h n) = S.V n l from interp_natCast (S.h_pos n) hl'] at this
      exact max_le (by linarith) (by linarith)
    have h3 : P.U.u (max (S.V n j - S.Vn n K) 0) ≤ P.U.u (S.V n (l + j) - S.V n l) :=
      P.U.monotoneOn (mem_Ici.2 (le_max_right _ _)) (mem_Ici.2 ((le_max_right _ _).trans h2)) h2
    have h4 : q * (1 - l * S.h n / K) ≤ q := by nlinarith
    calc q * (1 - l * S.h n / K) ≤ q := h4
      _ ≤ Grid.gobj P.U.u (S.V n) i l j := by simp only [Grid.gobj, hq]; linarith
      _ ≤ _ := h1
  · have h1 : 1 - (l : ℝ) * S.h n / K < 0 := by
      rw [sub_neg, one_lt_div hK0]; exact not_le.1 hlK
    have h2 := Grid.gH_nonneg P.U hE.cone.incr hE.cone.zero hiN hl' (V := S.V n)
    nlinarith

/-- `eq:Wsplit` (Step 2 of `thm:halflevel`), with `y = a + b`, `z = a`. -/
private lemma wsplit (S : SelectedSeq P) (r : ℕ → ℝ) (W : ℝ → ℝ)
    (hVK : ∀ K > 0, Tendsto (fun n => S.Vn n K) atTop (𝓝 0))
    (hr0 : ∀ n, 0 < r n) (hrR : ∀ n, r n ≤ S.N n * S.h n)
    (hrinf : Tendsto r atTop atTop)
    (hW : TendstoLocallyUniformlyOn (fun n y => S.Vn n (r n * y)) W atTop (Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) :
    P.β * (P.U.u (W a) + W b) ≤ W (a + b) := by
  obtain ⟨hm, hcv, hbd⟩ := resc_facts S hr0
  obtain ⟨-, -, -, Wbd, -⟩ := concave_limit_props hm hcv hbd hW
  obtain ⟨i, hi⟩ : ∃ i : ℕ → ℕ, ∀ n, i n = ⌊(a + b) * r n / S.h n⌋₊ := ⟨_, fun _ => rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ → ℕ, ∀ n, j n = ⌊a * r n / S.h n⌋₊ := ⟨_, fun _ => rfl⟩
  have hiN : ∀ n, i n ≤ S.N n := by
    intro n
    rw [hi]
    apply Nat.floor_le_of_le
    rw [div_le_iff₀ (S.h_pos n)]
    calc (a + b) * r n ≤ 1 * r n := mul_le_mul_of_nonneg_right hab (hr0 n).le
      _ ≤ S.N n * S.h n := by rw [one_mul]; exact hrR n
  have hji : ∀ n, j n ≤ i n := by
    intro n
    rw [hi, hj]
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ (S.h_pos n).le
    exact mul_le_mul_of_nonneg_right (by linarith) (hr0 n).le
  have hiT : Tendsto (fun n => (i n : ℝ) * S.h n / r n) atTop (𝓝 (a + b)) := by
    simp only [hi]; exact tendsto_floor_div S hr0 hrinf (by linarith)
  have hjT : Tendsto (fun n => (j n : ℝ) * S.h n / r n) atTop (𝓝 a) := by
    simp only [hj]; exact tendsto_floor_div S hr0 hrinf ha.le
  have hVi : Tendsto (fun n => S.V n (i n)) atTop (𝓝 (W (a + b))) :=
    tendsto_V_idx S hr0 hW hiN (by linarith) hiT
  have hVj : Tendsto (fun n => S.V n (j n)) atTop (𝓝 (W a)) :=
    tendsto_V_idx S hr0 hW (fun n => (hji n).trans (hiN n)) ha hjT
  have hVij : Tendsto (fun n => S.V n (i n - j n)) atTop (𝓝 (W b)) := by
    refine tendsto_V_idx S hr0 hW (fun n => (Nat.sub_le _ _).trans (hiN n)) hb ?_
    have := hiT.sub hjT
    rw [show a + b - a = b by ring] at this
    refine this.congr (fun n => ?_)
    rw [Nat.cast_sub (hji n)]; ring
  -- the estimate for a fixed Markov cutoff `K > M`
  have key : ∀ K, P.M < K → P.β * (P.U.u (W a) + W b) * (1 - P.M / K) ≤ W (a + b) := by
    intro K hK
    have hK0 : 0 < K := P.M_pos.trans hK
    have hqT : Tendsto (fun n => P.β * (P.U.u (max (S.V n (j n) - S.Vn n K) 0) +
        S.V n (i n - j n)) * (1 - P.M / K)) atTop
        (𝓝 (P.β * (P.U.u (W a) + W b) * (1 - P.M / K))) := by
      have h1 : Tendsto (fun n => max (S.V n (j n) - S.Vn n K) 0) atTop (𝓝 (W a)) := by
        have := (hVj.sub (hVK K hK0)).max (tendsto_const_nhds (x := (0:ℝ)))
        rwa [sub_zero, max_eq_left (Wbd a ha).1] at this
      have h2 : Tendsto (fun n => P.U.u (max (S.V n (j n) - S.Vn n K) 0)) atTop
          (𝓝 (P.U.u (W a))) :=
        (P.U.continuousOn.continuousWithinAt (show W a ∈ Ici 0 from (Wbd a ha).1)).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨h1, Eventually.of_forall fun n => mem_Ici.2 (le_max_right _ _)⟩)
      exact ((h2.add hVij).const_mul P.β).mul_const _
    have h1a : 0 < 1 - a := by linarith
    have hev : ∀ᶠ n in atTop, P.β * (P.U.u (max (S.V n (j n) - S.Vn n K) 0) +
        S.V n (i n - j n)) * (1 - P.M / K) ≤ S.V n (i n) := by
      filter_upwards [hrinf.eventually_ge_atTop (K / (1 - a))] with n hn
      have hKr : K ≤ (1 - a) * r n := by rwa [div_le_iff₀ h1a, mul_comm] at hn
      refine bellman_bound S n (hiN n) (hji n) hK0 (fun l hl => ?_)
      have hjr : (j n : ℝ) * S.h n ≤ a * r n := by
        have := Nat.floor_le (div_nonneg (mul_nonneg ha.le (hr0 n).le) (S.h_pos n).le)
        rw [← hj] at this
        calc (j n : ℝ) * S.h n ≤ a * r n / S.h n * S.h n :=
              mul_le_mul_of_nonneg_right this (S.h_pos n).le
          _ = a * r n := div_mul_cancel₀ _ (S.h_pos n).ne'
      have h5 : ((l + j n : ℕ) : ℝ) * S.h n ≤ S.N n * S.h n := by
        push_cast
        linarith [hrR n]
      have h6 := le_of_mul_le_mul_right h5 (S.h_pos n)
      exact_mod_cast h6
    exact le_of_tendsto_of_tendsto hqT hVi hev
  -- let the cutoff `K → ∞`
  have hlim : Tendsto (fun K => P.β * (P.U.u (W a) + W b) * (1 - P.M / K)) atTop
      (𝓝 (P.β * (P.U.u (W a) + W b) * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id))
  rw [sub_zero, mul_one] at hlim
  exact le_of_tendsto hlim ((eventually_gt_atTop P.M).mono key)

/-- Step 3 of `thm:halflevel`: a rescaled limit satisfying `eq:Wsplit` with `0 < W ≤ W(1) < L_*`
on `(0,1]` cannot exist (both cases for the jump `J = W(0+)` are contradictory). -/
private lemma step3 (W : ℝ → ℝ) (hmono : MonotoneOn W (Ioi 0)) (hcont : ContinuousOn W (Ioi 0))
    (hpos : ∀ x, 0 < x → x ≤ 1 → 0 < W x) (hW1 : W 1 < P.Lstar)
    (hsplit : ∀ a b, 0 < a → 0 < b → a + b ≤ 1 → P.β * (P.U.u (W a) + W b) ≤ W (a + b)) :
    False := by
  have hlimR : ∀ x, 0 < x → Tendsto (fun t => W (x + t)) (𝓝[>] 0) (𝓝 (W x)) := by
    intro x hx
    have hc : Tendsto W (𝓝 x) (𝓝 (W x)) := (hcont.continuousAt (Ioi_mem_nhds hx)).tendsto
    have ht : Tendsto (fun t : ℝ => x + t) (𝓝[>] 0) (𝓝 x) := by
      have : Tendsto (fun t : ℝ => x + t) (𝓝 0) (𝓝 (x + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hc.comp ht
  set J := sInf (W '' Ioo 0 1) with hJ
  have hne : (W '' Ioo 0 1).Nonempty := ⟨W (1/2), 1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hbdd : BddBelow (W '' Ioo 0 1) :=
    ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact (hpos x hx.1 hx.2.le).le⟩
  have hJW : ∀ x ∈ Ioo (0:ℝ) 1, J ≤ W x := fun x hx => csInf_le hbdd ⟨x, hx, rfl⟩
  have hJ0 : 0 ≤ J := le_csInf hne (by rintro _ ⟨x, hx, rfl⟩; exact (hpos x hx.1 hx.2.le).le)
  have hJL : J < P.Lstar := by
    have h1 := hJW (1/2) ⟨by norm_num, by norm_num⟩
    have h2 := hmono (show (1/2:ℝ) ∈ Ioi 0 by norm_num) (show (1:ℝ) ∈ Ioi 0 by norm_num)
      (by norm_num)
    linarith
  have hβ := P.β_pos
  have hβ1 := P.β_lt_one
  rcases hJ0.lt_or_eq with hJpos | hJzero
  · -- `J > 0`: `σ W(x) ≥ u(J)`, hence `σ J ≥ u(J)`, forcing `J ≥ L_*`
    have hb : ∀ x ∈ Ioo (0:ℝ) 1, P.β * (P.U.u J + W x) ≤ W x := by
      intro x hx
      refine ge_of_tendsto (hlimR x hx.1) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 - x by linarith [hx.2])] with t ht
      have h1 := hsplit t x ht.1 hx.1 (by linarith [ht.2])
      rw [add_comm t x] at h1
      have htJ : J ≤ W t := hJW t ⟨ht.1, by linarith [ht.2, hx.1]⟩
      have h2 : P.U.u J ≤ P.U.u (W t) := P.U.monotoneOn hJ0 (hJ0.trans htJ) htJ
      have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
      linarith
    have hc : P.β * P.U.u J / (1 - P.β) ≤ J := by
      refine le_csInf hne ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [div_le_iff₀ (by linarith)]
      linarith [hb x hx]
    have h1 : P.β * P.U.u J ≤ J * (1 - P.β) := by rwa [div_le_iff₀ (by linarith)] at hc
    have h2 := (P.div_gt_σ_iff hJpos).2 hJL
    rw [lt_div_iff₀ hJpos] at h2
    have hσ : P.β * P.σ = 1 - P.β := by simp only [Primitives.σ]; field_simp
    have h3 := mul_lt_mul_of_pos_left h2 hβ
    have h4 : P.β * (P.σ * J) = J * (1 - P.β) := by rw [← mul_assoc, hσ]; ring
    linarith
  · -- `J = 0`: `W(x) ≥ β u(W(x))` with `W(x) ↓ 0`, against `β c₀ > 1`
    have ha : ∀ x ∈ Ioo (0:ℝ) 1, P.β * P.U.u (W x) ≤ W x := by
      intro x hx
      refine ge_of_tendsto (hlimR x hx.1) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 - x by linarith [hx.2])] with t ht
      have h1 := hsplit x t hx.1 ht.1 (by linarith [ht.2])
      have h2 := mul_pos hβ (hpos t ht.1 (by linarith [ht.2, hx.1]))
      linarith
    have hc0 : 1 / P.β < P.U.c0 := by rw [div_lt_iff₀ hβ]; linarith [P.active]
    obtain ⟨t0, ht0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (P.U.tendsto_div_zero.eventually (lt_mem_nhds hc0))
    have hJt : J < t0 := by rw [← hJzero]; exact ht0
    obtain ⟨_, ⟨x, hx, rfl⟩, hxt⟩ := exists_lt_of_csInf_lt hne hJt
    have hWx := hpos x hx.1 hx.2.le
    have h1 : 1 / P.β < P.U.u (W x) / W x := hsub ⟨hWx, hxt⟩
    rw [lt_div_iff₀ hWx, div_mul_eq_mul_div, one_mul, div_lt_iff₀ hβ] at h1
    linarith [ha x hx]

/-- `thm:halflevel` (half-level compactness): `V ≢ 0` on `(0, ∞)`. -/
theorem halflevel (S : SelectedSeq P) : ∃ x > 0, S.Vlim x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hℓ0, hℓL, -⟩ := P.uniformfloor
  -- Step 1: `V_n(K) → 0` for every fixed `K > 0`
  have hVK : ∀ K > 0, Tendsto (fun n => S.Vn n K) atTop (𝓝 0) := by
    intro K hK
    have := S.V_conv.tendsto_at (show K ∈ Ioi 0 from hK)
    rw [hcon K hK] at this
    exact this
  -- the point `r_n` where `V_n` reaches the level `ℓ₀`
  have hex : ∀ n, ∃ r, 0 < r ∧ r ≤ S.N n * S.h n ∧ S.Vn n r = P.ℓ0 := by
    intro n
    have hE := S.isApproxEq n
    have hR0 : (0:ℝ) ≤ S.N n * S.h n := mul_nonneg (Nat.cast_nonneg _) (S.h_pos n).le
    have hf0 : S.Vn n 0 = 0 := by
      show interp _ _ _ 0 = 0
      rw [interp_of_nonpos (S.h_pos n) le_rfl, hE.cone.zero]
    have hfR : S.Vn n (S.N n * S.h n) = S.V n (S.N n) := interp_of_le (S.h_pos n) le_rfl
    have hc : Continuous (S.Vn n) := continuous_interp (S.h_pos n)
    obtain ⟨r, hr, hrv⟩ := intermediate_value_Icc hR0 hc.continuousOn
      (show P.ℓ0 ∈ Icc (S.Vn n 0) (S.Vn n (S.N n * S.h n)) by
        rw [hf0, hfR]; exact ⟨hℓ0.le, (S.floor n).1⟩)
    refine ⟨r, ?_, hr.2, hrv⟩
    rcases hr.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hf0] at hrv; exact absurd hrv.symm hℓ0.ne'
  choose r hr0 hrR hrV using hex
  -- `r_n → ∞`
  have hrinf : Tendsto r atTop atTop := by
    refine tendsto_atTop.2 fun K => ?_
    have hK1 : (0:ℝ) < max K 1 := lt_max_of_lt_right one_pos
    filter_upwards [(hVK _ hK1).eventually (Iio_mem_nhds hℓ0)] with n hn
    refine le_trans (le_max_left K 1) ?_
    by_contra hlt
    push Not at hlt
    have := (Vn_basic S n).1 hlt.le
    rw [hrV n] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)
  -- Helly limit of the rescalings
  obtain ⟨hm, hcv, hbd⟩ := resc_facts S hr0
  obtain ⟨φ, hφ, W, hW⟩ := helly_concave (f := fun n y => S.Vn n (r n * y)) hm hcv hbd
  obtain ⟨Wmono, -, Wcont, -, Wscale⟩ :=
    concave_limit_props (fun n => hm (φ n)) (fun n => hcv (φ n)) (fun n => hbd (φ n)) hW
  have hW1 : W 1 = P.ℓ0 := by
    have := hW.tendsto_at (mem_Ioi.2 (one_pos : (0:ℝ) < 1))
    refine tendsto_nhds_unique this ?_
    simp only [mul_one, hrV]
    exact tendsto_const_nhds
  have hpos : ∀ x, 0 < x → x ≤ 1 → 0 < W x := by
    intro x hx hx1
    have := Wscale 1 one_pos x hx hx1
    rw [mul_one, hW1] at this
    exact lt_of_lt_of_le (mul_pos hx hℓ0) this
  -- Step 2
  have hsplit : ∀ a b, 0 < a → 0 < b → a + b ≤ 1 → P.β * (P.U.u (W a) + W b) ≤ W (a + b) :=
    fun a b ha hb hab => wsplit (S.comp φ hφ) (r ∘ φ) W
      (fun K hK => (hVK K hK).comp hφ.tendsto_atTop) (fun n => hr0 (φ n))
      (fun n => hrR (φ n)) (hrinf.comp hφ.tendsto_atTop) hW ha hb hab
  -- Step 3
  exact step3 W Wmono Wcont hpos (hW1 ▸ hℓL) hsplit

end Molico
