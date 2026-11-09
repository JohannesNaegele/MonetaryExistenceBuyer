import MonetaryExistenceBuyer.Rescaling.Exists

/-!
# Properties of normalized limits (`lem:normalizedlimits`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### The interpolants `V_n` and the normalized profiles `W_n` -/

private lemma scale_nonneg (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.scale a n :=
  mul_nonneg (S.h_pos n).le (Nat.cast_nonneg _)

private lemma Vn_zero (S : SelectedSeq P) (n : ℕ) : S.Vn n 0 = 0 := by
  unfold SelectedSeq.Vn
  rw [interp_of_nonpos (S.h_pos n) le_rfl, (S.isApproxEq n).cone.zero]

private lemma Vn_mono (S : SelectedSeq P) (n : ℕ) : Monotone (S.Vn n) :=
  interp_monotone (S.h_pos n) (S.isApproxEq n).cone.incr

private lemma Vn_bd (S : SelectedSeq P) (n : ℕ) (x : ℝ) : 0 ≤ S.Vn n x ∧ S.Vn n x ≤ P.Lstar := by
  have h1 := interp_mem_Icc (S.h_pos n) (S.isApproxEq n).cone.incr x
  rw [(S.isApproxEq n).cone.zero] at h1
  exact ⟨h1.1, h1.2.trans (S.floor n).2⟩

/-- `W_n = V_n(e_n ·)` is nondecreasing and concave on `[0, ∞)` with values in `[0, L_*]`
(also for the finitely many `n` with `e_n = 0`, where `W_n ≡ 0`). -/
private lemma Wn_facts (S : SelectedSeq P) (a : ℝ) :
    (∀ n, MonotoneOn (S.Wn a n) (Ici 0)) ∧ (∀ n, ConcaveOn ℝ (Ici 0) (S.Wn a n)) ∧
      (∀ n x, 0 ≤ x → 0 ≤ S.Wn a n x ∧ S.Wn a n x ≤ P.Lstar) := by
  refine ⟨fun n x _ y _ hxy => Vn_mono S n (mul_le_mul_of_nonneg_left hxy (scale_nonneg S a n)),
    fun n => ⟨convex_Ici 0, fun x hx y hy α β hα hβ hαβ => ?_⟩, fun n x _ => Vn_bd S n _⟩
  have he := scale_nonneg S a n
  have hc := (interp_concaveOn (S.h_pos n) (S.isApproxEq n).cone.incr).2
    (show S.scale a n * x ∈ Ici (0:ℝ) from mul_nonneg he hx)
    (show S.scale a n * y ∈ Ici (0:ℝ) from mul_nonneg he hy) hα hβ hαβ
  simp only [smul_eq_mul] at hc ⊢
  unfold SelectedSeq.Wn SelectedSeq.Vn
  rw [show S.scale a n * (α * x + β * y) = α * (S.scale a n * x) + β * (S.scale a n * y) by ring]
  exact hc

/-! ### The crossing -/

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

/-! ### The limit profile `W` and its extension `W̄` -/

section NL

variable {S : SelectedSeq P} {a : ℝ}

private lemma W_facts (NL : NormalizedLimit S a) :
    MonotoneOn NL.W (Ioi 0) ∧ ConcaveOn ℝ (Ioi 0) NL.W ∧ ContinuousOn NL.W (Ioi 0) ∧
      (∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar) := by
  obtain ⟨hm, hc, hb⟩ := Wn_facts S a
  obtain ⟨g1, g2, g3, g4, -⟩ := concave_limit_props (fun n => hm (NL.φ n))
    (fun n => hc (NL.φ n)) (fun n => hb (NL.φ n)) NL.W_conv
  exact ⟨g1, g2, g3, g4⟩

private lemma W_img_nonempty (NL : NormalizedLimit S a) : (NL.W '' Ioi 0).Nonempty :=
  ⟨_, mem_image_of_mem _ (mem_Ioi.2 (one_pos : (0:ℝ) < 1))⟩

private lemma J'_le (NL : NormalizedLimit S a) {x : ℝ} (hx : 0 < x) : NL.J' ≤ NL.W x :=
  csInf_le ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact ((W_facts NL).2.2.2 y hy).1⟩ ⟨x, hx, rfl⟩

private lemma le_J' (NL : NormalizedLimit S a) {v : ℝ} (h : ∀ x, 0 < x → v ≤ NL.W x) :
    v ≤ NL.J' :=
  le_csInf (W_img_nonempty NL) (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

private lemma J'_nonneg (NL : NormalizedLimit S a) : 0 ≤ NL.J' :=
  le_J' NL fun x hx => ((W_facts NL).2.2.2 x hx).1

private lemma L_le (NL : NormalizedLimit S a) {v : ℝ} (h : ∀ x, 0 < x → NL.W x ≤ v) :
    NL.Lsup ≤ v :=
  csSup_le (W_img_nonempty NL) (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

private lemma Wbar_of_ne (NL : NormalizedLimit S a) {x : ℝ} (hx : x ≠ 0) :
    NL.Wbar x = NL.W x := by
  simp [NormalizedLimit.Wbar, hx]

private lemma Wbar_zero (NL : NormalizedLimit S a) : NL.Wbar 0 = NL.J' := by
  simp [NormalizedLimit.Wbar]

end NL

/-- Concavity across the boundary point: with `J ≤ W` on `(0, ∞)`, the chord from `(0, J)` lies
below `W`: `α J + β W(y) ≤ W(β y)`. -/
private lemma concave_edge {W : ℝ → ℝ} {J : ℝ} (gconc : ConcaveOn ℝ (Ioi 0) W)
    (gcont : ContinuousOn W (Ioi 0)) (hJ : ∀ x, 0 < x → J ≤ W x) {α β y : ℝ} (hα : 0 ≤ α)
    (hβ : 0 < β) (hαβ : α + β = 1) (hy : 0 < y) : α * J + β * W y ≤ W (β * y) := by
  have hby : 0 < β * y := mul_pos hβ hy
  have hT : Tendsto (fun ε => W (α * ε + β * y)) (𝓝[>] 0) (𝓝 (W (β * y))) := by
    have h1 : Tendsto (fun ε : ℝ => α * ε + β * y) (𝓝 0) (𝓝 (β * y)) := by
      have hc : Continuous fun ε : ℝ => α * ε + β * y := by fun_prop
      have := hc.tendsto 0
      simpa using this
    exact ((gcont.continuousAt (Ioi_mem_nhds hby)).tendsto.comp h1).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  have h2 := gconc.2 (show ε ∈ Ioi (0:ℝ) from hε) (show y ∈ Ioi (0:ℝ) from hy) hα hβ.le hαβ
  simp only [smul_eq_mul] at h2
  have h3 : α * J ≤ α * W ε := mul_le_mul_of_nonneg_left (hJ ε hε) hα
  linarith

section NL

variable {S : SelectedSeq P} {a : ℝ}

/-- `W̄` is continuous, nondecreasing and concave on `[0, ∞)`, with values in `[0, L_*]`. -/
private lemma Wbar_facts (NL : NormalizedLimit S a) :
    ContinuousOn NL.Wbar (Ici 0) ∧ MonotoneOn NL.Wbar (Ici 0) ∧ ConcaveOn ℝ (Ici 0) NL.Wbar ∧
      (∀ x, 0 ≤ x → 0 ≤ NL.Wbar x ∧ NL.Wbar x ≤ P.Lstar) := by
  obtain ⟨gmono, gconc, gcont, gbd⟩ := W_facts NL
  have hJ0 := J'_nonneg NL
  have hJL : NL.J' ≤ P.Lstar := (J'_le NL one_pos).trans (gbd 1 one_pos).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases (show (0:ℝ) ≤ x from hx).eq_or_lt with h | h
    · subst h
      rw [ContinuousWithinAt, Wbar_zero]
      refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
      · filter_upwards [self_mem_nhdsWithin] with y (hy : 0 ≤ y)
        rcases hy.eq_or_lt with h | h
        · rw [← h, Wbar_zero]; exact hb
        · rw [Wbar_of_ne NL h.ne']; exact hb.trans_le (J'_le NL h)
      · obtain ⟨_, ⟨x0, hx0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (W_img_nonempty NL) hb
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ) < x0 from hx0)),
          self_mem_nhdsWithin] with y hy1 (hy2 : 0 ≤ y)
        rcases hy2.eq_or_lt with h | h
        · rw [← h, Wbar_zero]; exact hb
        · rw [Wbar_of_ne NL h.ne']; exact (gmono h hx0 (le_of_lt hy1)).trans_lt hlt
    · have heq : NL.W =ᶠ[𝓝 x] NL.Wbar := by
        filter_upwards [Ioi_mem_nhds h] with y (hy : 0 < y) using (Wbar_of_ne NL hy.ne').symm
      exact ((gcont.continuousAt (Ioi_mem_nhds h)).congr heq).continuousWithinAt
  · intro x (hx : 0 ≤ x) y (hy : 0 ≤ y) hxy
    rcases hx.eq_or_lt with h | h
    · rw [← h, Wbar_zero]
      rcases hy.eq_or_lt with h' | h'
      · rw [← h', Wbar_zero]
      · rw [Wbar_of_ne NL h'.ne']; exact J'_le NL h'
    · have h' : 0 < y := h.trans_le hxy
      rw [Wbar_of_ne NL h.ne', Wbar_of_ne NL h'.ne']
      exact gmono h h' hxy
  · refine ⟨convex_Ici 0, fun x (hx : 0 ≤ x) y (hy : 0 ≤ y) α β hα hβ hαβ => ?_⟩
    simp only [smul_eq_mul]
    rcases hx.eq_or_lt with hx0 | hx0 <;> rcases hy.eq_or_lt with hy0 | hy0
    · rw [← hx0, ← hy0]
      simp only [mul_zero, add_zero, Wbar_zero]
      rw [← add_mul, hαβ, one_mul]
    · rw [← hx0, mul_zero, zero_add, Wbar_zero, Wbar_of_ne NL hy0.ne']
      rcases hβ.eq_or_lt with hβ0 | hβ0
      · obtain rfl : β = 0 := hβ0.symm
        obtain rfl : α = 1 := by linarith
        simp [Wbar_zero NL]
      · rw [Wbar_of_ne NL (mul_pos hβ0 hy0).ne']
        exact concave_edge gconc gcont (fun x hx => J'_le NL hx) hα hβ0 hαβ hy0
    · rw [← hy0, mul_zero, add_zero, Wbar_zero, Wbar_of_ne NL hx0.ne']
      rcases hα.eq_or_lt with hα0 | hα0
      · obtain rfl : α = 0 := hα0.symm
        obtain rfl : β = 1 := by linarith
        simp [Wbar_zero NL]
      · rw [Wbar_of_ne NL (mul_pos hα0 hx0).ne']
        have := concave_edge gconc gcont (fun x hx => J'_le NL hx) hβ hα0 (by linarith) hx0
        linarith
    · have hpos : 0 < α * x + β * y := by
        rcases hα.eq_or_lt with hα0 | hα0
        · obtain rfl : α = 0 := hα0.symm
          obtain rfl : β = 1 := by linarith
          simpa using hy0
        · exact add_pos_of_pos_of_nonneg (mul_pos hα0 hx0) (mul_nonneg hβ hy)
      rw [Wbar_of_ne NL hx0.ne', Wbar_of_ne NL hy0.ne', Wbar_of_ne NL hpos.ne']
      have := gconc.2 (show x ∈ Ioi (0:ℝ) from hx0) (show y ∈ Ioi (0:ℝ) from hy0) hα hβ hαβ
      simpa only [smul_eq_mul] using this
  · intro x hx
    rcases (show (0:ℝ) ≤ x from hx).eq_or_lt with h | h
    · rw [← h, Wbar_zero]; exact ⟨hJ0, hJL⟩
    · rw [Wbar_of_ne NL h.ne']; exact gbd x h

private lemma delta_nonneg (NL : NormalizedLimit S a) : 0 ≤ NL.δ := by
  rcases NL.lattice with h | h
  · exact h.1.ge
  · exact h.1.le

private lemma Xplus_pos (NL : NormalizedLimit S a) {z : ℝ} (hz : z ∈ NL.Xplus) : 0 < z := by
  unfold NormalizedLimit.Xplus at hz
  split_ifs at hz with hδ
  · exact hz
  · obtain ⟨k, hk, rfl⟩ := hz
    exact mul_pos (Nat.cast_pos.2 (by omega)) (lt_of_le_of_ne (delta_nonneg NL) (Ne.symm hδ))

end NL

/-! ### Compatible states -/

/-- The lattice `δ ℕ` is closed. -/
private lemma isClosed_natMul {δ : ℝ} (hδ : 0 < δ) : IsClosed {x : ℝ | ∃ k : ℕ, x = k * δ} := by
  have : {x : ℝ | ∃ k : ℕ, x = k * δ} = (fun x => x / δ) ⁻¹' range (Nat.cast : ℕ → ℝ) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_range]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, (mul_div_cancel_right₀ _ hδ.ne').symm⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; exact (div_mul_cancel₀ x hδ.ne').symm⟩
  rw [this]
  exact Nat.isClosedEmbedding_coe_real.isClosed_range.preimage (continuous_id.div_const δ)

section NL

variable {S : SelectedSeq P} {a : ℝ}

/-- The case analysis of the proof of `lem:normalizedlimits`: a limit of normalized states
`(z_j, F_j(z_j))`, with `F_j → W` locally uniformly on `(0, ∞)`, lies in `ℰ_W`. -/
private lemma mem_EW_of_tendsto (NL : NormalizedLimit S a) {F : ℕ → ℝ → ℝ}
    (hmono : ∀ n, MonotoneOn (F n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (F n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ F n x ∧ F n x ≤ P.Lstar)
    (hlim : TendstoLocallyUniformlyOn F NL.W atTop (Ioi 0)) {z : ℕ → ℝ} (hz0 : ∀ j, 0 ≤ z j)
    (hlat : 0 < NL.δ → ∀ j, ∃ k : ℕ, z j = k * NL.δ) {p : ℝ≥0∞ × ℝ}
    (hp : Tendsto (fun j => (ENNReal.ofReal (z j), F j (z j))) atTop (𝓝 p)) : p ∈ NL.EW := by
  have h1 : Tendsto (fun j => ENNReal.ofReal (z j)) atTop (𝓝 p.1) := hp.fst_nhds
  have h2 : Tendsto (fun j => F j (z j)) atTop (𝓝 p.2) := hp.snd_nhds
  have hv0 : 0 ≤ p.2 := ge_of_tendsto' h2 fun j => (hbd j _ (hz0 j)).1
  have hvL : p.2 ≤ P.Lstar := le_of_tendsto' h2 fun j => (hbd j _ (hz0 j)).2
  unfold NormalizedLimit.EW
  by_cases htop : p.1 = ⊤
  · -- normalized wealth escapes to `∞`
    have hz : Tendsto z atTop atTop := by
      refine tendsto_atTop.2 fun M => ?_
      have hM : ENNReal.ofReal M < p.1 := by rw [htop]; exact ENNReal.ofReal_lt_top
      filter_upwards [h1.eventually (lt_mem_nhds hM)] with j hj
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 hj).1.le
    have hge : ∀ x, 0 < x → NL.W x ≤ p.2 := by
      intro x hx
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := ge_of_tendsto h2
        (eventually_ge_of_tendsto_atTop hmono hconc hbd hlim hz hx hε)
      linarith
    exact mem_union_right _ (mem_prod.2 ⟨htop, L_le NL hge, hvL⟩)
  · have hz : Tendsto z atTop (𝓝 p.1.toReal) :=
      ((ENNReal.tendsto_toReal htop).comp h1).congr fun j => ENNReal.toReal_ofReal (hz0 j)
    by_cases h0 : p.1 = 0
    · -- normalized wealth collapses to `0`
      have hz' : Tendsto z atTop (𝓝 0) := by simpa [h0] using hz
      have hle : ∀ x, 0 < x → p.2 ≤ NL.W x := by
        intro x hx
        refine le_of_forall_pos_le_add fun ε hε => ?_
        exact le_of_tendsto h2 (eventually_le_of_tendsto_zero hmono hconc hbd hlim hz0 hz' hx hε)
      exact mem_union_left _ (mem_union_left _ (mem_prod.2 ⟨h0, hv0, le_J' NL hle⟩))
    · -- finite positive normalized wealth
      have hpos : 0 < p.1.toReal := ENNReal.toReal_pos h0 htop
      have hv : p.2 = NL.W p.1.toReal :=
        tendsto_nhds_unique h2 (tendsto_comp_of_concave hmono hconc hbd hlim hpos hz)
      refine mem_union_left _ (mem_union_right _ ⟨p.1.toReal, ?_,
        Prod.ext (ENNReal.ofReal_toReal htop).symm hv⟩)
      unfold NormalizedLimit.Xplus
      split_ifs with hδ
      · exact hpos
      · have hδpos : 0 < NL.δ := lt_of_le_of_ne (delta_nonneg NL) (Ne.symm hδ)
        obtain ⟨k, hk⟩ := (isClosed_natMul hδpos).mem_of_tendsto hz
          (Eventually.of_forall fun j => hlat hδpos j)
        refine ⟨k, ?_, hk⟩
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0, Nat.cast_zero, zero_mul] at hk; linarith
        · exact hk0

/-- `ℰ_W` is closed. -/
private lemma isClosed_EW (NL : NormalizedLimit S a) : IsClosed NL.EW := by
  obtain ⟨-, hmono, hconc, hbd⟩ := Wbar_facts NL
  have hlim : TendstoLocallyUniformlyOn (fun _ : ℕ => NL.Wbar) NL.W atTop (Ioi 0) := by
    intro u hu x _
    refine ⟨Ioi 0, self_mem_nhdsWithin, Eventually.of_forall fun n y (hy : 0 < y) => ?_⟩
    dsimp only
    rw [Wbar_of_ne NL hy.ne']
    exact refl_mem_uniformity hu
  have hG : closure {p : ℝ≥0∞ × ℝ | ∃ z ∈ NL.Xplus, p = (ENNReal.ofReal z, NL.W z)} ⊆ NL.EW := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := mem_closure_iff_seq_limit.1 hp
    choose z hzX hqz using hq
    refine mem_EW_of_tendsto NL (F := fun _ => NL.Wbar) (fun _ => hmono) (fun _ => hconc)
      (fun _ => hbd) hlim (z := z) (fun j => (Xplus_pos NL (hzX j)).le) ?_ ?_
    · intro hδ j
      have hX := hzX j
      unfold NormalizedLimit.Xplus at hX
      rw [ite_eq_right hδ.ne'] at hX
      obtain ⟨k, -, hk⟩ := hX
      exact ⟨k, hk⟩
    · refine hqp.congr fun j => ?_
      rw [hqz j, Wbar_of_ne NL (Xplus_pos NL (hzX j)).ne']
  have hA : IsClosed ({(0 : ℝ≥0∞)} ×ˢ Icc 0 NL.J') := isClosed_singleton.prod isClosed_Icc
  have hB : IsClosed ({(⊤ : ℝ≥0∞)} ×ˢ Icc NL.Lsup P.Lstar) :=
    isClosed_singleton.prod isClosed_Icc
  refine isClosed_of_closure_subset ?_
  have hEW := hG
  unfold NormalizedLimit.EW at hEW ⊢
  rw [closure_union, closure_union, hA.closure_eq, hB.closure_eq]
  exact union_subset (union_subset (subset_union_left.trans subset_union_left) hEW)
    subset_union_right

end NL

/-! ### `α` is carried by `ℰ_W` -/

private lemma tluo_comp {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {s : Set ℝ}
    (h : TendstoLocallyUniformlyOn F g atTop s) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    TendstoLocallyUniformlyOn (fun j => F (k j)) g atTop s := by
  intro u hu x hx
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hk.eventually hev⟩

/-- `lem:device` (b), second part, in a first-countable space. -/
private lemma exists_seq_of_mem_limsup {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {E : ℕ → Set X} {x : X} (hx : x ∈ ⋂ k, closure (⋃ n ≥ k, E n)) :
    ∃ n : ℕ → ℕ, ∃ y : ℕ → X, Tendsto n atTop atTop ∧ (∀ j, y j ∈ E (n j)) ∧
      Tendsto y atTop (𝓝 x) := by
  obtain ⟨U, hU⟩ := (𝓝 x).exists_antitone_basis
  have hj : ∀ j : ℕ, ∃ n, j ≤ n ∧ ∃ y ∈ E n, y ∈ U j := by
    intro j
    obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.1 (mem_iInter.1 hx j) (U j) (hU.mem j)
    simp only [mem_iUnion] at hy
    obtain ⟨n, hn, hyn⟩ := hy
    exact ⟨n, hn, y, hyn, hyU⟩
  choose n hn y hy hyU using hj
  exact ⟨n, y, tendsto_atTop_mono hn tendsto_id, hy, hU.tendsto hyU⟩

private lemma continuous_ι (S : SelectedSeq P) (a : ℝ) (n : ℕ) : Continuous (S.ι a n) :=
  (ENNReal.continuous_ofReal.comp (continuous_id.div_const _)).prodMk
    (continuous_interp (S.h_pos n))

private lemma αn_prob (S : SelectedSeq P) (a : ℝ) (n : ℕ) : IsProbabilityMeasure (S.αn a n) := by
  have := gridMeasure_isProb (S.isApproxEq n).law
  exact (Measure.isProbabilityMeasure_map_iff (continuous_ι S a n).measurable.aemeasurable).2 this

/-- The finitely many normalized states charged by `α_n`. -/
private def chargedStates (S : SelectedSeq P) (a : ℝ) (n : ℕ) : Set (ℝ≥0∞ × ℝ) :=
  (fun l : ℕ => S.ι a n (l * S.h n)) '' {l | l ≤ S.N n ∧ S.η n l ≠ 0}

private lemma αn_charged (S : SelectedSeq P) (a : ℝ) (n : ℕ) :
    S.αn a n (chargedStates S a n)ᶜ = 0 := by
  have hfin : (chargedStates S a n).Finite :=
    ((Set.finite_le_nat (S.N n)).subset fun l hl => hl.1).image _
  unfold SelectedSeq.αn
  rw [Measure.map_apply (continuous_ι S a n).measurable hfin.measurableSet.compl]
  have hae : ∀ᵐ s ∂(gridMeasure (S.h n) (S.N n) (S.η n)), S.ι a n s ∈ chargedStates S a n :=
    ae_gridMeasure (S.isApproxEq n).law.nonneg fun l hl hη => ⟨l, ⟨hl, hη⟩, rfl⟩
  exact ae_iff.1 hae

section NL

variable {S : SelectedSeq P} {a : ℝ}

/-- `α(ℰ_Wᶜ) = 0`. -/
private lemma α_EW (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) :
    NL.α NL.EWᶜ = 0 := by
  obtain ⟨hm, hc, hb⟩ := Wn_facts S a
  have hlim := WeakConv.measure_compl_limsup (fun n => αn_prob S a (NL.φ n)) NL.α_prob
    NL.α_conv (E := fun n => chargedStates S a (NL.φ n)) (fun n => αn_charged S a (NL.φ n))
  refine measure_mono_null (compl_subset_compl.2 ?_) hlim
  intro p hp
  obtain ⟨n, y, hn, hyE, hy⟩ := exists_seq_of_mem_limsup hp
  have hyE' : ∀ j, ∃ l : ℕ, (l ≤ S.N (NL.φ (n j)) ∧ S.η (NL.φ (n j)) l ≠ 0) ∧
      S.ι a (NL.φ (n j)) (l * S.h (NL.φ (n j))) = y j := hyE
  choose l _hl hyl using hyE'
  have hφn : Tendsto (fun j => NL.φ (n j)) atTop atTop := NL.φ_mono.tendsto_atTop.comp hn
  refine mem_EW_of_tendsto NL (F := fun j => S.Wn a (NL.φ (n j))) (fun j => hm _)
    (fun j => hc _) (fun j => hb _) (tluo_comp NL.W_conv hn)
    (z := fun j => l j * S.h (NL.φ (n j)) / S.scale a (NL.φ (n j)))
    (fun j => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.h_pos _).le) (scale_nonneg S a _))
    ?_ ?_
  · intro hδ j
    have hlat : S.δn a (NL.φ (n j)) = NL.δ := by
      rcases NL.lattice with h | h
      · exact absurd h.1 hδ.ne'
      · exact h.2 _
    refine ⟨l j, ?_⟩
    rw [← hlat, SelectedSeq.δn, mul_div_assoc]
  · refine hy.congr' ?_
    filter_upwards [hφn.eventually (eventually_good S ha haJ)] with j hj
    rw [← hyl j]
    have hpos : 0 < S.scale a (NL.φ (n j)) := mul_pos (S.h_pos _) (Nat.cast_pos.2 hj.2.2)
    have he : S.scale a (NL.φ (n j)) * (l j * S.h (NL.φ (n j)) / S.scale a (NL.φ (n j))) =
        l j * S.h (NL.φ (n j)) := by field_simp
    simp only [SelectedSeq.ι, SelectedSeq.Wn, he]

/-! ### The value marginal -/

/-- `eq:valueprojection`: `(pr_y)_# α = ν`. -/
private lemma α_snd (NL : NormalizedLimit S a) : NL.α.map Prod.snd = S.νlim := by
  have h1 := WeakConv.map (fun n => αn_prob S a (NL.φ n)) NL.α_prob NL.α_conv continuous_snd
  have heq : ∀ n, (S.αn a n).map Prod.snd =
      (gridMeasure (S.h n) (S.N n) (S.η n)).map (interp (S.h n) (S.N n) (S.V n)) := by
    intro n
    unfold SelectedSeq.αn
    rw [Measure.map_map measurable_snd (continuous_ι S a n).measurable]
    rfl
  simp only [heq] at h1
  have h2 := S.ν_conv.comp NL.φ_mono
  have hprob : ∀ n, IsProbabilityMeasure ((gridMeasure (S.h (NL.φ n)) (S.N (NL.φ n))
      (S.η (NL.φ n))).map (interp (S.h (NL.φ n)) (S.N (NL.φ n)) (S.V (NL.φ n)))) := fun n => by
    have := gridMeasure_isProb (S.isApproxEq (NL.φ n)).law
    exact (Measure.isProbabilityMeasure_map_iff
      (continuous_interp (S.h_pos _)).measurable.aemeasurable).2 this
  have hαprob : IsProbabilityMeasure (NL.α.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 NL.α_prob
  exact WeakConv.unique hprob hαprob S.νlim_prob h1 h2

/-! ### The normalization level -/

/-- `W(1) ≥ a`. -/
private lemma W_one_ge (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) :
    a ≤ NL.W 1 := by
  refine ge_of_tendsto (NL.W_conv.tendsto_at (mem_Ioi.2 (one_pos : (0:ℝ) < 1))) ?_
  filter_upwards [NL.φ_mono.tendsto_atTop.eventually (eventually_good S ha haJ)] with n hn
  show a ≤ S.Vn (NL.φ n) (S.scale a (NL.φ n) * 1)
  rw [show S.scale a (NL.φ n) * 1 = (S.crossIdx a (NL.φ n) : ℝ) * S.h (NL.φ n) by
    unfold SelectedSeq.scale; ring]
  unfold SelectedSeq.Vn
  rw [interp_natCast (S.h_pos _) hn.1]
  exact hn.2.1

/-- Non-lattice case: `W(1) = a` and `J' ≤ a`. -/
private lemma nonlattice_case (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump)
    (hδ : NL.δ = 0) : NL.W 1 = a ∧ NL.J' ≤ a := by
  have hδn : Tendsto (fun n => S.δn a (NL.φ n)) atTop (𝓝 0) := by
    rcases NL.lattice with h | h
    · exact h.2
    · exact absurd hδ h.1.ne'
  have hlt : ∀ x, 0 < x → x < 1 → NL.W x ≤ a := by
    intro x hx0 hx1
    refine le_of_tendsto (NL.W_conv.tendsto_at (show x ∈ Ioi (0:ℝ) from hx0)) ?_
    filter_upwards [NL.φ_mono.tendsto_atTop.eventually (eventually_good S ha haJ),
      hδn.eventually_lt_const (show (0:ℝ) < 1 - x by linarith)] with n hg hs
    obtain ⟨hcN, -, hc0⟩ := hg
    set m := NL.φ n with hm
    set c := S.crossIdx a m with hc
    have hh := S.h_pos m
    have hcpos : (0:ℝ) < c := Nat.cast_pos.2 hc0
    have hδeq : S.δn a m = 1 / c := by
      unfold SelectedSeq.δn SelectedSeq.scale
      rw [← hc]
      field_simp
    rw [hδeq, div_lt_iff₀ hcpos] at hs
    have hi1 : (⌈x * c⌉₊ : ℝ) < x * c + 1 := Nat.ceil_lt_add_one (by positivity)
    have hic : ⌈x * c⌉₊ < c := by
      have : (⌈x * c⌉₊ : ℝ) < c := by nlinarith
      exact_mod_cast this
    have hiN : ⌈x * c⌉₊ ≤ S.N m := hic.le.trans hcN
    have hVi : S.V m ⌈x * c⌉₊ < a := by
      have := Nat.notMem_of_lt_sInf hic
      simp only [mem_ofPred_eq, not_and, not_le] at this
      exact this hiN
    have hle : S.scale a m * x ≤ (⌈x * c⌉₊ : ℝ) * S.h m := by
      have := Nat.le_ceil (x * c)
      calc S.scale a m * x = (x * c) * S.h m := by unfold SelectedSeq.scale; rw [← hc]; ring
        _ ≤ (⌈x * c⌉₊ : ℝ) * S.h m := mul_le_mul_of_nonneg_right this hh.le
    show S.Vn m (S.scale a m * x) ≤ a
    calc S.Vn m (S.scale a m * x) ≤ S.Vn m ((⌈x * c⌉₊ : ℝ) * S.h m) := Vn_mono S m hle
      _ = S.V m ⌈x * c⌉₊ := interp_natCast hh hiN
      _ ≤ a := hVi.le
  have hW1 : NL.W 1 ≤ a := by
    have hc1 : ContinuousAt NL.W 1 := (W_facts NL).2.2.1.continuousAt (Ioi_mem_nhds one_pos)
    refine le_of_tendsto (hc1.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto NL.W (𝓝[<] 1) (𝓝 (NL.W 1))) ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    exact hlt x hx.1 hx.2
  refine ⟨le_antisymm hW1 (W_one_ge NL ha haJ), ?_⟩
  exact (J'_le NL (show (0:ℝ) < 1 / 2 by norm_num)).trans (hlt _ (by norm_num) (by norm_num))

end NL

/-! ### The lattice case -/

/-- In the lattice case every `W_n` is affine on the cells `[jδ, (j+1)δ]`. -/
private lemma Wn_cell (S : SelectedSeq P) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hδn : S.δn a n = δ) (j : ℕ) {x : ℝ} (hx : x ∈ Icc ((j : ℝ) * δ) ((j + 1) * δ)) :
    S.Wn a n x = S.Wn a n (j * δ) +
      (x - j * δ) / δ * (S.Wn a n ((j + 1) * δ) - S.Wn a n (j * δ)) := by
  have hh := S.h_pos n
  unfold SelectedSeq.δn at hδn
  have hne : S.scale a n ≠ 0 := by
    intro h0; rw [h0, div_zero] at hδn; linarith
  have he : S.scale a n = S.h n / δ := by
    rw [← hδn]; field_simp
  have hW : ∀ y, S.Wn a n y = interp (S.h n) (S.N n) (S.V n) (y / δ * S.h n) := by
    intro y; unfold SelectedSeq.Wn SelectedSeq.Vn; rw [he]; congr 1; ring
  simp only [hW]
  have h1 : (j : ℝ) * δ / δ * S.h n = (j : ℝ) * S.h n := by field_simp
  have h2 : ((j : ℝ) + 1) * δ / δ * S.h n = ((j + 1 : ℕ) : ℝ) * S.h n := by push_cast; field_simp
  rw [h1, h2]
  rcases lt_or_ge j (S.N n) with hj | hj
  · have hcell : x / δ * S.h n ∈ Icc ((j : ℝ) * S.h n) ((j + 1 : ℝ) * S.h n) := by
      constructor
      · exact mul_le_mul_of_nonneg_right ((le_div_iff₀ hδ).2 hx.1) hh.le
      · exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).2 hx.2) hh.le
    rw [interp_eq_on_cell hh hj hcell, interp_natCast hh hj.le,
      interp_natCast (i := j + 1) hh (by omega)]
    field_simp
  · have hjN : (S.N n : ℝ) ≤ j := by exact_mod_cast hj
    have hx' : (S.N n : ℝ) * S.h n ≤ x / δ * S.h n :=
      mul_le_mul_of_nonneg_right (hjN.trans ((le_div_iff₀ hδ).2 hx.1)) hh.le
    have hj' : (S.N n : ℝ) * S.h n ≤ (j : ℝ) * S.h n := mul_le_mul_of_nonneg_right hjN hh.le
    have hj1 : (S.N n : ℝ) * S.h n ≤ ((j + 1 : ℕ) : ℝ) * S.h n :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hh.le
    rw [interp_of_le hh hx', interp_of_le hh hj', interp_of_le hh hj1]
    ring

section NL

variable {S : SelectedSeq P} {a : ℝ}

/-- Lattice case: `J' = 0` and `W̄` is affine on every cell `[jδ, (j+1)δ]`. -/
private lemma lattice_case (NL : NormalizedLimit S a) (hδ : 0 < NL.δ) :
    NL.J' = 0 ∧ ∀ j : ℕ, ∀ x ∈ Icc (j * NL.δ) ((j + 1) * NL.δ),
      NL.Wbar x = NL.Wbar (j * NL.δ) +
        (x - j * NL.δ) / NL.δ * (NL.Wbar ((j + 1) * NL.δ) - NL.Wbar (j * NL.δ)) := by
  have hlat : ∀ n, S.δn a (NL.φ n) = NL.δ := by
    rcases NL.lattice with h | h
    · exact absurd h.1 hδ.ne'
    · exact h.2
  have hpt : ∀ y, 0 ≤ y → Tendsto (fun n => S.Wn a (NL.φ n) y) atTop (𝓝 (NL.W y)) := by
    intro y hy
    rcases hy.eq_or_lt with h | h
    · subst h
      have : ∀ n, S.Wn a (NL.φ n) 0 = 0 := fun n => by
        show S.Vn _ (S.scale a _ * 0) = 0
        rw [mul_zero]; exact Vn_zero S _
      simp only [this, NL.W_zero]
      exact tendsto_const_nhds
    · exact NL.W_conv.tendsto_at h
  have hjδ : ∀ j : ℕ, 0 ≤ (j : ℝ) * NL.δ := fun j => mul_nonneg (Nat.cast_nonneg j) hδ.le
  have hcell : ∀ j : ℕ, ∀ x ∈ Icc ((j : ℝ) * NL.δ) ((j + 1) * NL.δ),
      NL.W x = NL.W (j * NL.δ) +
        (x - j * NL.δ) / NL.δ * (NL.W ((j + 1) * NL.δ) - NL.W (j * NL.δ)) := by
    intro j x hx
    have h0 : 0 ≤ ((j : ℝ) + 1) * NL.δ := mul_nonneg (by positivity) hδ.le
    have hl := (hpt _ (hjδ j)).add
      (((hpt _ h0).sub (hpt _ (hjδ j))).const_mul ((x - j * NL.δ) / NL.δ))
    exact tendsto_nhds_unique (hpt x ((hjδ j).trans hx.1))
      (hl.congr fun n => (Wn_cell S a hδ (hlat n) j hx).symm)
  have hJ : NL.J' = 0 := by
    refine le_antisymm ?_ (J'_nonneg NL)
    have hT : Tendsto (fun x : ℝ => x / NL.δ * NL.W NL.δ) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x / NL.δ * NL.W NL.δ) (𝓝 0) (𝓝 (0 / NL.δ * NL.W NL.δ)) :=
        ((continuous_id.div_const _).mul continuous_const).tendsto 0
      rw [zero_div, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    have h := hcell 0 x ⟨by simpa using hx.1.le, by simpa using hx.2.le⟩
    simp only [Nat.cast_zero, zero_mul, zero_add, one_mul, NL.W_zero, sub_zero] at h
    have := J'_le NL hx.1
    linarith
  have hWbar : ∀ x, NL.Wbar x = NL.W x := by
    intro x
    by_cases hx : x = 0
    · rw [hx, Wbar_zero, hJ, NL.W_zero]
    · exact Wbar_of_ne NL hx
  refine ⟨hJ, fun j x hx => ?_⟩
  simp only [hWbar]
  exact hcell j x hx

end NL

/-- `lem:normalizedlimits` (properties): `e_n → 0`, `W(1) ≥ a > 0`; `W̄` is continuous, increasing
and concave on `[0, ∞)`; `ℰ_W` is closed of full `α`-measure; the value marginal of `α` is the
limiting value distribution `ν` (`eq:valueprojection`); in the non-lattice case `W(1) = a` and
`J' ≤ a`; in the lattice case `J' = 0` and `W̄` is affine on every cell `[jδ, (j+1)δ]`. -/
theorem NormalizedLimit.props {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) :
    Tendsto (fun n => S.scale a (NL.φ n)) atTop (𝓝 0) ∧ a ≤ NL.W 1 ∧
    ContinuousOn NL.Wbar (Ici 0) ∧ MonotoneOn NL.Wbar (Ici 0) ∧ ConcaveOn ℝ (Ici 0) NL.Wbar ∧
    (∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar) ∧
    IsClosed NL.EW ∧ NL.α NL.EWᶜ = 0 ∧ NL.α.map Prod.snd = S.νlim ∧
    (NL.δ = 0 → NL.W 1 = a ∧ NL.J' ≤ a) ∧
    (0 < NL.δ → NL.J' = 0 ∧ ∀ j : ℕ, ∀ x ∈ Icc (j * NL.δ) ((j + 1) * NL.δ),
      NL.Wbar x = NL.Wbar (j * NL.δ) +
        (x - j * NL.δ) / NL.δ * (NL.Wbar ((j + 1) * NL.δ) - NL.Wbar (j * NL.δ))) := by
  obtain ⟨hcont, hmono, hconc, -⟩ := Wbar_facts NL
  exact ⟨(scale_tendsto S haJ).comp NL.φ_mono.tendsto_atTop, W_one_ge NL ha haJ, hcont, hmono,
    hconc, (W_facts NL).2.2.2, isClosed_EW NL, α_EW NL ha haJ, α_snd NL,
    nonlattice_case NL ha haJ, lattice_case NL⟩

end Molico
