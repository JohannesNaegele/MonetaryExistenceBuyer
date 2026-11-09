import MonetaryExistenceBuyer.Saturation.Wdf

/-!
# Inverting dyadic decay (`lem:inversion`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### Grid facts along the selected sequence -/

private lemma scale_nonneg'' (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.scale a n :=
  mul_nonneg (S.h_pos n).le (Nat.cast_nonneg _)

private lemma δn_nonneg' (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.δn a n :=
  div_nonneg (S.h_pos n).le (scale_nonneg'' S a n)

private lemma scale_pos_of_δn_pos' (S : SelectedSeq P) (a : ℝ) {n : ℕ} (h : 0 < S.δn a n) :
    0 < S.scale a n := by
  rcases (scale_nonneg'' S a n).eq_or_lt with h0 | h0
  · rw [SelectedSeq.δn, ← h0, div_zero] at h; exact absurd h (lt_irrefl 0)
  · exact h0

private lemma Wn_grid' (S : SelectedSeq P) (a : ℝ) {n : ℕ} (he : 0 < S.scale a n) {i : ℕ}
    (hi : i ≤ S.N n) : S.Wn a n (i * S.δn a n) = S.V n i := by
  unfold SelectedSeq.Wn SelectedSeq.Vn SelectedSeq.δn
  rw [show S.scale a n * (i * (S.h n / S.scale a n)) = i * S.h n by field_simp]
  exact interp_natCast (S.h_pos n) hi

/-- `W_n = V_n(e_n ·)` is concave on `[0, ∞)`. -/
private lemma Wn_concave (S : SelectedSeq P) (a : ℝ) (n : ℕ) :
    ConcaveOn ℝ (Ici 0) (S.Wn a n) := by
  refine ⟨convex_Ici 0, fun x hx y hy α β hα hβ hαβ => ?_⟩
  have he := scale_nonneg'' S a n
  have hc := (interp_concaveOn (S.h_pos n) (S.isApproxEq n).cone.incr).2
    (show S.scale a n * x ∈ Ici (0:ℝ) from mul_nonneg he hx)
    (show S.scale a n * y ∈ Ici (0:ℝ) from mul_nonneg he hy) hα hβ hαβ
  simp only [smul_eq_mul] at hc ⊢
  unfold SelectedSeq.Wn SelectedSeq.Vn
  rw [show S.scale a n * (α * x + β * y) = α * (S.scale a n * x) + β * (S.scale a n * y) by ring]
  exact hc

/-- Grid slopes are positive (`lem:slopepos`; the floor `V(N) ≥ ℓ₀ > 0` gives `V ≢ 0`). -/
private lemma V_strict' (S : SelectedSeq P) (n : ℕ) :
    ∀ i, i < S.N n → S.V n i < S.V n (i + 1) := by
  have hE := S.isApproxEq n
  exact slopepos P.U P.β_pos P.β_lt_one hE.cone.incr hE.cone.zero hE.law.nonneg hE.law.sum_one
    hE.bellman ⟨S.N n, le_rfl, (lt_of_lt_of_le P.uniformfloor.1 (S.floor n).1).ne'⟩

/-- Four-point secant inequality for a concave function on `[0, ∞)`. -/
private lemma concave_four {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f) {x1 x2 x3 x4 : ℝ}
    (h0 : 0 ≤ x1) (h12 : x1 < x2) (h23 : x2 ≤ x3) (h34 : x3 < x4) :
    (f x4 - f x3) / (x4 - x3) ≤ (f x2 - f x1) / (x2 - x1) := by
  have hg := hf.neg
  have h1 := hg.secant_mono_aux2 (mem_Ici.2 h0) (mem_Ici.2 (by linarith : (0:ℝ) ≤ x4)) h12
    (by linarith : x2 < x4)
  have h2 := hg.secant_mono_aux3 (mem_Ici.2 h0) (mem_Ici.2 (by linarith : (0:ℝ) ≤ x4))
    (by linarith : x1 < x3) h34
  simp only [Pi.neg_apply] at h1 h2
  have e : ∀ u v w z : ℝ, (-u - -v) / (w - z) = -((u - v) / (w - z)) := fun u v w z => by ring
  rw [e, e] at h1
  rw [e, e] at h2
  linarith

/-- Concavity: `i (V(i) - V(i-1)) ≤ V(i)`. -/
private lemma mul_step_le {V : ℕ → ℝ} {N : ℕ} (hV : IncrSeq V N) (h0 : V 0 = 0) {i : ℕ}
    (hi1 : 1 ≤ i) (hiN : i ≤ N) : (i : ℝ) * (V i - V (i - 1)) ≤ V i := by
  have key : ∀ t, t ≤ i → (t : ℝ) * (V i - V (i - 1)) ≤ V i - V (i - t) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := hV.step_anti (x := i - t - 1) (y := i - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel hi1, show i - t - 1 + 1 = i - t by omega] at h2
      rw [show i - (t + 1) = i - t - 1 by omega]
      push_cast
      linarith
  have := key i le_rfl
  rwa [Nat.sub_self, h0, sub_zero] at this

section NL

variable {S : SelectedSeq P} {a : ℝ}

/-- Without a finite-wealth saturation, `W(A) < W(A+1)` for every `A > 0`. -/
private lemma W_lt (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump)
    (hnp : ¬ NL.HasFiniteSaturation) {A : ℝ} (hA : 0 < A) : NL.W A < NL.W (A + 1) := by
  obtain ⟨-, -, -, hmono, hconc, hbd, -⟩ := NL.props ha haJ
  have hWbar : ∀ x, 0 < x → NL.Wbar x = NL.W x := fun x hx => by
    simp [NormalizedLimit.Wbar, hx.ne']
  have hA1 : 0 < A + 1 := by linarith
  have hle : NL.W A ≤ NL.W (A + 1) := by
    have := hmono (mem_Ici.2 hA.le) (mem_Ici.2 hA1.le) (by linarith : A ≤ A + 1)
    rwa [hWbar A hA, hWbar _ hA1] at this
  refine lt_of_le_of_ne hle fun heq => hnp ⟨A, hA, le_antisymm ?_ ?_⟩
  · exact le_csSup ⟨P.Lstar, by rintro _ ⟨y, hy, rfl⟩; exact (hbd y hy).2⟩ ⟨A, hA, rfl⟩
  · refine csSup_le ⟨_, mem_image_of_mem _ (mem_Ioi.2 hA)⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 < x := hx
    rcases le_or_gt x (A + 1) with hx1 | hx1
    · have := hmono (mem_Ici.2 hx0.le) (mem_Ici.2 hA1.le) hx1
      rw [hWbar x hx0, hWbar _ hA1] at this; linarith
    · have := hconc.slope_anti_adjacent (mem_Ici.2 hA.le) (mem_Ici.2 hx0.le)
        (show A < A + 1 by linarith) hx1
      rw [hWbar A hA, hWbar _ hA1, hWbar x hx0, ← heq, sub_self, zero_div,
        div_le_iff₀ (by linarith), zero_mul] at this
      linarith

/-- If `r δ_n ≤ A`, concavity gives `v_{n,r} ≥ W_n(A+1) - W_n(A)`. -/
private lemma slope_ge (NL : NormalizedLimit S a) {n r : ℕ} (hr1 : 1 ≤ r) (hrN : r ≤ NL.Nn n)
    (hδ : 0 < NL.δ' n) {A : ℝ} (hrA : (r : ℝ) * NL.δ' n ≤ A) :
    S.Wn a (NL.φ n) (A + 1) - S.Wn a (NL.φ n) A ≤ NL.slope n r := by
  have he := scale_pos_of_δn_pos' S a hδ
  have hcast : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub hr1]; simp
  have hx1 : (0:ℝ) ≤ ((r - 1 : ℕ) : ℝ) * NL.δ' n := by positivity
  have h12 : ((r - 1 : ℕ) : ℝ) * NL.δ' n < r * NL.δ' n := by rw [hcast]; nlinarith
  have key := concave_four (Wn_concave S a (NL.φ n)) hx1 h12 hrA (by linarith : A < A + 1)
  have hN : r ≤ S.N (NL.φ n) := hrN
  unfold NormalizedLimit.δ' at key
  rw [Wn_grid' S a he hN, Wn_grid' S a he (by omega : r - 1 ≤ S.N (NL.φ n)),
    show A + 1 - A = 1 by ring, div_one, hcast,
    show (r : ℝ) * S.δn a (NL.φ n) - (r - 1) * S.δn a (NL.φ n) = S.δn a (NL.φ n) by ring] at key
  exact key

/-- `v_{n,i} ≤ L_* / (i δ_n)`. -/
private lemma slope_mul_le (NL : NormalizedLimit S a) {n i : ℕ} (hi1 : 1 ≤ i) (hiN : i ≤ NL.Nn n)
    (hδ : 0 < NL.δ' n) : NL.slope n i * ((i : ℝ) * NL.δ' n) ≤ P.Lstar := by
  have hE := S.isApproxEq (NL.φ n)
  have h1 := mul_step_le hE.cone.incr hE.cone.zero hi1 hiN
  have h3 := (S.floor (NL.φ n)).2
  have e : NL.slope n i * ((i : ℝ) * NL.δ' n) =
      (i : ℝ) * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) := by
    unfold NormalizedLimit.slope; field_simp
  rw [e]
  have : S.V (NL.φ n) i ≤ S.V (NL.φ n) (S.N (NL.φ n)) := hE.cone.incr.le_of_le hiN le_rfl
  linarith

end NL

/-- `lem:inversion` (inverting dyadic decay): if `v_{n,r_n} ≤ D v_{n,i_n}` with
`i_n δ_n → ∞`, then `liminf r_n / i_n ≥ 1/R_D`. -/
theorem NormalizedLimit.inversion {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation)
    (htight : NL.α {p | p.1 = ⊤} = 0) (hC : NL.Cbar ≤ P.σ) {D : ℝ} (hD : 0 < D) :
    ∃ RD ≥ (1 : ℝ), ∀ i r : ℕ → ℕ, (∀ n, 1 ≤ i n ∧ i n ≤ NL.Nn n) →
      (∀ n, 1 ≤ r n ∧ r n ≤ NL.Nn n) →
      Tendsto (fun n => (i n : ℝ) * NL.δ' n) atTop atTop →
      (∀ n, NL.slope n (r n) ≤ D * NL.slope n (i n)) →
      ∀ c < 1 / RD, ∀ᶠ n in atTop, c ≤ (r n : ℝ) / i n := by
  obtain ⟨εd, hεd, -, Kd, nd, hb⟩ := NL.wdf ha haJ hnp htight hC
  -- `j_D ε_d > log D`, `R_D = 2^{j_D}`
  set jD : ℕ := ⌈Real.log D / εd⌉₊ + 1 with hjD_def
  have hjD : Real.log D < jD * εd := by
    have h1 : Real.log D / εd ≤ ⌈Real.log D / εd⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hεd] at h1
    have h2 : (jD : ℝ) = ⌈Real.log D / εd⌉₊ + 1 := by rw [hjD_def]; push_cast; ring
    rw [h2]; nlinarith
  refine ⟨(2:ℝ) ^ jD, one_le_pow₀ (by norm_num), fun i r hi hr hiδ hrD c hc => ?_⟩
  -- positivity and monotonicity of the slopes
  have hpos : ∀ n s, 1 ≤ s → s ≤ NL.Nn n → 0 < NL.δ' n → 0 < NL.slope n s := by
    intro n s hs1 hsN hδ
    have := V_strict' S (NL.φ n) (s - 1) (by unfold NormalizedLimit.Nn at hsN; omega)
    rw [Nat.sub_add_cancel hs1] at this
    exact div_pos (by linarith) hδ
  have hanti : ∀ n x y, 1 ≤ x → x ≤ y → y ≤ NL.Nn n → 0 < NL.δ' n →
      NL.slope n y ≤ NL.slope n x := by
    intro n x y hx hxy hy hδ
    have := (S.isApproxEq (NL.φ n)).cone.incr.step_anti (x := x - 1) (y := y - 1) (by omega)
      (by unfold NormalizedLimit.Nn at hy; omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ y), Nat.sub_add_cancel hx] at this
    exact div_le_div_of_nonneg_right this hδ.le
  -- Step 1: `r_n δ_n → ∞`, in the form: eventually `r_n δ_n ≥ K_d`
  have hstep1 : ∀ᶠ n in atTop, Kd ≤ (r n : ℝ) * NL.δ' n := by
    set A := max Kd 1 with hA_def
    have hA : 0 < A := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hg : 0 < NL.W (A + 1) - NL.W A := sub_pos.2 (W_lt NL ha haJ hnp hA)
    have hconv : Tendsto (fun n => S.Wn a (NL.φ n) (A + 1) - S.Wn a (NL.φ n) A) atTop
        (𝓝 (NL.W (A + 1) - NL.W A)) :=
      (NL.W_conv.tendsto_at (mem_Ioi.2 (by linarith))).sub (NL.W_conv.tendsto_at (mem_Ioi.2 hA))
    have hsmall : Tendsto (fun n => D * P.Lstar / ((i n : ℝ) * NL.δ' n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hiδ
    filter_upwards [hconv.eventually (lt_mem_nhds (half_lt_self hg)),
      hsmall.eventually (gt_mem_nhds (half_pos hg)), hiδ.eventually_gt_atTop 0] with n h1 h2 h3
    by_contra hlt
    push Not at hlt
    have hδ : 0 < NL.δ' n := by
      rcases (δn_nonneg' S a (NL.φ n)).eq_or_lt with h | h
      · exfalso; rw [NormalizedLimit.δ', ← h, mul_zero] at h3; exact lt_irrefl _ h3
      · exact h
    have hrA : (r n : ℝ) * NL.δ' n ≤ A := hlt.le.trans (le_max_left _ _)
    have hv1 := slope_ge NL (hr n).1 (hr n).2 hδ hrA
    have hv2 := slope_mul_le NL (hi n).1 (hi n).2 hδ
    have hv3 : D * NL.slope n (i n) ≤ D * P.Lstar / ((i n : ℝ) * NL.δ' n) := by
      rw [le_div_iff₀ h3, mul_assoc]
      exact mul_le_mul_of_nonneg_left hv2 hD.le
    linarith [hrD n]
  -- Step 2: dyadic chaining of `eq:wdf`
  filter_upwards [hstep1, eventually_ge_atTop nd, hiδ.eventually_gt_atTop 0] with n hrn hn hin
  have hδ : 0 < NL.δ' n := by
    rcases (δn_nonneg' S a (NL.φ n)).eq_or_lt with h | h
    · exfalso; rw [NormalizedLimit.δ', ← h, mul_zero] at hin; exact lt_irrefl _ hin
    · exact h
  obtain ⟨hr1, hrN⟩ := hr n
  obtain ⟨hi1, hiN⟩ := hi n
  have hle : i n ≤ 2 ^ jD * r n := by
    by_contra hlt
    push Not at hlt
    -- `t ε_d ≤ log v_r - log v_{2^t r}` for `t ≤ j_D`
    have chain : ∀ t, t ≤ jD → (t : ℝ) * εd ≤
        Real.log (NL.slope n (r n)) - Real.log (NL.slope n (2 ^ t * r n)) := by
      intro t
      induction t with
      | zero => intro _; simp
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have hpt : 2 ^ t * r n ≤ 2 ^ jD * r n :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hpt1 : 2 * (2 ^ t * r n) ≤ 2 ^ jD * r n := by
          rw [← mul_assoc, ← pow_succ']
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) ht)
        have hK : Kd ≤ ((2 ^ t * r n : ℕ) : ℝ) * NL.δ' n := by
          refine hrn.trans (mul_le_mul_of_nonneg_right ?_ hδ.le)
          exact_mod_cast Nat.le_mul_of_pos_left _ (Nat.two_pow_pos t)
        have h2 := hb n hn (2 ^ t * r n) hK (by omega)
        have hp1 := hpos n (2 ^ t * r n) (by nlinarith [Nat.one_le_two_pow (n := t)]) (by omega) hδ
        have hp2 := hpos n (2 * (2 ^ t * r n)) (by nlinarith [Nat.one_le_two_pow (n := t)])
          (by omega) hδ
        rw [Real.log_div hp1.ne' hp2.ne'] at h2
        rw [show 2 ^ (t + 1) * r n = 2 * (2 ^ t * r n) by ring]
        push_cast
        linarith
    have h1 := chain jD le_rfl
    have hpj : 1 ≤ 2 ^ jD * r n := by nlinarith [Nat.one_le_two_pow (n := jD)]
    have h2 := hanti n (2 ^ jD * r n) (i n) hpj hlt.le hiN hδ
    have hvi := hpos n (i n) hi1 hiN hδ
    have hvr := hpos n (r n) hr1 hrN hδ
    have h3 := Real.log_le_log hvi h2
    have h4 : Real.log (NL.slope n (r n)) ≤ Real.log D + Real.log (NL.slope n (i n)) := by
      rw [← Real.log_mul hD.ne' hvi.ne']
      exact Real.log_le_log hvr (hrD n)
    linarith
  have hle' : (i n : ℝ) ≤ (2:ℝ) ^ jD * r n := by exact_mod_cast hle
  have hi0 : (0:ℝ) < i n := by exact_mod_cast hi1
  have : 1 / (2:ℝ) ^ jD ≤ (r n : ℝ) / i n := by
    rw [div_le_div_iff₀ (by positivity) hi0]; linarith
  linarith

end Molico
