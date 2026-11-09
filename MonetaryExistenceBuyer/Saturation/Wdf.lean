import MonetaryExistenceBuyer.Saturation.Coeff

/-!
# Dyadic slope decay (`thm:wdf`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### The marginal utility on all of `ℝ` (`u'₋ = c₀` on `(-∞, 0]`) -/

private lemma marg_of_nonpos (U : AdmissibleUtility) {x : ℝ} (hx : x ≤ 0) : U.marg x = U.c0 := by
  simp [AdmissibleUtility.marg, hx]

private lemma marg_le_c0' (U : AdmissibleUtility) (x : ℝ) : U.marg x ≤ U.c0 := by
  rcases le_or_gt x 0 with hx | hx
  · rw [marg_of_nonpos U hx]
  · exact U.marg_le_c0 hx.le

private lemma marg_pos' (U : AdmissibleUtility) (x : ℝ) : 0 < U.marg x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [marg_of_nonpos U hx]; exact U.c0_pos
  · exact U.marg_pos hx.le

private lemma marg_antitone (U : AdmissibleUtility) : Antitone U.marg := by
  intro x y hxy
  rcases le_or_gt y 0 with hy | hy
  · rw [marg_of_nonpos U hy, marg_of_nonpos U (hxy.trans hy)]
  rcases le_or_gt x 0 with hx | hx
  · rw [marg_of_nonpos U hx]; exact U.marg_le_c0 hy.le
  · exact U.marg_antitoneOn (mem_Ici.2 hx.le) (mem_Ici.2 hy.le) hxy

private lemma marg_usc (U : AdmissibleUtility) : UpperSemicontinuous U.marg := by
  intro x c hc
  rcases le_or_gt x 0 with hx | hx
  · rw [marg_of_nonpos U hx] at hc
    exact Eventually.of_forall fun z => (marg_le_c0' U z).trans_lt hc
  · have h := U.marg_upperSemicontinuousOn x (mem_Ici.2 hx.le) c hc
    rwa [nhdsWithin_eq_nhds.2 (Ici_mem_nhds hx)] at h

/-! ### The comparison integrand `F(y) = max{1, u'₋(c - y)}` -/

/-- The integrand `F_ε(y) = max{1, u'₋(c - y)}` of the proof of `thm:wdf` (with `c = L - ε`). -/
private def Fc (U : AdmissibleUtility) (c y : ℝ) : ℝ := max 1 (U.marg (c - y))

private lemma Fc_mono (U : AdmissibleUtility) (c : ℝ) : Monotone (Fc U c) := fun _ _ h =>
  max_le_max le_rfl (marg_antitone U (by linarith))

private lemma one_le_Fc (U : AdmissibleUtility) (c y : ℝ) : 1 ≤ Fc U c y := le_max_left _ _

private lemma Fc_le (P : Primitives) (c y : ℝ) : Fc P.U c y ≤ P.U.c0 :=
  max_le P.c0_gt_one.le (marg_le_c0' _ _)

private lemma abs_Fc_le (P : Primitives) (c y : ℝ) : |Fc P.U c y| ≤ P.U.c0 := by
  rw [abs_of_pos (lt_of_lt_of_le one_pos (one_le_Fc _ _ _))]; exact Fc_le P c y

private lemma Fc_usc (U : AdmissibleUtility) (c : ℝ) :
    UpperSemicontinuous fun p : ℝ≥0∞ × ℝ => Fc U c p.2 := by
  have h1 : UpperSemicontinuous fun p : ℝ≥0∞ × ℝ => U.marg (c - p.2) :=
    (marg_usc U).comp (continuous_const.sub continuous_snd)
  exact upperSemicontinuous_const.sup h1

/-- Left continuity of `u'₋` at positive arguments and the convention at the origin:
`F_{c - 1/(m+1)}(y) → F_c(y)`. -/
private lemma tendsto_Fc (U : AdmissibleUtility) (c y : ℝ) :
    Tendsto (fun m : ℕ => Fc U (c - 1 / ((m : ℝ) + 1)) y) atTop (𝓝 (Fc U c y)) := by
  have hx : Tendsto (fun m : ℕ => c - 1 / ((m : ℝ) + 1) - y) atTop (𝓝 (c - y)) := by
    have := (tendsto_const_nhds (x := c)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this.sub_const y
  have hm : Tendsto (fun m : ℕ => U.marg (c - 1 / ((m : ℝ) + 1) - y)) atTop
      (𝓝 (U.marg (c - y))) := by
    rcases le_or_gt (c - y) 0 with h | h
    · have e : ∀ m : ℕ, U.marg (c - 1 / ((m : ℝ) + 1) - y) = U.marg (c - y) := fun m => by
        have : 0 < 1 / ((m : ℝ) + 1) := by positivity
        rw [marg_of_nonpos U h, marg_of_nonpos U (by linarith)]
      simp only [e]; exact tendsto_const_nhds
    · refine (U.marg_continuousWithinAt_Iic h).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun m => ?_⟩)
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      simp only [mem_Iic]; linarith
  exact tendsto_const_nhds.max hm

/-! ### Grid facts along the selected sequence -/

private lemma scale_nonneg' (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.scale a n :=
  mul_nonneg (S.h_pos n).le (Nat.cast_nonneg _)

private lemma δn_nonneg (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.δn a n :=
  div_nonneg (S.h_pos n).le (scale_nonneg' S a n)

private lemma scale_pos_of_δn_pos (S : SelectedSeq P) (a : ℝ) {n : ℕ} (h : 0 < S.δn a n) :
    0 < S.scale a n := by
  rcases (scale_nonneg' S a n).eq_or_lt with h0 | h0
  · rw [SelectedSeq.δn, ← h0, div_zero] at h; exact absurd h (lt_irrefl 0)
  · exact h0

private lemma Wn_grid (S : SelectedSeq P) (a : ℝ) {n : ℕ} (he : 0 < S.scale a n) {i : ℕ}
    (hi : i ≤ S.N n) : S.Wn a n (i * S.δn a n) = S.V n i := by
  unfold SelectedSeq.Wn SelectedSeq.Vn SelectedSeq.δn
  rw [show S.scale a n * (i * (S.h n / S.scale a n)) = i * S.h n by field_simp]
  exact interp_natCast (S.h_pos n) hi

private lemma Wn_mono (S : SelectedSeq P) (a : ℝ) (n : ℕ) : Monotone (S.Wn a n) := fun _ _ hxy =>
  interp_monotone (S.h_pos n) (S.isApproxEq n).cone.incr
    (mul_le_mul_of_nonneg_left hxy (scale_nonneg' S a n))

/-- Grid slopes are positive (`lem:slopepos`; the floor `V(N) ≥ ℓ₀ > 0` gives `V ≢ 0`). -/
private lemma V_strict (S : SelectedSeq P) (n : ℕ) :
    ∀ i, i < S.N n → S.V n i < S.V n (i + 1) := by
  have hE := S.isApproxEq n
  exact slopepos P.U P.β_pos P.β_lt_one hE.cone.incr hE.cone.zero hE.law.nonneg hE.law.sum_one
    hE.bellman ⟨S.N n, le_rfl, (lt_of_lt_of_le P.uniformfloor.1 (S.floor n).1).ne'⟩

private lemma ι_meas (S : SelectedSeq P) (a : ℝ) (n : ℕ) : Measurable (S.ι a n) :=
  ((ENNReal.continuous_ofReal.comp (continuous_id.div_const _)).prodMk
    (continuous_interp (S.h_pos n))).measurable

private lemma αn_isProb (S : SelectedSeq P) (a : ℝ) (n : ℕ) :
    IsProbabilityMeasure (S.αn a n) := by
  have := gridMeasure_isProb (S.isApproxEq n).law
  exact (Measure.isProbabilityMeasure_map_iff (ι_meas S a n).aemeasurable).2 this

/-- `∫ G(y) dα_n(z, y) = ∑_l η_l G(V(l))` (`eq:jointstates`). -/
private lemma integral_αn (S : SelectedSeq P) (a : ℝ) (n : ℕ) {G : ℝ → ℝ} (hG : Measurable G) :
    ∫ p, G p.2 ∂S.αn a n = ∑ l ∈ Finset.range (S.N n + 1), S.η n l * G (S.V n l) := by
  unfold SelectedSeq.αn
  rw [integral_map (f := fun p : ℝ≥0∞ × ℝ => G p.2) (ι_meas S a n).aemeasurable
    (hG.comp measurable_snd).aestronglyMeasurable]
  unfold SelectedSeq.ηn
  rw [integral_gridMeasure (S.isApproxEq n).law.nonneg]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [SelectedSeq.ι, SelectedSeq.Vn]
  rw [interp_natCast (S.h_pos n) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))]

/-- `α_n{y ≥ 0} = 1`, hence `y ≥ 0` for `α`-almost every `(z, y)`. -/
private lemma ae_snd_nonneg {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a) :
    ∀ᵐ p ∂NL.α, 0 ≤ p.2 := by
  have hC : IsClosed {p : ℝ≥0∞ × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
  have hprob := fun n => αn_isProb S a (NL.φ n)
  have h1 : (1 : ℝ≥0∞) ≤ NL.α {p | 0 ≤ p.2} := by
    refine NL.α_conv.le_measure_closed hprob NL.α_prob hC (Eventually.of_forall fun n => ?_)
    unfold SelectedSeq.αn
    rw [Measure.map_apply (ι_meas S a _) hC.measurableSet]
    have : S.ι a (NL.φ n) ⁻¹' {p | 0 ≤ p.2} = univ := by
      ext s
      simp only [mem_preimage, mem_ofPred_eq, SelectedSeq.ι, mem_univ, iff_true]
      have := (interp_mem_Icc (S.h_pos (NL.φ n)) (S.isApproxEq (NL.φ n)).cone.incr s).1
      rwa [(S.isApproxEq (NL.φ n)).cone.zero] at this
    rw [this]
    have : IsProbabilityMeasure (S.ηn (NL.φ n)) := gridMeasure_isProb (S.isApproxEq (NL.φ n)).law
    exact le_of_eq (measure_univ).symm
  have := NL.α_prob
  have hc : NL.α {p | 0 ≤ p.2}ᶜ = 0 :=
    (prob_compl_eq_zero_iff hC.measurableSet).2 (le_antisymm prob_le_one h1)
  exact measure_mono_null (fun p hp => hp) hc

/-! ### The grid core of `thm:wdf` -/

/-- Evaluate `eq:adjnorm` at `i = 2k` and bound every `ρ_{n,s,i}` by `e^{ε} F(V(l))` via
`lem:neighbour`, assuming `v_k ≤ e^{ε} v_{2k}` and `c ≤ V(k)`. -/
private lemma grid_core {h : ℝ} {N : ℕ} {V η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ}
    (hE : Grid.IsApproxEq P h N V η κ) (hstrict : ∀ i, i < N → V i < V (i + 1))
    {k : ℕ} (hk1 : 1 ≤ k) (hkN : 2 * k ≤ N) {c ε : ℝ} (hc : c ≤ V k)
    (hdk : V k - V (k - 1) ≤ Real.exp ε * (V (2 * k) - V (2 * k - 1))) :
    1 ≤ P.β * Real.exp ε * ∑ l ∈ Finset.range (N + 1), η l * Fc P.U c (V l) := by
  have hV := hE.cone.incr
  have danti : ∀ x y, 1 ≤ x → x ≤ y → y ≤ N → V y - V (y - 1) ≤ V x - V (x - 1) := by
    intro x y hx hxy hy
    have := hV.step_anti (x := x - 1) (y := y - 1) (by omega) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ y), Nat.sub_add_cancel hx] at this
  have hi1 : 1 ≤ 2 * k := by omega
  have dpos : 0 < V (2 * k) - V (2 * k - 1) := by
    have := hstrict (2 * k - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at this; linarith
  set di := V (2 * k) - V (2 * k - 1) with hdi
  have hexp := Real.exp_pos ε
  have hed : 0 ≤ Real.exp ε * di := by positivity
  have hp : ∀ l ∈ Finset.range (N + 1),
      Grid.gH P.U.u N V (2 * k) l - Grid.gH P.U.u N V (2 * k - 1) l ≤
        Real.exp ε * di * Fc P.U c (V l) := by
    intro l hl
    have hlN : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    obtain ⟨j, hj, hmax⟩ := Grid.exists_gH_eq P.U (V := V) hkN hlN
    have hjf := (Grid.mem_feas hkN hlN).1 hj
    obtain ⟨n1, n2, -, -⟩ := neighbour P.U hE.cone hi1 hkN hlN hj hmax
    have hF1 := one_le_Fc P.U c (V l)
    by_cases hB : k ≤ 2 * k - j
    · calc _ ≤ V (2 * k - j) - V (2 * k - j - 1) := n1 (by omega)
        _ ≤ V k - V (k - 1) := danti k (2 * k - j) hk1 hB (by omega)
        _ ≤ Real.exp ε * di := hdk
        _ = Real.exp ε * di * 1 := by ring
        _ ≤ Real.exp ε * di * Fc P.U c (V l) := mul_le_mul_of_nonneg_left hF1 hed
    · have hj1 : 1 ≤ j := by omega
      obtain ⟨h1, h2⟩ := n2 hj1
      have hS := danti k (l + j) hk1 (by omega) hjf.2
      have hΔ : c - V l ≤ V (l + (j - 1)) - V l := by
        have := hV.le_of_le (show k ≤ l + (j - 1) by omega) (by omega); linarith
      have hm := marg_antitone P.U hΔ
      have hmpos := (marg_pos' P.U (V (l + (j - 1)) - V l)).le
      calc _ ≤ _ := h1
        _ ≤ _ := h2
        _ ≤ P.U.marg (V (l + (j - 1)) - V l) * (Real.exp ε * di) :=
            mul_le_mul_of_nonneg_left (hS.trans hdk) hmpos
        _ ≤ P.U.marg (c - V l) * (Real.exp ε * di) := mul_le_mul_of_nonneg_right hm hed
        _ ≤ Fc P.U c (V l) * (Real.exp ε * di) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hed
        _ = _ := by ring
  have hadj := adjnorm hE hi1 hkN
  have hsum : ∑ l ∈ Finset.range (N + 1),
      η l * (Grid.gH P.U.u N V (2 * k) l - Grid.gH P.U.u N V (2 * k - 1) l) ≤
        ∑ l ∈ Finset.range (N + 1), η l * (Real.exp ε * di * Fc P.U c (V l)) :=
    Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (hp l hl) (hE.law.nonneg l)
  have key : di ≤ di * (P.β * Real.exp ε * ∑ l ∈ Finset.range (N + 1), η l * Fc P.U c (V l)) := by
    calc di = _ := hadj
      _ ≤ P.β * ∑ l ∈ Finset.range (N + 1), η l * (Real.exp ε * di * Fc P.U c (V l)) :=
          mul_le_mul_of_nonneg_left hsum P.β_pos.le
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
  exact (le_mul_iff_one_le_right dpos).1 key

/-! ### Limit facts -/

section NL

variable {S : SelectedSeq P} {a : ℝ}

private lemma img_nonempty (NL : NormalizedLimit S a) : (NL.W '' Ioi 0).Nonempty :=
  ⟨_, mem_image_of_mem _ (mem_Ioi.2 (one_pos : (0:ℝ) < 1))⟩

private lemma L_le_Lstar (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) :
    NL.Lsup ≤ P.Lstar := by
  obtain ⟨-, -, -, -, -, hbd, -⟩ := NL.props ha haJ
  exact csSup_le (img_nonempty NL) (by rintro _ ⟨y, hy, rfl⟩; exact (hbd y hy).2)

/-- `∫ max{1, u'₋(L - y)} dα ≤ 1 + C̄ - c_min ≤ 1 + σ - c_min` (`eq:bracket`). -/
private lemma limit_bound (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump)
    (hC : NL.Cbar ≤ P.σ) : ∫ p, Fc P.U NL.Lsup p.2 ∂NL.α ≤ 1 + P.σ - P.cmin := by
  have := NL.α_prob
  have hmeas : Measurable fun p : ℝ≥0∞ × ℝ => P.U.marg (NL.Lsup - p.2) :=
    (marg_antitone P.U).measurable.comp (measurable_const.sub measurable_snd)
  have hint : Integrable (fun p : ℝ≥0∞ × ℝ => P.U.marg (NL.Lsup - p.2)) NL.α :=
    Integrable.of_bound hmeas.aestronglyMeasurable P.U.c0 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_pos (marg_pos' _ _)]; exact marg_le_c0' _ _)
  have hFint : Integrable (fun p : ℝ≥0∞ × ℝ => Fc P.U NL.Lsup p.2) NL.α :=
    Integrable.of_bound ((Fc_mono P.U _).measurable.comp measurable_snd).aestronglyMeasurable
      P.U.c0 (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact abs_Fc_le P _ _)
  have hint1 : Integrable (fun p : ℝ≥0∞ × ℝ => 1 + P.U.marg (NL.Lsup - p.2)) NL.α :=
    (integrable_const 1).add hint
  have hL := L_le_Lstar NL ha haJ
  have hLC := P.Lstar_lt_Cstar
  calc ∫ p, Fc P.U NL.Lsup p.2 ∂NL.α
      ≤ ∫ p, (1 + P.U.marg (NL.Lsup - p.2) - P.cmin) ∂NL.α := by
        refine integral_mono_ae hFint (hint1.sub (integrable_const _)) ?_
        filter_upwards [ae_snd_nonneg NL] with p hp
        have hm : P.U.marg P.Cstar ≤ P.U.marg (NL.Lsup - p.2) :=
          marg_antitone P.U (by linarith)
        have hcmin1 : P.cmin ≤ 1 := P.cmin_le_one
        have hcmin2 : P.cmin ≤ P.U.marg P.Cstar := min_le_right _ _
        show max 1 (P.U.marg (NL.Lsup - p.2)) ≤ _
        rcases le_total 1 (P.U.marg (NL.Lsup - p.2)) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith
    _ = 1 + NL.Cbar - P.cmin := by
        rw [integral_sub hint1 (integrable_const _),
          integral_add (integrable_const 1) hint, integral_const, integral_const]
        simp [NormalizedLimit.Cbar]
    _ ≤ 1 + P.σ - P.cmin := by linarith

/-- Bounded convergence as `ε = 1/(m+1) ↓ 0`. -/
private lemma tendsto_Fc_integral (NL : NormalizedLimit S a) :
    Tendsto (fun m : ℕ => ∫ p, Fc P.U (NL.Lsup - 1 / ((m : ℝ) + 1)) p.2 ∂NL.α) atTop
      (𝓝 (∫ p, Fc P.U NL.Lsup p.2 ∂NL.α)) := by
  have := NL.α_prob
  refine tendsto_integral_of_dominated_convergence (fun _ => P.U.c0)
    (fun m => ((Fc_mono P.U _).measurable.comp measurable_snd).aestronglyMeasurable)
    (integrable_const _) (fun m => Eventually.of_forall fun p => ?_)
    (Eventually.of_forall fun p => tendsto_Fc P.U NL.Lsup p.2)
  rw [Real.norm_eq_abs]; exact abs_Fc_le P _ _

end NL

/-- `thm:wdf` (dyadic slope decay), eq. `eq:wdf`, in its sequential and its uniform form. -/
theorem NormalizedLimit.wdf {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation)
    (htight : NL.α {p | p.1 = ⊤} = 0) (hC : NL.Cbar ≤ P.σ) :
    ∃ εd > 0,
      (∀ k : ℕ → ℕ, Tendsto (fun n => (k n : ℝ) * NL.δ' n) atTop atTop →
        (∀ n, 2 * k n ≤ NL.Nn n) →
        ∀ᶠ n in atTop, εd < Real.log (NL.slope n (k n) / NL.slope n (2 * k n))) ∧
      ∃ Kd : ℝ, ∃ nd : ℕ, ∀ n ≥ nd, ∀ k : ℕ, Kd ≤ k * NL.δ' n → 2 * k ≤ NL.Nn n →
        εd < Real.log (NL.slope n k / NL.slope n (2 * k)) := by
  -- the choice of `ε_d`: `e^{ε_d}(1 + σ - c_min) < 1 + σ`
  have hσ := P.σ_pos
  have hcmin := P.cmin_pos
  have hcmin1 := P.cmin_le_one
  have hden : 0 < 1 + P.σ - P.cmin := by linarith
  set q := (1 + P.σ) / (1 + P.σ - P.cmin) with hq
  have hq1 : 1 < q := by rw [hq, one_lt_div hden]; linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  set εd := Real.log q / 2 with hεd
  have hεd0 : 0 < εd := by positivity
  have hexp : Real.exp εd * (1 + P.σ - P.cmin) < 1 + P.σ := by
    have : Real.exp εd < q := by
      calc Real.exp εd < Real.exp (Real.log q) := Real.exp_lt_exp.2 (by linarith)
        _ = q := Real.exp_log (by linarith)
    calc Real.exp εd * (1 + P.σ - P.cmin) < q * (1 + P.σ - P.cmin) :=
          mul_lt_mul_of_pos_right this hden
      _ = 1 + P.σ := by rw [hq]; field_simp
  have hE0 := Real.exp_pos εd
  -- the uniform formulation
  have hunif : ∃ Kd : ℝ, ∃ nd : ℕ, ∀ n ≥ nd, ∀ k : ℕ, Kd ≤ k * NL.δ' n → 2 * k ≤ NL.Nn n →
      εd < Real.log (NL.slope n k / NL.slope n (2 * k)) := by
    have hlim : Real.exp εd * ∫ p, Fc P.U NL.Lsup p.2 ∂NL.α < 1 + P.σ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (limit_bound NL ha haJ hC) hE0.le) hexp
    -- choose `ε = 1/(m+1)` with `e^{ε_d} ∫ F_ε dα < 1 + σ`
    obtain ⟨m, hm⟩ := (((tendsto_Fc_integral NL).const_mul (Real.exp εd)).eventually
      (gt_mem_nhds hlim)).exists
    set ε : ℝ := 1 / ((m : ℝ) + 1) with hε_def
    have hε : 0 < ε := by positivity
    set c := NL.Lsup - ε with hc_def
    set I := ∫ p, Fc P.U c p.2 ∂NL.α with hI_def
    set τ := ((1 + P.σ) - Real.exp εd * I) / (2 * Real.exp εd) with hτ_def
    have hτ : 0 < τ := div_pos (by linarith) (by positivity)
    have hτ' : Real.exp εd * (I + τ) < 1 + P.σ := by
      have e : Real.exp εd * (I + τ) = Real.exp εd * I + ((1 + P.σ) - Real.exp εd * I) / 2 := by
        rw [hτ_def]; field_simp
      rw [e]; linarith
    -- usc Portmanteau
    have hev1 := NL.α_conv.eventually_integral_le_of_usc (fun n => αn_isProb S a (NL.φ n))
      NL.α_prob (Fc_usc P.U c) (fun p => abs_Fc_le P c p.2) hτ
    -- `U_n = W_n(kδ_n) ≥ W_n(A) > L - ε`
    obtain ⟨_, ⟨A, hA, rfl⟩, hWA⟩ := exists_lt_of_lt_csSup (img_nonempty NL)
      (show c < NL.Lsup by linarith)
    have hA' : (0:ℝ) < A := hA
    have hev2 := (NL.W_conv.tendsto_at hA).eventually (lt_mem_nhds hWA)
    obtain ⟨nd, hnd⟩ := eventually_atTop.1 (hev1.and hev2)
    refine ⟨A, nd, fun n hn k hk h2k => ?_⟩
    obtain ⟨hI, hW⟩ := hnd n hn
    have hδ0 := δn_nonneg S a (NL.φ n)
    have hkδ : 0 < (k : ℝ) * NL.δ' n := hA'.trans_le hk
    have hδ : 0 < NL.δ' n := by
      rcases hδ0.eq_or_lt with h | h
      · exfalso; rw [NormalizedLimit.δ', ← h, mul_zero] at hkδ; exact lt_irrefl _ hkδ
      · exact h
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso; rw [h, Nat.cast_zero, zero_mul] at hkδ; exact lt_irrefl _ hkδ
      · exact h
    have he := scale_pos_of_δn_pos S a hδ
    have hN : 2 * k ≤ S.N (NL.φ n) := h2k
    have hVk : c ≤ S.V (NL.φ n) k := by
      have h1 := Wn_mono S a (NL.φ n) hk
      rw [NormalizedLimit.δ', Wn_grid S a he (by omega)] at h1
      exact hW.le.trans h1
    have hstrict := V_strict S (NL.φ n)
    have dpos : ∀ r, 1 ≤ r → r ≤ S.N (NL.φ n) → 0 < NL.slope n r := by
      intro r hr1 hrN
      have := hstrict (r - 1) (by omega)
      rw [Nat.sub_add_cancel hr1] at this
      exact div_pos (by linarith) hδ
    have hvk := dpos k hk1 (by omega)
    have hv2k := dpos (2 * k) (by omega) hN
    by_contra hcon
    push Not at hcon
    rw [Real.log_le_iff_le_exp (div_pos hvk hv2k), div_le_iff₀ hv2k] at hcon
    -- `v_k ≤ e^{ε_d} v_{2k}` in index form
    have hdk : S.V (NL.φ n) k - S.V (NL.φ n) (k - 1) ≤
        Real.exp εd * (S.V (NL.φ n) (2 * k) - S.V (NL.φ n) (2 * k - 1)) := by
      unfold NormalizedLimit.slope at hcon
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hδ] at hcon
      exact hcon
    have hcore := grid_core (S.isApproxEq (NL.φ n)) hstrict hk1 hN hVk hdk
    rw [← integral_αn S a (NL.φ n) (Fc_mono P.U c).measurable] at hcore
    have hβ : P.β * (1 + P.σ) = 1 := by rw [P.one_add_σ]; field_simp [P.β_pos.ne']
    have : P.β * Real.exp εd * ∫ p, Fc P.U c p.2 ∂S.αn a (NL.φ n) < 1 := by
      calc P.β * Real.exp εd * ∫ p, Fc P.U c p.2 ∂S.αn a (NL.φ n)
          ≤ P.β * (Real.exp εd * (I + τ)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI hE0.le) P.β_pos.le
        _ < P.β * (1 + P.σ) := mul_lt_mul_of_pos_left hτ' P.β_pos
        _ = 1 := hβ
    linarith
  obtain ⟨Kd, nd, hb⟩ := hunif
  refine ⟨εd, hεd0, fun k hk h2k => ?_, Kd, nd, hb⟩
  filter_upwards [eventually_ge_atTop nd, hk.eventually_ge_atTop Kd] with n hn hkn
  exact hb n hn (k n) hkn (h2k n)

end Molico
