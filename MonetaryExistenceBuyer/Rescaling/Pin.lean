import MonetaryExistenceBuyer.Rescaling.BellmanInfinity

/-!
# Finite-wealth saturation is immediate (`prop:pin`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

namespace NormalizedLimit

variable {S : SelectedSeq P} {a : ℝ}

private lemma wbar_of_pos (NL : NormalizedLimit S a) {x : ℝ} (hx : 0 < x) :
    NL.Wbar x = NL.W x :=
  ite_eq_right hx.ne'

private lemma delta_pos_of_ne (NL : NormalizedLimit S a) (hδ : NL.δ ≠ 0) : 0 < NL.δ := by
  rcases NL.lattice with h | h
  · exact absurd h.1 hδ
  · exact h.1

private lemma xplus_pos (NL : NormalizedLimit S a) {x : ℝ} (hx : x ∈ NL.Xplus) : 0 < x := by
  unfold Xplus at hx
  split_ifs at hx with hδ
  · exact hx
  · obtain ⟨k, hk, rfl⟩ := hx
    have : (1:ℝ) ≤ k := by exact_mod_cast hk
    exact mul_pos (by linarith) (delta_pos_of_ne NL hδ)

private lemma W_bounds (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {x : ℝ}
    (hx : 0 < x) : 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar :=
  (NL.props ha haJ).2.2.2.2.2.1 x hx

private lemma bddAbove_W (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) :
    BddAbove (NL.W '' Ioi 0) := by
  refine ⟨P.Lstar, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (W_bounds NL ha haJ hx).2

private lemma W_le_Lsup (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {x : ℝ}
    (hx : 0 < x) : NL.W x ≤ NL.Lsup :=
  le_csSup (bddAbove_W NL ha haJ) ⟨x, hx, rfl⟩

private lemma J'_le (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {x : ℝ}
    (hx : 0 < x) : NL.J' ≤ NL.W x := by
  refine csInf_le ⟨0, ?_⟩ ⟨x, hx, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (W_bounds NL ha haJ hy).1

private lemma wbar_mono (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : NL.Wbar x ≤ NL.Wbar y :=
  (NL.props ha haJ).2.2.2.1 (show x ∈ Ici (0:ℝ) from hx)
    (show y ∈ Ici (0:ℝ) from hx.trans hxy) hxy

private lemma W_mono (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : NL.W x ≤ NL.W y := by
  have := wbar_mono NL ha haJ hx.le hxy
  rwa [wbar_of_pos NL hx, wbar_of_pos NL (hx.trans_le hxy)] at this

private lemma wbar_le_Lsup (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {x : ℝ}
    (hx : 0 ≤ x) : NL.Wbar x ≤ NL.Lsup := by
  have := wbar_mono NL ha haJ hx (show x ≤ x + 1 by linarith)
  rw [wbar_of_pos NL (show 0 < x + 1 by linarith)] at this
  exact this.trans (W_le_Lsup NL ha haJ (show 0 < x + 1 by linarith))

/-- Finite compatible states: either `z = 0` and `0 ≤ y ≤ J'`, or `z > 0` and `y = W(z)`. -/
private lemma fin_state (NL : NormalizedLimit S a) {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW)
    (hfin : p.1 ≠ ⊤) :
    (p.1.toReal = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ NL.J') ∨ (0 < p.1.toReal ∧ p.2 = NL.W p.1.toReal) := by
  rcases hp with (⟨h1, h2⟩ | ⟨z, hz, rfl⟩) | ⟨h1, -⟩
  · left
    rw [mem_singleton_iff] at h1
    exact ⟨by simp [h1], h2.1, h2.2⟩
  · right
    have hz0 := xplus_pos NL hz
    exact ⟨by simpa [ENNReal.toReal_ofReal hz0.le] using hz0,
      by simp [ENNReal.toReal_ofReal hz0.le]⟩
  · exact absurd (mem_singleton_iff.1 h1) hfin

private lemma fin_state' (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump)
    {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW) (hfin : p.1 ≠ ⊤) :
    0 ≤ p.1.toReal ∧ p.2 ≤ NL.Wbar p.1.toReal ∧ p.2 ≤ NL.Lsup := by
  rcases fin_state NL hp hfin with ⟨h0, -, h2⟩ | ⟨h0, h1⟩
  · refine ⟨h0 ▸ le_rfl, ?_, ?_⟩
    · rw [h0]; simpa [Wbar] using h2
    · exact h2.trans ((J'_le NL ha haJ one_pos).trans (W_le_Lsup NL ha haJ one_pos))
  · refine ⟨h0.le, ?_, ?_⟩
    · rw [h1, wbar_of_pos NL h0]
    · rw [h1]; exact W_le_Lsup NL ha haJ h0

private lemma ae_EW (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) :
    ∀ᵐ p ∂NL.α, p ∈ NL.EW :=
  ae_iff.2 (NL.props ha haJ).2.2.2.2.2.2.2.1

private lemma measurableSet_fin : MeasurableSet {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤} :=
  measurable_fst (measurableSet_singleton ⊤).compl

private lemma integrable_Hc (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {m : ℝ}
    (hm : m ∈ NL.Xplus) : Integrable (NL.Hc m) NL.α := by
  have := NL.α_prob
  have hmeas : AEStronglyMeasurable (NL.Hc m) NL.α := by
    have := ((NL.passage ha haJ).2.1 m hm).aestronglyMeasurable (μ := NL.α)
      (NL.props ha haJ).2.2.2.2.2.2.1.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_EW NL ha haJ)] at this
  refine Integrable.of_bound hmeas (P.U.ubar + P.Lstar) ?_
  filter_upwards [ae_EW NL ha haJ] with p hp
  have hWm := W_bounds NL ha haJ (xplus_pos NL hm)
  have hub := P.U.ubar_pos
  by_cases hfin : p.1 = ⊤
  · rw [Hc, ite_eq_left hfin, Real.norm_eq_abs, abs_of_nonneg hWm.1]
    linarith
  · obtain ⟨h1, h2⟩ := (NL.passage ha haJ).2.2.2 m hm p hp hfin
    obtain ⟨-, -, hyL⟩ := fin_state' NL ha haJ hp hfin
    have := P.U.le_ubar (sub_nonneg.2 hyL)
    rw [Real.norm_eq_abs, abs_of_nonneg (hWm.1.trans h1)]
    linarith

/-- Integrated Bellman excess over the finite states: `∫_{z<∞} (ℋ(m;·) - W(m)) dα = σ W(m)`. -/
private lemma setIntegral_excess (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump)
    {m : ℝ} (hm : m ∈ NL.Xplus) :
    ∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}, (NL.Hc m p - NL.W m) ∂NL.α = P.σ * NL.W m := by
  have := NL.α_prob
  have hHc := integrable_Hc NL ha haJ hm
  have hint : Integrable (fun p => NL.Hc m p - NL.W m) NL.α := hHc.sub (integrable_const _)
  have h1 := integral_add_compl measurableSet_fin hint
  have h2 : ∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}ᶜ, (NL.Hc m p - NL.W m) ∂NL.α = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun p hp => ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_not] at hp
    rw [Hc, ite_eq_left hp, sub_self]
  have h3 : ∫ p, (NL.Hc m p - NL.W m) ∂NL.α = ∫ p, NL.Hc m p ∂NL.α - NL.W m := by
    rw [integral_sub hHc (integrable_const _)]
    simp
  have h4 := (NL.passage ha haJ).2.2.1 m hm
  rw [h2, add_zero, h3] at h1
  have hβ := P.β_pos
  have hσ : P.σ = 1 / P.β - 1 := rfl
  rw [h1, hσ, h4]
  field_simp

end NormalizedLimit

open NormalizedLimit in
/-- `prop:pin` (finite-wealth saturation is immediate), eq. `eq:pin`: a normalized limit with
finite-wealth saturation is non-lattice and `W(x) = L = J' = a` for `x > 0`. -/
theorem NormalizedLimit.pin {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hfp : NL.HasFiniteSaturation) :
    NL.δ = 0 ∧ (∀ x > 0, NL.W x = NL.Lsup) ∧ NL.Lsup = NL.J' ∧ NL.J' = a := by
  have := NL.α_prob
  obtain ⟨-, hW1a, hcont, -, -, -, -, -, -, hnl, hl⟩ := NL.props ha haJ
  have hL : 0 < NL.Lsup := ha.trans_le (hW1a.trans (W_le_Lsup NL ha haJ one_pos))
  -- Step 1: the plateau starts at the origin, `x_p = 0`.
  have hconst : ∀ x > 0, NL.W x = NL.Lsup := by
    by_contra hne
    push Not at hne
    obtain ⟨x0, hx0, hx0L⟩ := hne
    obtain ⟨xq, hxq, hWxq⟩ := hfp
    set T : Set ℝ := {x | 0 < x ∧ NL.W x = NL.Lsup} with hT
    have hTne : T.Nonempty := ⟨xq, hxq, hWxq⟩
    have hTbdd : BddBelow T := ⟨0, fun x hx => hx.1.le⟩
    -- the onset `x_p`
    set xp := sInf T with hxp_def
    have hlb : ∀ x ∈ T, x0 < x := by
      rintro x ⟨hx, hWx⟩
      by_contra h
      push Not at h
      have := W_mono NL ha haJ hx h
      exact hx0L (le_antisymm (W_le_Lsup NL ha haJ hx0) (by rw [← hWx]; exact this))
    have hxp_pos : 0 < xp := hx0.trans_le (le_csInf hTne fun x hx => (hlb x hx).le)
    have hbelow : ∀ x, 0 < x → x < xp → NL.W x < NL.Lsup := fun x hx hxxp =>
      lt_of_le_of_ne (W_le_Lsup NL ha haJ hx) fun h =>
        absurd (csInf_le hTbdd ⟨hx, h⟩) (not_le.2 hxxp)
    have habove : ∀ x, xp < x → NL.W x = NL.Lsup := by
      intro x hx
      obtain ⟨y, hyT, hyx⟩ := exists_lt_of_csInf_lt hTne hx
      refine le_antisymm (W_le_Lsup NL ha haJ (hyT.1.trans hyx)) ?_
      rw [← hyT.2]
      exact W_mono NL ha haJ hyT.1 hyx.le
    have hWxp : NL.W xp = NL.Lsup := by
      refine le_antisymm (W_le_Lsup NL ha haJ hxp_pos) ?_
      have hc : ContinuousWithinAt NL.Wbar (Ioi xp) xp :=
        (hcont xp (mem_Ici.2 hxp_pos.le)).mono (Ioi_subset_Ici hxp_pos.le)
      rw [← wbar_of_pos NL hxp_pos]
      refine ge_of_tendsto hc.tendsto ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [wbar_of_pos NL (hxp_pos.trans hx), habove x hx]
    -- the onset is an admissible buyer wealth
    have hxpX : xp ∈ NL.Xplus := by
      by_cases hδ : NL.δ = 0
      · simp only [Xplus, hδ, ite_true, mem_Ioi]
        exact hxp_pos
      · have hδpos := delta_pos_of_ne NL hδ
        simp only [Xplus, hδ, ite_false]
        have hcell := (hl hδpos).2
        set j := ⌊xp / NL.δ⌋₊ with hj
        have hj1 : (j : ℝ) * NL.δ ≤ xp := by
          have := Nat.floor_le (div_nonneg hxp_pos.le hδpos.le)
          rwa [le_div_iff₀ hδpos] at this
        have hj2 : xp < ((j : ℝ) + 1) * NL.δ := by
          have := Nat.lt_floor_add_one (xp / NL.δ)
          rwa [div_lt_iff₀ hδpos] at this
        rcases hj1.lt_or_eq with hlt | heq
        · exfalso
          have hj0 : (0 : ℝ) ≤ j * NL.δ := by positivity
          set x' := ((j : ℝ) * NL.δ + xp) / 2 with hx'
          have hx'pos : 0 < x' := by linarith
          have hx'lt : x' < xp := by linarith
          have hR : NL.Wbar (((j : ℝ) + 1) * NL.δ) = NL.Lsup := by
            rw [wbar_of_pos NL (by linarith), habove _ hj2]
          have e1 := hcell j xp ⟨hj1, hj2.le⟩
          have e2 := hcell j x' ⟨by linarith, by linarith⟩
          rw [hR, wbar_of_pos NL hxp_pos, hWxp] at e1
          rw [hR, wbar_of_pos NL hx'pos] at e2
          set A0 := NL.Wbar (j * NL.δ)
          have hs : (xp - j * NL.δ) / NL.δ < 1 := (div_lt_one hδpos).2 (by linarith)
          have hA0 : NL.Lsup - A0 = 0 := by
            have : (1 - (xp - j * NL.δ) / NL.δ) * (NL.Lsup - A0) = 0 := by
              linear_combination e1
            rcases mul_eq_zero.1 this with h | h
            · exfalso
              linarith
            · exact h
          have : NL.W x' = NL.Lsup := by
            rw [e2, hA0, mul_zero, add_zero]
            linarith
          exact (hbelow x' hx'pos hx'lt).ne this
        · refine ⟨j, ?_, heq.symm⟩
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · rw [h0] at heq
            simp at heq
            linarith
          · exact h0
    -- at a finite state below the onset the Bellman excess is strictly below `u(L - y)`
    have hstrict : ∀ p ∈ NL.EW, p.1 ≠ ⊤ → p.1.toReal < xp →
        NL.Hc xp p < P.U.u (NL.Lsup - p.2) + NL.Lsup := by
      intro p hp hfin hzxp
      obtain ⟨hz, hy, hyL⟩ := fin_state' NL ha haJ hp hfin
      set z := p.1.toReal
      set q := (xp + z) / 2 with hq
      have hq0 : 0 < q := by linarith
      have hzq : z ≤ q := by linarith
      have hqxp : q < xp := by linarith
      have hWq := hbelow q hq0 hqxp
      have hyq : p.2 ≤ NL.W q := by
        have := wbar_mono NL ha haJ hz hzq
        rw [wbar_of_pos NL hq0] at this
        exact hy.trans this
      have hu1 : P.U.u (NL.W q - p.2) < P.U.u (NL.Lsup - p.2) :=
        P.U.strictMonoOn (mem_Ici.2 (sub_nonneg.2 hyq)) (mem_Ici.2 (sub_nonneg.2 hyL))
          (by linarith)
      have h0A : (0 : ℝ) ∈ NL.A xp := ⟨⟨le_rfl, hxp_pos.le⟩, Or.inr rfl⟩
      have hbound : NL.Hc xp p ≤
          max (P.U.u (NL.W q - p.2) + NL.Lsup) (P.U.u (NL.Lsup - p.2) + NL.W q) := by
        rw [Hc, ite_eq_right hfin]
        refine csSup_le (Set.Nonempty.image _ ⟨0, h0A⟩) ?_
        rintro _ ⟨d, ⟨⟨hd0, hdm⟩, -⟩, rfl⟩
        have harg : p.2 ≤ NL.Wbar (z + d) := hy.trans (wbar_mono NL ha haJ hz (by linarith))
        rcases le_or_gt d (q - z) with hd | hd
        · refine le_max_of_le_left ?_
          have e1 : NL.Wbar (z + d) ≤ NL.W q := by
            have := wbar_mono NL ha haJ (by linarith) (show z + d ≤ q by linarith)
            rwa [wbar_of_pos NL hq0] at this
          have e2 : NL.Wbar (xp - d) ≤ NL.Lsup := wbar_le_Lsup NL ha haJ (by linarith)
          have e3 := P.U.monotoneOn (mem_Ici.2 (sub_nonneg.2 harg))
            (mem_Ici.2 (sub_nonneg.2 hyq)) (sub_le_sub_right e1 p.2)
          linarith
        · refine le_max_of_le_right ?_
          have e1 : NL.Wbar (z + d) ≤ NL.Lsup := wbar_le_Lsup NL ha haJ (by linarith)
          have e2 : NL.Wbar (xp - d) ≤ NL.W q := by
            have := wbar_mono NL ha haJ (by linarith) (show xp - d ≤ q by linarith)
            rwa [wbar_of_pos NL hq0] at this
          have e3 := P.U.monotoneOn (mem_Ici.2 (sub_nonneg.2 harg))
            (mem_Ici.2 (sub_nonneg.2 hyL)) (sub_le_sub_right e1 p.2)
          linarith
      exact hbound.trans_lt (max_lt (by linarith) (by linarith))
    -- integrate: the nonnegative gap `u(L - y) + L - ℋ(x_p; z, y)` has integral zero
    have hBI := NL.bellmanInfinity ha haJ
    have hEx := setIntegral_excess NL ha haJ hxpX
    rw [hWxp] at hEx
    have hσL : 0 < P.σ * NL.Lsup := mul_pos P.σ_pos hL
    have hIu : Integrable (fun p : ℝ≥0∞ × ℝ => P.U.u (NL.Lsup - p.2))
        (NL.α.restrict {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}) :=
      Integrable.of_integral_ne_zero (by rw [← hBI]; exact hσL.ne')
    have hIH : Integrable (fun p => NL.Hc xp p - NL.Lsup)
        (NL.α.restrict {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}) :=
      ((integrable_Hc NL ha haJ hxpX).sub (integrable_const _)).restrict
    have hF0 : ∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤},
        (P.U.u (NL.Lsup - p.2) - (NL.Hc xp p - NL.Lsup)) ∂NL.α = 0 := by
      rw [integral_sub hIu hIH, ← hBI, hEx, sub_self]
    have hFnn : 0 ≤ᵐ[NL.α.restrict {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}]
        fun p => P.U.u (NL.Lsup - p.2) - (NL.Hc xp p - NL.Lsup) := by
      have : ∀ᵐ p ∂NL.α.restrict {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤},
          0 ≤ P.U.u (NL.Lsup - p.2) - (NL.Hc xp p - NL.Lsup) := by
        rw [ae_restrict_iff' measurableSet_fin]
        filter_upwards [ae_EW NL ha haJ] with p hp hfin
        have := ((NL.passage ha haJ).2.2.2 xp hxpX p hp hfin).2
        rw [hWxp] at this
        linarith
      exact this
    have hFae := (integral_eq_zero_iff_of_nonneg_ae hFnn (hIu.sub hIH)).1 hF0
    have hEW : ∀ᵐ p ∂NL.α.restrict {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}, p ∈ NL.EW ∧ p.1 ≠ ⊤ := by
      rw [ae_restrict_iff' measurableSet_fin]
      filter_upwards [ae_EW NL ha haJ] with p hp hfin using ⟨hp, hfin⟩
    -- hence `u(L - y) = 0` at almost every finite state
    have hu0 : ∀ᵐ p ∂NL.α.restrict {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤},
        P.U.u (NL.Lsup - p.2) = 0 := by
      filter_upwards [hFae, hEW] with p hFp hpEW
      obtain ⟨hp, hfin⟩ := hpEW
      simp only [Pi.zero_apply] at hFp
      rcases lt_or_ge p.1.toReal xp with hz | hz
      · have := hstrict p hp hfin hz
        exfalso
        linarith
      · rcases fin_state NL hp hfin with ⟨h0, -, -⟩ | ⟨h0, h1⟩
        · exfalso
          linarith
        · have hWz : NL.W p.1.toReal = NL.Lsup := by
            rcases hz.lt_or_eq with h | h
            · exact habove _ h
            · rw [← h, hWxp]
          rw [h1, hWz, sub_self, P.U.u_zero]
    have hzero : ∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}, P.U.u (NL.Lsup - p.2) ∂NL.α = 0 := by
      rw [integral_congr_ae hu0]
      simp
    linarith
  -- Step 2: consequences of the constant profile.
  have hJ' : NL.J' = NL.Lsup := by
    have : NL.W '' Ioi 0 = {NL.Lsup} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hconst x hx
      · intro hy
        rw [mem_singleton_iff] at hy
        exact ⟨1, mem_Ioi.2 one_pos, by rw [hy]; exact hconst 1 one_pos⟩
    rw [J', this, csInf_singleton]
  have hδ : NL.δ = 0 := by
    by_contra hδ
    have := (hl (delta_pos_of_ne NL hδ)).1
    linarith
  refine ⟨hδ, hconst, hJ'.symm, ?_⟩
  rw [hJ', ← hconst 1 one_pos, (hnl hδ).1]

end Molico
