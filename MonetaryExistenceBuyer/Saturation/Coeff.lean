import MonetaryExistenceBuyer.Saturation.Count

/-!
# The coefficient bound (`lem:coeff`)

Proof outline (following the manuscript): with `w = L - W > 0` the deficit,
* Step 1 (`distance`, eq. `eq:distance`): `∫ u'₋(L - y) w(m + z) dα ≤ σ w(m)` for `m ∈ 𝒳₊`;
* Step 2 (`revwindow`, eq. `eq:revwindow`): `w(3m/4) ≤ C w(m)` for large `m ∈ 𝒳₊`;
* Step 3 (`ratio_bound`): concavity turns the reverse window into `w(m + z)/w(m) → 1`, and
  dominated convergence along `m_k → ∞` in `𝒳₊` gives `C̄ ≤ σ`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace Molico

variable {P : Primitives}

namespace NormalizedLimit

/-! ### Global bounds on the marginal utility -/

private lemma marg_le_c0' (U : AdmissibleUtility) (x : ℝ) : U.marg x ≤ U.c0 := by
  by_cases hx : x ≤ 0
  · simp [AdmissibleUtility.marg, hx]
  · exact U.marg_le_c0 (not_le.mp hx).le

private lemma marg_pos' (U : AdmissibleUtility) (x : ℝ) : 0 < U.marg x := by
  by_cases hx : x ≤ 0
  · have e : U.marg x = U.c0 := by simp [AdmissibleUtility.marg, hx]
    rw [e]; exact U.c0_pos
  · exact U.marg_pos (not_le.mp hx).le

private lemma marg_measurable (U : AdmissibleUtility) : Measurable U.marg := by
  refine Antitone.measurable fun x y hxy => ?_
  by_cases hx : x ≤ 0
  · have e : U.marg x = U.c0 := by simp [AdmissibleUtility.marg, hx]
    rw [e]; exact marg_le_c0' U y
  · have hx' : 0 ≤ x := (not_le.mp hx).le
    exact U.marg_antitoneOn hx' (hx'.trans hxy) hxy

variable {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)

/-! ### Elementary facts about the normalized limit -/

private lemma Wbar_of_pos {x : ℝ} (hx : 0 < x) : NL.Wbar x = NL.W x := by
  simp [Wbar, hx.ne']

private lemma W_le_L (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar) {x : ℝ} (hx : 0 < x) :
    NL.W x ≤ NL.Lsup :=
  le_csSup ⟨P.Lstar, by rintro _ ⟨y, hy, rfl⟩; exact (hW y hy).2⟩ ⟨x, hx, rfl⟩

private lemma L_le_Lstar (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar) :
    NL.Lsup ≤ P.Lstar :=
  csSup_le ⟨NL.W 1, 1, mem_Ioi.mpr one_pos, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact (hW y hy).2)

private lemma J'_le (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar) {x : ℝ} (hx : 0 < x) :
    NL.J' ≤ NL.W x :=
  csInf_le ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact (hW y hy).1⟩ ⟨x, hx, rfl⟩

private lemma Wbar_le_L (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar) {x : ℝ}
    (hx : 0 ≤ x) : NL.Wbar x ≤ NL.Lsup := by
  rcases hx.eq_or_lt with rfl | hx
  · have e : NL.Wbar 0 = NL.J' := by simp [Wbar]
    rw [e]; exact (J'_le NL hW one_pos).trans (W_le_L NL hW one_pos)
  · rw [Wbar_of_pos NL hx]; exact W_le_L NL hW hx

private lemma δ_pos_of_ne (hδ : NL.δ ≠ 0) : 0 < NL.δ := by
  rcases NL.lattice with ⟨h, _⟩ | ⟨h, _⟩
  · exact absurd h hδ
  · exact h

private lemma Xplus_pos {m : ℝ} (hm : m ∈ NL.Xplus) : 0 < m := by
  unfold Xplus at hm
  split_ifs at hm with hδ
  · exact hm
  · obtain ⟨k, hk, rfl⟩ := hm
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact mul_pos (by linarith) (δ_pos_of_ne NL hδ)

/-- A sequence of admissible buyer wealths tending to infinity. -/
private lemma exists_seq : ∃ m : ℕ → ℝ, (∀ k, m k ∈ NL.Xplus) ∧ Tendsto m atTop atTop := by
  by_cases hδ : NL.δ = 0
  · refine ⟨fun k => (k : ℝ) + 1, fun k => ?_, ?_⟩
    · simp only [Xplus, hδ, ↓reduceIte, mem_Ioi]; positivity
    · exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  · refine ⟨fun k => ((k + 1 : ℕ) : ℝ) * NL.δ, fun k => ?_, ?_⟩
    · simp only [Xplus, hδ, ↓reduceIte]; exact ⟨k + 1, by omega, rfl⟩
    · exact (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const
        (δ_pos_of_ne NL hδ)

/-- Finite compatible states: `0 ≤ y ≤ W̄(z)`. -/
private lemma finite_state (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar)
    {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW) (hfin : p.1 ≠ ⊤) :
    0 ≤ p.2 ∧ p.2 ≤ NL.Wbar p.1.toReal := by
  rcases hp with (⟨h1, h2⟩ | ⟨z, hz, rfl⟩) | ⟨h1, _⟩
  · have h1' : p.1 = 0 := h1
    have e : NL.Wbar p.1.toReal = NL.J' := by simp [h1', Wbar]
    rw [e]; exact h2
  · have hz0 : 0 < z := Xplus_pos NL hz
    simp only [ENNReal.toReal_ofReal hz0.le, Wbar_of_pos NL hz0]
    exact ⟨(hW z hz0).1, le_rfl⟩
  · exact absurd h1 hfin

/-- Almost every state is a finite compatible state. -/
private lemma fin_ae (hEWnull : NL.α NL.EWᶜ = 0) (htight : NL.α {p | p.1 = ⊤} = 0) :
    ∀ᵐ p ∂NL.α, p ∈ NL.EW ∧ p.1 ≠ ⊤ := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hEWnull,
    measure_eq_zero_iff_ae_notMem.1 htight] with p hp1 hp2
  exact ⟨by simpa using hp1, hp2⟩

/-- Bounding the finite-state payoff `ℋ(m; z, y)` by bounding every transfer. -/
private lemma Hc_le {m : ℝ} (hm : 0 ≤ m) {p : ℝ≥0∞ × ℝ} (hfin : p.1 ≠ ⊤) {B : ℝ}
    (hB : ∀ d, 0 ≤ d → d ≤ m →
      P.U.u (NL.Wbar (p.1.toReal + d) - p.2) + NL.Wbar (m - d) ≤ B) :
    NL.Hc m p ≤ B := by
  simp only [Hc, hfin, ↓reduceIte]
  have h0 : (0 : ℝ) ∈ NL.A m := ⟨⟨le_rfl, hm⟩, Or.inr (mem_singleton 0)⟩
  refine csSup_le ⟨_, 0, h0, rfl⟩ ?_
  rintro _ ⟨d, hd, rfl⟩
  exact hB d hd.1.1 hd.1.2

/-! ### Step 1: the deficit inequality -/

/-- Pointwise form of the deficit inequality:
`ℋ(m; z, y) ≤ u(L - y) - u'₋(L - y) w(z + m) + W(m)`. -/
private lemma deficit_pt (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar)
    (hmono : MonotoneOn NL.Wbar (Ici 0)) {m : ℝ} (hm : 0 < m) {p : ℝ≥0∞ × ℝ}
    (hp : p ∈ NL.EW) (hfin : p.1 ≠ ⊤) :
    NL.Hc m p ≤ P.U.u (NL.Lsup - p.2) -
      P.U.marg (NL.Lsup - p.2) * (NL.Lsup - NL.W (p.1.toReal + m)) + NL.W m := by
  obtain ⟨hy0, hyz⟩ := finite_state NL hW hp hfin
  have hz0 : 0 ≤ p.1.toReal := ENNReal.toReal_nonneg
  apply Hc_le NL hm.le hfin
  intro d hd0 hdm
  have h1 : p.2 ≤ NL.Wbar (p.1.toReal + d) :=
    hyz.trans (hmono (mem_Ici.mpr hz0) (mem_Ici.mpr (by linarith)) (by linarith))
  have h2 : NL.Wbar (p.1.toReal + d) ≤ NL.W (p.1.toReal + m) := by
    rw [← Wbar_of_pos NL (by linarith : 0 < p.1.toReal + m)]
    exact hmono (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (by linarith)
  have h3 : NL.W (p.1.toReal + m) ≤ NL.Lsup := W_le_L NL hW (by linarith)
  have h4 : NL.Wbar (m - d) ≤ NL.W m := by
    rw [← Wbar_of_pos NL hm]
    exact hmono (mem_Ici.mpr (by linarith)) (mem_Ici.mpr hm.le) (by linarith)
  have hsec := P.U.marg_mul_le_sub (sub_nonneg.mpr h1)
    (show NL.Wbar (p.1.toReal + d) - p.2 ≤ NL.Lsup - p.2 by linarith)
  have hmpos := marg_pos' P.U (NL.Lsup - p.2)
  have : P.U.marg (NL.Lsup - p.2) * (NL.Lsup - NL.W (p.1.toReal + m)) ≤
      P.U.marg (NL.Lsup - p.2) * (NL.Lsup - p.2 - (NL.Wbar (p.1.toReal + d) - p.2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hmpos.le
  linarith

/-- Measurability of `(z, y) ↦ W(z + m)` for `m > 0`. -/
private lemma measurable_W_shift (hcont : ContinuousOn NL.Wbar (Ici 0)) {m : ℝ} (hm : 0 < m) :
    Measurable fun p : ℝ≥0∞ × ℝ => NL.W (p.1.toReal + m) := by
  have hc : Continuous fun x : ℝ => NL.Wbar (max x 0) :=
    hcont.comp_continuous (continuous_id.max continuous_const) fun x => le_max_right x 0
  have e : (fun p : ℝ≥0∞ × ℝ => NL.W (p.1.toReal + m)) =
      fun p => NL.Wbar (max (p.1.toReal + m) 0) := by
    funext p
    have h : 0 < p.1.toReal + m := by
      have := ENNReal.toReal_nonneg (a := p.1); linarith
    rw [max_eq_left h.le, Wbar_of_pos NL h]
  rw [e]
  exact hc.measurable.comp ((ENNReal.measurable_toReal.comp measurable_fst).add_const m)

private lemma integrable_u (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar)
    (hfinae : ∀ᵐ p ∂NL.α, p ∈ NL.EW ∧ p.1 ≠ ⊤) :
    Integrable (fun p : ℝ≥0∞ × ℝ => P.U.u (NL.Lsup - p.2)) NL.α := by
  have : IsProbabilityMeasure NL.α := NL.α_prob
  have hc : Continuous fun p : ℝ≥0∞ × ℝ => P.U.u (max (NL.Lsup - p.2) 0) :=
    P.U.continuousOn.comp_continuous ((continuous_const.sub continuous_snd).max continuous_const)
      fun p => mem_Ici.mpr (le_max_right _ _)
  have hL0 : 0 ≤ NL.Lsup := (hW 1 one_pos).1.trans (W_le_L NL hW one_pos)
  have hyL : ∀ᵐ p ∂NL.α, 0 ≤ NL.Lsup - p.2 ∧ NL.Lsup - p.2 ≤ NL.Lsup := by
    filter_upwards [hfinae] with p hp
    obtain ⟨hy0, hyz⟩ := finite_state NL hW hp.1 hp.2
    have : p.2 ≤ NL.Lsup := hyz.trans (Wbar_le_L NL hW ENNReal.toReal_nonneg)
    exact ⟨by linarith, by linarith⟩
  refine Integrable.of_bound (hc.aestronglyMeasurable.congr ?_) (P.U.u NL.Lsup) ?_
  · filter_upwards [hyL] with p hp
    simp only [max_eq_left hp.1]
  · filter_upwards [hyL] with p hp
    have h1 := P.U.nonneg hp.1
    have h2 : P.U.u (NL.Lsup - p.2) ≤ P.U.u NL.Lsup := P.U.monotoneOn hp.1 hL0 hp.2
    rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact h2

private lemma integrable_prod (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar)
    (hcont : ContinuousOn NL.Wbar (Ici 0)) {m : ℝ} (hm : 0 < m) :
    Integrable (fun p : ℝ≥0∞ × ℝ =>
      P.U.marg (NL.Lsup - p.2) * (NL.Lsup - NL.W (p.1.toReal + m))) NL.α := by
  have : IsProbabilityMeasure NL.α := NL.α_prob
  refine Integrable.of_bound ((((marg_measurable P.U).comp
    (measurable_const.sub measurable_snd)).mul
    (measurable_const.sub (measurable_W_shift NL hcont hm))).aestronglyMeasurable)
    (P.U.c0 * NL.Lsup) (ae_of_all _ fun p => ?_)
  have hpos : 0 < p.1.toReal + m := by
    have := ENNReal.toReal_nonneg (a := p.1); linarith
  have h1 := (hW _ hpos).1
  have h2 := W_le_L NL hW hpos
  have h3 := marg_pos' P.U (NL.Lsup - p.2)
  have h4 := marg_le_c0' P.U (NL.Lsup - p.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3.le (by linarith))]
  exact mul_le_mul h4 (by linarith) (by linarith) P.U.c0_pos.le

/-- `σ L = ∫ u(L - y) dα` under tightness. -/
private lemma integral_u (ha : 0 < a) (haJ : a < S.jump)
    (hfinae : ∀ᵐ p ∂NL.α, p ∈ NL.EW ∧ p.1 ≠ ⊤) :
    ∫ p, P.U.u (NL.Lsup - p.2) ∂NL.α = P.σ * NL.Lsup := by
  have hs : ∀ᵐ p ∂NL.α, p ∈ {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤} := hfinae.mono fun p hp => hp.2
  rw [NL.bellmanInfinity ha haJ, Measure.restrict_eq_self_of_ae_mem hs]

private lemma β_mul_σ : P.β * P.σ = 1 - P.β := by
  rw [Primitives.σ, mul_sub, mul_one_div_cancel P.β_pos.ne', mul_one]

/-- Step 1, eq. `eq:distance`: `∫ u'₋(L - y) w(m + z) dα ≤ σ w(m)` for `m ∈ 𝒳₊`. -/
private lemma deficit (ha : 0 < a) (haJ : a < S.jump) (htight : NL.α {p | p.1 = ⊤} = 0)
    {m : ℝ} (hm : m ∈ NL.Xplus) :
    ∫ p, P.U.marg (NL.Lsup - p.2) * (NL.Lsup - NL.W (p.1.toReal + m)) ∂NL.α ≤
      P.σ * (NL.Lsup - NL.W m) := by
  have : IsProbabilityMeasure NL.α := NL.α_prob
  obtain ⟨-, -, hcont, hmono, -, hW, -, hEWnull, -, -, -⟩ := NL.props ha haJ
  obtain ⟨-, -, hbell, hbounds⟩ := NL.passage ha haJ
  have hm0 : 0 < m := Xplus_pos NL hm
  have hfinae := fin_ae NL hEWnull htight
  have hu := integrable_u NL hW hfinae
  have hpr := integrable_prod NL hW hcont hm0
  have hint_u := integral_u NL ha haJ hfinae
  set L := NL.Lsup
  have hint1 : Integrable (fun p : ℝ≥0∞ × ℝ =>
      P.U.u (L - p.2) - P.U.marg (L - p.2) * (L - NL.W (p.1.toReal + m))) NL.α := hu.sub hpr
  have hle : ∫ p, NL.Hc m p ∂NL.α ≤ ∫ p, (P.U.u (L - p.2) -
      P.U.marg (L - p.2) * (L - NL.W (p.1.toReal + m)) + NL.W m) ∂NL.α := by
    refine integral_mono_of_nonneg ?_ (hint1.add (integrable_const _)) ?_
    · filter_upwards [hfinae] with p hp
      exact ((hW m hm0).1).trans (hbounds m hm p hp.1 hp.2).1
    · filter_upwards [hfinae] with p hp
      exact deficit_pt NL hW hmono hm0 hp.1 hp.2
  rw [integral_add hint1 (integrable_const _), integral_sub hu hpr, integral_const,
    hint_u] at hle
  simp only [probReal_univ, one_smul] at hle
  generalize ∫ p, P.U.marg (L - p.2) * (L - NL.W (p.1.toReal + m)) ∂NL.α = I at hle ⊢
  have h1 : NL.W m ≤ P.β * (P.σ * L - I + NL.W m) :=
    calc NL.W m = P.β * ∫ p, NL.Hc m p ∂NL.α := hbell m hm
      _ ≤ _ := mul_le_mul_of_nonneg_left hle P.β_pos.le
  have e1 : P.β * (P.σ * L - I + NL.W m) = (1 - P.β) * L - P.β * I + P.β * NL.W m := by
    rw [← β_mul_σ]; ring
  have e2 : P.β * (P.σ * (L - NL.W m)) = (1 - P.β) * (L - NL.W m) := by
    rw [← β_mul_σ]; ring
  have h2 : P.β * I ≤ P.β * (P.σ * (L - NL.W m)) := by rw [e2]; linarith
  exact le_of_mul_le_mul_left h2 P.β_pos

/-! ### Step 2: the reverse window -/

/-- Pointwise form of the reverse window: for `z ≤ m/4`, one landing value is at most
`W(3m/4)`, so `ℋ(m; z, y) ≤ u(L - y) + L - c_min w(3m/4)`. -/
private lemma window_pt (hW : ∀ x, 0 < x → 0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar)
    (hmono : MonotoneOn NL.Wbar (Ici 0)) {m : ℝ} (hm : 0 < m) {p : ℝ≥0∞ × ℝ}
    (hp : p ∈ NL.EW) (hfin : p.1 ≠ ⊤) (hz : p.1.toReal ≤ m / 4) :
    NL.Hc m p ≤ P.U.u (NL.Lsup - p.2) + NL.Lsup - P.cmin * (NL.Lsup - NL.W (3 * m / 4)) := by
  obtain ⟨hy0, hyz⟩ := finite_state NL hW hp hfin
  have hz0 : 0 ≤ p.1.toReal := ENNReal.toReal_nonneg
  apply Hc_le NL hm.le hfin
  intro d hd0 hdm
  have hm34 : 0 < 3 * m / 4 := by positivity
  have hW34 := W_le_L NL hW hm34
  have hyL : p.2 ≤ NL.Lsup := hyz.trans (Wbar_le_L NL hW hz0)
  have hLy : 0 ≤ NL.Lsup - p.2 := by linarith
  have hcmin : P.cmin ≤ P.U.marg (NL.Lsup - p.2) := by
    have h1 : P.cmin ≤ P.U.marg P.Cstar := by unfold Primitives.cmin; exact min_le_right _ _
    refine h1.trans (P.U.marg_antitoneOn hLy P.Cstar_pos.le ?_)
    linarith [L_le_Lstar NL hW, P.Lstar_lt_Cstar]
  have h1 : p.2 ≤ NL.Wbar (p.1.toReal + d) :=
    hyz.trans (hmono (mem_Ici.mpr hz0) (mem_Ici.mpr (by linarith)) (by linarith))
  have hWzd : NL.Wbar (p.1.toReal + d) ≤ NL.Lsup := Wbar_le_L NL hW (by linarith)
  have hWmd : NL.Wbar (m - d) ≤ NL.Lsup := Wbar_le_L NL hW (by linarith)
  have hsec := P.U.marg_mul_le_sub (sub_nonneg.mpr h1)
    (show NL.Wbar (p.1.toReal + d) - p.2 ≤ NL.Lsup - p.2 by linarith)
  have hmpos := marg_pos' P.U (NL.Lsup - p.2)
  have hw0 : 0 ≤ NL.Lsup - NL.W (3 * m / 4) := by linarith
  rcases le_or_gt d (m / 2) with hd | hd
  · -- the seller lands at `z + d ≤ 3m/4`
    have h2 : NL.Wbar (p.1.toReal + d) ≤ NL.W (3 * m / 4) := by
      rw [← Wbar_of_pos NL hm34]
      exact hmono (mem_Ici.mpr (by linarith)) (mem_Ici.mpr hm34.le) (by linarith)
    have : P.cmin * (NL.Lsup - NL.W (3 * m / 4)) ≤
        P.U.marg (NL.Lsup - p.2) * (NL.Lsup - p.2 - (NL.Wbar (p.1.toReal + d) - p.2)) :=
      calc P.cmin * (NL.Lsup - NL.W (3 * m / 4))
          ≤ P.U.marg (NL.Lsup - p.2) * (NL.Lsup - NL.W (3 * m / 4)) :=
            mul_le_mul_of_nonneg_right hcmin hw0
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hmpos.le
    linarith
  · -- the buyer keeps `m - d < m/2 ≤ 3m/4`
    have h2 : NL.Wbar (m - d) ≤ NL.W (3 * m / 4) := by
      rw [← Wbar_of_pos NL hm34]
      exact hmono (mem_Ici.mpr (by linarith)) (mem_Ici.mpr hm34.le) (by linarith)
    have h3 : P.cmin * (NL.Lsup - NL.W (3 * m / 4)) ≤ NL.Lsup - NL.W (3 * m / 4) :=
      mul_le_of_le_one_left hw0 P.cmin_le_one
    have h4 : 0 ≤ P.U.marg (NL.Lsup - p.2) *
        (NL.Lsup - p.2 - (NL.Wbar (p.1.toReal + d) - p.2)) :=
      mul_nonneg hmpos.le (by linarith)
    linarith

/-- Step 2, eq. `eq:revwindow`: `w(3m/4) ≤ C w(m)` for all large `m ∈ 𝒳₊`. -/
private lemma revwindow (ha : 0 < a) (haJ : a < S.jump) (htight : NL.α {p | p.1 = ⊤} = 0) :
    ∃ K C : ℝ, ∀ m ∈ NL.Xplus, K ≤ m →
      NL.Lsup - NL.W (3 * m / 4) ≤ C * (NL.Lsup - NL.W m) := by
  have : IsProbabilityMeasure NL.α := NL.α_prob
  obtain ⟨-, -, -, hmono, -, hW, -, hEWnull, -, -, -⟩ := NL.props ha haJ
  obtain ⟨-, -, hbell, hbounds⟩ := NL.passage ha haJ
  have hfinae := fin_ae NL hEWnull htight
  have hu := integrable_u NL hW hfinae
  have hint_u := integral_u NL ha haJ hfinae
  -- a set of bounded wealths of positive mass
  obtain ⟨n, hn⟩ : ∃ n : ℕ, NL.α {p : ℝ≥0∞ × ℝ | p.1 ≤ (n : ℝ≥0∞)} ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    have hU : NL.α (⋃ n : ℕ, {p : ℝ≥0∞ × ℝ | p.1 ≤ (n : ℝ≥0∞)}) = 0 := measure_iUnion_null hcon
    have hsub : (univ : Set (ℝ≥0∞ × ℝ)) ⊆
        {p | p.1 = ⊤} ∪ ⋃ n : ℕ, {p : ℝ≥0∞ × ℝ | p.1 ≤ (n : ℝ≥0∞)} := by
      intro p _
      by_cases hp : p.1 = ⊤
      · exact Or.inl hp
      · obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hp
        exact Or.inr (mem_iUnion.mpr ⟨k, hk.le⟩)
    have h1 : NL.α univ ≤ 0 :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans (by rw [htight, hU, add_zero]))
    simp at h1
  set E := {p : ℝ≥0∞ × ℝ | p.1 ≤ (n : ℝ≥0∞)}
  have hEm : MeasurableSet E := measurable_fst measurableSet_Iic
  have haE : 0 < NL.α.real E := ENNReal.toReal_pos hn (measure_ne_top _ _)
  set L := NL.Lsup
  have hpos : 0 < P.β * NL.α.real E * P.cmin := by
    have := P.β_pos; have := P.cmin_pos; positivity
  refine ⟨4 * n, 1 / (P.β * NL.α.real E * P.cmin), fun m hm hmK => ?_⟩
  have hm0 : 0 < m := Xplus_pos NL hm
  set w34 := L - NL.W (3 * m / 4)
  have hc : Integrable (E.indicator fun _ => P.cmin * w34) NL.α :=
    (integrable_const _).indicator hEm
  have hint1 : Integrable (fun p : ℝ≥0∞ × ℝ => P.U.u (L - p.2) + L) NL.α :=
    hu.add (integrable_const _)
  have hle : ∫ p, NL.Hc m p ∂NL.α ≤
      ∫ p, (P.U.u (L - p.2) + L - E.indicator (fun _ => P.cmin * w34) p) ∂NL.α := by
    refine integral_mono_of_nonneg ?_ (hint1.sub hc) ?_
    · filter_upwards [hfinae] with p hp
      exact ((hW m hm0).1).trans (hbounds m hm p hp.1 hp.2).1
    · filter_upwards [hfinae] with p hp
      by_cases hpE : p ∈ E
      · rw [indicator_of_mem hpE]
        have hz : p.1.toReal ≤ m / 4 := by
          have h := ENNReal.toReal_mono (ENNReal.natCast_ne_top n) hpE
          rw [ENNReal.toReal_natCast] at h
          linarith
        exact window_pt NL hW hmono hm0 hp.1 hp.2 hz
      · rw [indicator_of_notMem hpE, sub_zero]
        have := (hbounds m hm p hp.1 hp.2).2
        have := W_le_L NL hW hm0
        linarith
  rw [integral_sub hint1 hc, integral_add hu (integrable_const _), integral_const,
    integral_indicator_const _ hEm, hint_u] at hle
  simp only [probReal_univ, smul_eq_mul, one_mul] at hle
  have h1 : NL.W m ≤ P.β * (P.σ * L + L - NL.α.real E * (P.cmin * w34)) := by
    rw [hbell m hm]; exact mul_le_mul_of_nonneg_left hle P.β_pos.le
  have hβσ : P.β * P.σ * L = (1 - P.β) * L := by rw [β_mul_σ]
  have e1 : P.β * (P.σ * L + L - NL.α.real E * (P.cmin * w34)) =
      L - P.β * NL.α.real E * P.cmin * w34 := by
    linear_combination hβσ
  rw [one_div_mul_eq_div, le_div_iff₀ hpos]
  calc w34 * (P.β * NL.α.real E * P.cmin) = P.β * NL.α.real E * P.cmin * w34 := by ring
    _ ≤ L - NL.W m := by linarith

/-! ### Step 3: the ratio limit -/

/-- Concavity plus the reverse window:
`W(m + z) - W(m) ≤ (4z/m) C w(m)`. -/
private lemma ratio_bound (hconc : ConcaveOn ℝ (Ici 0) NL.Wbar) {C m z : ℝ} (hm : 0 < m)
    (hz : 0 ≤ z) (hw : 0 ≤ NL.Lsup - NL.W m)
    (hwin : NL.Lsup - NL.W (3 * m / 4) ≤ C * (NL.Lsup - NL.W m)) :
    NL.W (m + z) - NL.W m ≤ 4 * z / m * C * (NL.Lsup - NL.W m) := by
  rcases hz.eq_or_lt with rfl | hz
  · simp
  have hm34 : 0 < 3 * m / 4 := by positivity
  have hs := hconc.slope_anti_adjacent (x := 3 * m / 4) (y := m) (z := m + z)
    (mem_Ici.mpr hm34.le) (mem_Ici.mpr (by linarith)) (by linarith) (by linarith)
  rw [Wbar_of_pos NL hm34, Wbar_of_pos NL hm, Wbar_of_pos NL (by linarith : 0 < m + z),
    div_le_div_iff₀ (by linarith) (by linarith)] at hs
  have hb : NL.W m - NL.W (3 * m / 4) ≤ C * (NL.Lsup - NL.W m) := by linarith
  rw [show 4 * z / m * C * (NL.Lsup - NL.W m) = 4 * z * (C * (NL.Lsup - NL.W m)) / m by ring,
    le_div_iff₀ hm]
  have := mul_le_mul_of_nonneg_left hb hz.le
  nlinarith

end NormalizedLimit

open NormalizedLimit in
/-- `lem:coeff`: a tight normalized limit with asymptotic saturation has
`C̄ ≤ σ`. -/
theorem NormalizedLimit.coeff {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation)
    (htight : NL.α {p | p.1 = ⊤} = 0) : NL.Cbar ≤ P.σ := by
  have : IsProbabilityMeasure NL.α := NL.α_prob
  obtain ⟨-, -, hcont, hmono, hconc, hW, -, -, -, -, -⟩ := NL.props ha haJ
  obtain ⟨K, C, hwin⟩ := revwindow NL ha haJ htight
  obtain ⟨ms, hmsX, hms⟩ := exists_seq NL
  set L := NL.Lsup
  have hwpos : ∀ x, 0 < x → 0 < L - NL.W x := by
    intro x hx
    have h1 := W_le_L NL hW hx
    have h2 : NL.W x ≠ L := fun h => hnp ⟨x, hx, h⟩
    exact sub_pos.mpr (lt_of_le_of_ne h1 h2)
  have hWmono : ∀ x y, 0 < x → x ≤ y → NL.W x ≤ NL.W y := by
    intro x y hx hxy
    rw [← Wbar_of_pos NL hx, ← Wbar_of_pos NL (hx.trans_le hxy)]
    exact hmono (mem_Ici.mpr hx.le) (mem_Ici.mpr (hx.le.trans hxy)) hxy
  have hF_int : ∀ k, ∫ p, P.U.marg (L - p.2) * (L - NL.W (p.1.toReal + ms k)) /
      (L - NL.W (ms k)) ∂NL.α ≤ P.σ := by
    intro k
    have hmk := Xplus_pos NL (hmsX k)
    rw [integral_div, div_le_iff₀ (hwpos _ hmk)]
    exact deficit NL ha haJ htight (hmsX k)
  have hlim : Tendsto (fun k => ∫ p, P.U.marg (L - p.2) * (L - NL.W (p.1.toReal + ms k)) /
      (L - NL.W (ms k)) ∂NL.α) atTop (𝓝 (∫ p, P.U.marg (L - p.2) ∂NL.α)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => P.U.c0) (fun k => ?_)
      (integrable_const _) (fun k => ae_of_all _ fun p => ?_) (ae_of_all _ fun p => ?_)
    · exact ((((marg_measurable P.U).comp (measurable_const.sub measurable_snd)).mul
        (measurable_const.sub (measurable_W_shift NL hcont (Xplus_pos NL (hmsX k))))).div_const
          _).aestronglyMeasurable
    · have hmk := Xplus_pos NL (hmsX k)
      have hz := ENNReal.toReal_nonneg (a := p.1)
      have h1 := hWmono _ _ hmk (by linarith : ms k ≤ p.1.toReal + ms k)
      have h2 := W_le_L NL hW (by linarith : 0 < p.1.toReal + ms k)
      have h3 := marg_pos' P.U (L - p.2)
      have h4 := marg_le_c0' P.U (L - p.2)
      have h5 := hwpos _ hmk
      have hr0 : 0 ≤ (L - NL.W (p.1.toReal + ms k)) / (L - NL.W (ms k)) :=
        div_nonneg (by linarith) h5.le
      have hr1 : (L - NL.W (p.1.toReal + ms k)) / (L - NL.W (ms k)) ≤ 1 :=
        (div_le_one h5).mpr (by linarith)
      rw [mul_div_assoc, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3.le hr0)]
      calc _ ≤ P.U.c0 * 1 := mul_le_mul h4 hr1 hr0 P.U.c0_pos.le
        _ = P.U.c0 := mul_one _
    · have hz := ENNReal.toReal_nonneg (a := p.1)
      have hr : Tendsto (fun k => (L - NL.W (p.1.toReal + ms k)) / (L - NL.W (ms k))) atTop
          (𝓝 1) := by
        have h0 : Tendsto (fun k => 4 * p.1.toReal / ms k) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hms
        have hlow : Tendsto (fun k => 1 - 4 * p.1.toReal / ms k * C) atTop (𝓝 1) := by
          have := (tendsto_const_nhds (x := (1 : ℝ))).sub (h0.mul_const C)
          rwa [zero_mul, sub_zero] at this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
        · filter_upwards [hms.eventually_ge_atTop K] with k hk
          have hmk := Xplus_pos NL (hmsX k)
          have h5 := hwpos _ hmk
          have hb := ratio_bound NL hconc hmk hz h5.le (hwin (ms k) (hmsX k) hk)
          rw [le_div_iff₀ h5, add_comm p.1.toReal (ms k)]
          nlinarith
        · filter_upwards with k
          have hmk := Xplus_pos NL (hmsX k)
          have h5 := hwpos _ hmk
          have h1 := hWmono _ _ hmk (by linarith : ms k ≤ p.1.toReal + ms k)
          exact (div_le_one h5).mpr (by linarith)
      have := (tendsto_const_nhds (x := P.U.marg (L - p.2))).mul hr
      rw [mul_one] at this
      refine this.congr fun k => ?_
      rw [mul_div_assoc]
  show ∫ p, P.U.marg (L - p.2) ∂NL.α ≤ P.σ
  exact le_of_tendsto' hlim hF_int

end Molico
