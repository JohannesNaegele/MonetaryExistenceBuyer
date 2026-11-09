import MonetaryExistenceBuyer.Rescaling.Passage

/-!
# The Bellman identity at infinity (`lem:bellmaninfinity`)
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

/-- A step `t > 0` all of whose positive multiples are admissible buyer wealths. -/
private lemma exists_step (NL : NormalizedLimit S a) :
    ∃ t > 0, ∀ k : ℕ, 1 ≤ k → (k : ℝ) * t ∈ NL.Xplus := by
  by_cases hδ : NL.δ = 0
  · refine ⟨1, one_pos, fun k hk => ?_⟩
    simp only [Xplus, hδ, ite_true, mem_Ioi, mul_one]
    exact_mod_cast hk
  · refine ⟨NL.δ, delta_pos_of_ne NL hδ, fun k hk => ?_⟩
    simp only [Xplus, hδ, ite_false]
    exact ⟨k, hk, rfl⟩

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

private lemma obj_le (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {m : ℝ}
    {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW) (hfin : p.1 ≠ ⊤) {d : ℝ} (hd : d ∈ NL.A m) :
    P.U.u (NL.Wbar (p.1.toReal + d) - p.2) + NL.Wbar (m - d) ≤ P.U.ubar + NL.Wbar m := by
  obtain ⟨hz, hy, -⟩ := fin_state' NL ha haJ hp hfin
  obtain ⟨⟨hd0, hdm⟩, -⟩ := hd
  have h1 : p.2 ≤ NL.Wbar (p.1.toReal + d) :=
    hy.trans (wbar_mono NL ha haJ hz (by linarith))
  have h2 := P.U.le_ubar (sub_nonneg.2 h1)
  have h3 : NL.Wbar (m - d) ≤ NL.Wbar m := wbar_mono NL ha haJ (by linarith) (by linarith)
  linarith

private lemma obj_le_Hc (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump) {m : ℝ}
    {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW) (hfin : p.1 ≠ ⊤) {d : ℝ} (hd : d ∈ NL.A m) :
    P.U.u (NL.Wbar (p.1.toReal + d) - p.2) + NL.Wbar (m - d) ≤ NL.Hc m p := by
  rw [Hc, ite_eq_right hfin]
  refine le_csSup ⟨P.U.ubar + NL.Wbar m, ?_⟩ ⟨d, hd, rfl⟩
  rintro _ ⟨d', hd', rfl⟩
  exact obj_le NL ha haJ hp hfin hd'

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

/-- `W(x_k) → L` along any sequence `x_k → ∞` of positive wealths. -/
private lemma tendsto_W (NL : NormalizedLimit S a) (ha : 0 < a) (haJ : a < S.jump)
    {x : ℕ → ℝ} (hx : Tendsto x atTop atTop) (hpos : ∀ k, 0 < x k) :
    Tendsto (fun k => NL.W (x k)) atTop (𝓝 NL.Lsup) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb =>
    Eventually.of_forall fun k => (W_le_Lsup NL ha haJ (hpos k)).trans_lt hb⟩
  obtain ⟨_, ⟨x0, hx0, rfl⟩, hbx⟩ := exists_lt_of_lt_csSup (nonempty_Ioi.image _) hb
  filter_upwards [hx.eventually_ge_atTop x0] with k hk
  exact hbx.trans_le (W_mono NL ha haJ hx0 hk)

end NormalizedLimit

open NormalizedLimit in
/-- `lem:bellmaninfinity`, eq. `eq:bellmaninfinity`: `σ L = ∫_{z < ∞} u(L - y) dα`. -/
theorem NormalizedLimit.bellmanInfinity {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) :
    P.σ * NL.Lsup = ∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}, P.U.u (NL.Lsup - p.2) ∂NL.α := by
  have := NL.α_prob
  obtain ⟨t, ht, htX⟩ := exists_step NL
  set m : ℕ → ℝ := fun k => ((2 * (k + 1) : ℕ) : ℝ) * t with hm_def
  set c : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) * t with hc_def
  have hmX : ∀ k, m k ∈ NL.Xplus := fun k => htX _ (by omega)
  have hcX : ∀ k, c k ∈ NL.Xplus := fun k => htX _ (by omega)
  have hc0 : ∀ k, 0 < c k := fun k => xplus_pos NL (hcX k)
  have hmc : ∀ k, m k - c k = c k := by
    intro k
    simp only [hm_def, hc_def]
    push_cast
    ring
  have hcA : ∀ k, c k ∈ NL.A (m k) := fun k =>
    ⟨⟨(hc0 k).le, by linarith [hmc k, hc0 k]⟩, Or.inl (hcX k)⟩
  have hc_top : Tendsto c atTop atTop :=
    Tendsto.atTop_mul_const ht (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hm_top : Tendsto m atTop atTop :=
    tendsto_atTop_mono (fun k => by linarith [hmc k, hc0 k]) hc_top
  have hWm := tendsto_W NL ha haJ hm_top fun k => xplus_pos NL (hmX k)
  have hWc := tendsto_W NL ha haJ hc_top hc0
  -- the integrated Bellman excess converges to `σ L`
  have hlhs : Tendsto (fun k => ∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤},
      (NL.Hc (m k) p - NL.W (m k)) ∂NL.α) atTop (𝓝 (P.σ * NL.Lsup)) :=
    (hWm.const_mul P.σ).congr fun k => (setIntegral_excess NL ha haJ (hmX k)).symm
  -- dominated convergence on the finite states
  have hrhs : Tendsto (fun k => ∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤},
      (NL.Hc (m k) p - NL.W (m k)) ∂NL.α) atTop
      (𝓝 (∫ p in {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤}, P.U.u (NL.Lsup - p.2) ∂NL.α)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => P.U.ubar)
      (fun k => ((integrable_Hc NL ha haJ (hmX k)).sub (integrable_const _)).aestronglyMeasurable.restrict)
      (integrable_const _) (fun k => ?_) ?_
    · rw [ae_restrict_iff' measurableSet_fin]
      filter_upwards [ae_EW NL ha haJ] with p hp hfin
      obtain ⟨h1, h2⟩ := (NL.passage ha haJ).2.2.2 (m k) (hmX k) p hp hfin
      obtain ⟨-, -, hyL⟩ := fin_state' NL ha haJ hp hfin
      have := P.U.le_ubar (sub_nonneg.2 hyL)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    · rw [ae_restrict_iff' measurableSet_fin]
      filter_upwards [ae_EW NL ha haJ] with p hp hfin
      obtain ⟨hz, hy, hyL⟩ := fin_state' NL ha haJ hp hfin
      set z := p.1.toReal
      have hzc : ∀ k, 0 < z + c k := fun k => by linarith [hc0 k]
      have hWz := tendsto_W NL ha haJ (tendsto_atTop_add_const_left _ z hc_top) hzc
      -- the lower bound obtained from the transfer `c k`
      have hlow_le : ∀ k, P.U.u (NL.W (z + c k) - p.2) + NL.W (c k) - NL.W (m k) ≤
          NL.Hc (m k) p - NL.W (m k) := fun k => by
        have := obj_le_Hc NL ha haJ hp hfin (hcA k)
        rw [hmc k, wbar_of_pos NL (hzc k), wbar_of_pos NL (hc0 k)] at this
        linarith
      have hup : ∀ k, NL.Hc (m k) p - NL.W (m k) ≤ P.U.u (NL.Lsup - p.2) := fun k => by
        have := ((NL.passage ha haJ).2.2.2 (m k) (hmX k) p hp hfin).2
        linarith
      have hyW : ∀ k, p.2 ≤ NL.W (z + c k) := fun k => by
        have := wbar_mono NL ha haJ hz (show z ≤ z + c k by linarith [hc0 k])
        rw [wbar_of_pos NL (hzc k)] at this
        exact hy.trans this
      have harg : Tendsto (fun k => NL.W (z + c k) - p.2) atTop
          (𝓝[Ici 0] (NL.Lsup - p.2)) :=
        tendsto_nhdsWithin_iff.2 ⟨hWz.sub_const _,
          Eventually.of_forall fun k => sub_nonneg.2 (hyW k)⟩
      have hu : Tendsto (fun k => P.U.u (NL.W (z + c k) - p.2)) atTop
          (𝓝 (P.U.u (NL.Lsup - p.2))) :=
        ((P.U.continuousOn _ (sub_nonneg.2 hyL)).tendsto).comp harg
      have hlow : Tendsto (fun k => P.U.u (NL.W (z + c k) - p.2) + NL.W (c k) - NL.W (m k))
          atTop (𝓝 (P.U.u (NL.Lsup - p.2))) := by
        have := (hu.add hWc).sub hWm
        rwa [add_sub_cancel_right] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hlow_le hup
  exact tendsto_nhds_unique hlhs hrhs

end Molico
