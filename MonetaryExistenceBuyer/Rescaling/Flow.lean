import MonetaryExistenceBuyer.Rescaling.NonEscape

/-!
# Limiting meeting measure and stationarity (`lem:flowpassage`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

/-- Weak convergence passes to equal-weight mixtures `c • μ_n + c • ν_n` (integrals are linear
in the measure). -/
private lemma weakConv_mix {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μs νs : ℕ → Measure X} {μ ν : Measure X}
    (hμs : ∀ n, IsFiniteMeasure (μs n)) (hνs : ∀ n, IsFiniteMeasure (νs n))
    (hμ : IsFiniteMeasure μ) (hν : IsFiniteMeasure ν)
    (h1 : WeakConv μs μ) (h2 : WeakConv νs ν) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    WeakConv (fun n => c • μs n + c • νs n) (c • μ + c • ν) := by
  intro f
  have key : ∀ (m k : Measure X), IsFiniteMeasure m → IsFiniteMeasure k →
      ∫ x, f x ∂(c • m + c • k) = c.toReal • ∫ x, f x ∂m + c.toReal • ∫ x, f x ∂k := by
    intro m k hm hk
    rw [integral_add_measure ((f.integrable m).smul_measure hc) ((f.integrable k).smul_measure hc),
      integral_smul_measure, integral_smul_measure]
  simp only [key _ _ (hμs _) (hνs _), key μ ν hμ hν]
  exact ((h1 f).const_smul _).add ((h2 f).const_smul _)

/-- The prelimit meeting geometry `eq:meetgeom` for one charged triple `(b, s, d) = (x, y, w)`
with `0 ≤ d ≤ b`, `0 ≤ s`, after normalization by `e ≥ 0`. -/
private lemma meetgeom_point {x y w e : ℝ} (hw : 0 ≤ w) (hwx : w ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) :
    ENNReal.ofReal (w / e) ≤ ENNReal.ofReal (x / e) ∧
    ENNReal.ofReal ((x - w) / e) ≤ ENNReal.ofReal (x / e) ∧
    ENNReal.ofReal (y / e) ≤ ENNReal.ofReal ((y + w) / e) ∧
    ENNReal.ofReal ((x - w) / e) + ENNReal.ofReal ((y + w) / e) =
      ENNReal.ofReal (x / e) + ENNReal.ofReal (y / e) := by
  have hx : 0 ≤ x := hw.trans hwx
  refine ⟨ENNReal.ofReal_le_ofReal (by gcongr), ENNReal.ofReal_le_ofReal (by gcongr; linarith),
    ENNReal.ofReal_le_ofReal (by gcongr; linarith), ?_⟩
  rw [← ENNReal.ofReal_add (div_nonneg (by linarith) he) (div_nonneg (by linarith) he),
    ← ENNReal.ofReal_add (div_nonneg hx he) (div_nonneg hy he)]
  congr 1
  ring

/-- `lem:flowpassage`, eqs. `eq:normalizedstationarity`, `eq:meetgeom`. Coordinates of `[0,∞]⁵`
are `(b, z, d̂, B, S)`. -/
theorem NormalizedLimit.flowpassage {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) :
    NL.Γh.map (fun q => (q.1, q.2.1)) = NL.αw.prod NL.αw ∧
    NL.αw = (2⁻¹ : ℝ≥0∞) • NL.Γh.map (fun q => q.2.2.2.1) +
      (2⁻¹ : ℝ≥0∞) • NL.Γh.map (fun q => q.2.2.2.2) ∧
    ∀ᵐ q ∂NL.Γh, q.2.2.1 ≤ q.1 ∧ q.2.2.2.1 ≤ q.1 ∧ q.2.1 ≤ q.2.2.2.2 ∧
      q.2.2.2.1 + q.2.2.2.2 = q.1 + q.2.1 := by
  classical
  -- the normalization `g_n(s) = s / e_n` and the normalized meeting map `T_n`
  set e : ℕ → ℝ := fun n => S.scale a (NL.φ n) with he_def
  have he0 : ∀ n, 0 ≤ e n := fun n => mul_nonneg (S.h_pos _).le (Nat.cast_nonneg _)
  set g : ℕ → ℝ → ℝ≥0∞ := fun n s => ENNReal.ofReal (s / e n) with hg_def
  have hg : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_id.div_const _)
  set T : ℕ → ℝ × ℝ × ℝ → ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ := fun n p =>
    (g n p.1, g n p.2.1, g n p.2.2, g n (postB p), g n (postS p)) with hT_def
  have hT : ∀ n, Measurable (T n) := fun n => by
    simp only [hT_def, postB, postS]
    exact ((hg n).comp measurable_fst).prodMk (((hg n).comp (measurable_fst.comp measurable_snd)).prodMk
      (((hg n).comp (measurable_snd.comp measurable_snd)).prodMk
        (((hg n).comp (measurable_fst.sub (measurable_snd.comp measurable_snd))).prodMk
          ((hg n).comp ((measurable_fst.comp measurable_snd).add
            (measurable_snd.comp measurable_snd))))))
  have hΓhat : ∀ n, S.Γhat a (NL.φ n) = (S.Γn (NL.φ n)).map (T n) := fun n => rfl
  -- probability measures
  have hΓprob : ∀ n, IsProbabilityMeasure (S.Γn n) := fun n =>
    gridMeeting_isProb (S.h_pos n) (S.isApproxEq n)
  have hηprob : ∀ n, IsProbabilityMeasure (S.ηn n) := fun n =>
    gridMeasure_isProb (S.isApproxEq n).law
  have hΓhprob : ∀ n, IsProbabilityMeasure (S.Γhat a (NL.φ n)) := fun n => by
    rw [hΓhat]; have := hΓprob (NL.φ n); infer_instance
  have hιm : ∀ n, Measurable (S.ι a n) := fun n =>
    (ENNReal.measurable_ofReal.comp (measurable_id.div_const _)).prodMk
      (continuous_interp (S.h_pos n)).measurable
  have hαprob : ∀ n, IsProbabilityMeasure (S.αn a (NL.φ n)) := fun n => by
    have := hηprob (NL.φ n); unfold SelectedSeq.αn; infer_instance
  have hwprob : ∀ n, IsProbabilityMeasure ((S.ηn (NL.φ n)).map (g n)) := fun n => by
    have := hηprob (NL.φ n); infer_instance
  have := NL.α_prob
  have := NL.Γh_prob
  have hαwprob : IsProbabilityMeasure NL.αw := by unfold NormalizedLimit.αw; infer_instance
  -- wealth marginals of `α_n`
  have hαfst : ∀ n, (S.αn a (NL.φ n)).map Prod.fst = (S.ηn (NL.φ n)).map (g n) := by
    intro n
    rw [SelectedSeq.αn, Measure.map_map measurable_fst (hιm _)]
    rfl
  have hαw_conv : WeakConv (fun n => (S.ηn (NL.φ n)).map (g n)) NL.αw := by
    have h := NL.α_conv.map hαprob NL.α_prob continuous_fst
    simp only [hαfst] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · -- `(b, z)_# Γ̂ = α^w ⊗ α^w`
    have h1 : ∀ n, (S.Γhat a (NL.φ n)).map (fun q => (q.1, q.2.1)) =
        ((S.ηn (NL.φ n)).map (g n)).prod ((S.ηn (NL.φ n)).map (g n)) := by
      intro n
      rw [hΓhat, Measure.map_map (by fun_prop) (hT n)]
      have : (fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => (q.1, q.2.1)) ∘ T n =
          Prod.map (g n) (g n) ∘ pairBS := rfl
      rw [this, ← Measure.map_map ((hg n).prodMap (hg n)) (by unfold pairBS; fun_prop),
        SelectedSeq.Γn, gridMeeting_marginal (S.h_pos _) (S.isApproxEq _),
        Measure.map_prod_map _ _ (hg n) (hg n)]
      rfl
    have hc1 := NL.Γh_conv.map hΓhprob NL.Γh_prob
      (f := fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => (q.1, q.2.1)) (by fun_prop)
    have hc2 := hαw_conv.prod hwprob hαwprob hwprob hαwprob hαw_conv
    simp only [h1] at hc1
    have hpp : ∀ n, IsProbabilityMeasure
        (((S.ηn (NL.φ n)).map (g n)).prod ((S.ηn (NL.φ n)).map (g n))) := fun n => by
      have := hwprob n; infer_instance
    exact WeakConv.unique hpp inferInstance inferInstance hc1 hc2
  · -- `α^w = ½ B_# Γ̂ + ½ S_# Γ̂`
    have h1 : ∀ n, (S.ηn (NL.φ n)).map (g n) =
        (2⁻¹ : ℝ≥0∞) • (S.Γhat a (NL.φ n)).map (fun q => q.2.2.2.1) +
        (2⁻¹ : ℝ≥0∞) • (S.Γhat a (NL.φ n)).map (fun q => q.2.2.2.2) := by
      intro n
      rw [hΓhat, Measure.map_map (by fun_prop) (hT n), Measure.map_map (by fun_prop) (hT n),
        SelectedSeq.ηn, gridMeeting_stationary (S.h_pos _) (S.isApproxEq _),
        Measure.map_add _ _ (hg n), Measure.map_smul _ (hg n).aemeasurable,
        Measure.map_smul _ (hg n).aemeasurable,
        Measure.map_map (hg n) (by unfold postB; fun_prop),
        Measure.map_map (hg n) (by unfold postS; fun_prop)]
      rfl
    have hB := NL.Γh_conv.map hΓhprob NL.Γh_prob
      (f := fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.2.2.1) (by fun_prop)
    have hS := NL.Γh_conv.map hΓhprob NL.Γh_prob
      (f := fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.2.2.2) (by fun_prop)
    have hmix := weakConv_mix (fun n => inferInstance) (fun n => inferInstance) inferInstance
      inferInstance hB hS (c := (2⁻¹ : ℝ≥0∞)) (by simp)
    simp only [← h1] at hmix
    have hmixprob : IsProbabilityMeasure ((2⁻¹ : ℝ≥0∞) • NL.Γh.map (fun q => q.2.2.2.1) +
        (2⁻¹ : ℝ≥0∞) • NL.Γh.map (fun q => q.2.2.2.2)) := by
      constructor
      rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ]
      simp [ENNReal.inv_two_add_inv_two]
    exact WeakConv.unique hwprob hαwprob hmixprob hαw_conv hmix
  · -- `eq:meetgeom` via the closed-set Portmanteau inequality
    set C : Set (ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞) := {q | q.2.2.1 ≤ q.1 ∧ q.2.2.2.1 ≤ q.1 ∧
      q.2.1 ≤ q.2.2.2.2 ∧ q.2.2.2.1 + q.2.2.2.2 = q.1 + q.2.1} with hC_def
    have c1 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.1 := by fun_prop
    have c2 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.1 := by fun_prop
    have c3 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.2.1 := by fun_prop
    have c4 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.2.2.1 := by fun_prop
    have c5 : Continuous fun q : ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ => q.2.2.2.2 := by fun_prop
    have hC : IsClosed C :=
      (isClosed_le c3 c1).inter ((isClosed_le c4 c1).inter ((isClosed_le c2 c5).inter
        (isClosed_eq (c4.add c5) (c1.add c2))))
    have hn : ∀ n, S.Γhat a (NL.φ n) C = 1 := by
      intro n
      rw [hΓhat, Measure.map_apply (hT n) hC.measurableSet]
      have hae : ∀ᵐ p ∂S.Γn (NL.φ n), T n p ∈ C := by
        filter_upwards [ae_gridMeeting (S.isApproxEq (NL.φ n))] with p hp
        obtain ⟨m, l, j, hm, hl, hj, -, -, -, -, rfl⟩ := hp
        have hjm := ((Grid.mem_feas hm hl).1 hj).1
        have hh := (S.h_pos (NL.φ n)).le
        exact meetgeom_point (mul_nonneg (Nat.cast_nonneg _) hh)
          (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hjm) hh) (mul_nonneg (Nat.cast_nonneg _) hh)
          (he0 n)
      exact (prob_compl_eq_zero_iff ((hT n) hC.measurableSet)).1 (ae_iff.1 hae)
    have hlim : 1 ≤ NL.Γh C :=
      WeakConv.le_measure_closed hΓhprob NL.Γh_prob NL.Γh_conv hC
        (Eventually.of_forall fun n => (hn n).ge)
    have hC1 : NL.Γh Cᶜ = 0 :=
      (prob_compl_eq_zero_iff hC.measurableSet).2 (le_antisymm prob_le_one hlim)
    exact ae_iff.2 hC1

end Molico
