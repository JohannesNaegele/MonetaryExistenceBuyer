import MonetaryExistenceBuyer.Limit.Defs
import MonetaryExistenceBuyer.Analysis.Interp
import MonetaryExistenceBuyer.Analysis.Helly
import MonetaryExistenceBuyer.Analysis.Weak
import MonetaryExistenceBuyer.Analysis.GridMeasure

/-!
# Properties of the Helly limit (`def:selected`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

namespace SelectedSeq

variable (S : SelectedSeq P)

/-- The interpolants `V_n` are nondecreasing and concave on `[0,∞)` with values in `[0, L_*]`. -/
private lemma Vn_facts :
    (∀ n, MonotoneOn (S.Vn n) (Ici 0)) ∧ (∀ n, ConcaveOn ℝ (Ici 0) (S.Vn n)) ∧
      (∀ n x, 0 ≤ S.Vn n x ∧ S.Vn n x ≤ P.Lstar) := by
  refine ⟨fun n => (interp_monotone (S.h_pos n) (S.isApproxEq n).cone.incr).monotoneOn _,
    fun n => interp_concaveOn (S.h_pos n) (S.isApproxEq n).cone.incr, fun n x => ?_⟩
  have h1 := interp_mem_Icc (S.h_pos n) (S.isApproxEq n).cone.incr x
  rw [(S.isApproxEq n).cone.zero] at h1
  exact ⟨h1.1, h1.2.trans (S.floor n).2⟩

/-- The truncation `x ↦ min (max x 0) K` as a bounded continuous function. -/
private def trunc (K : ℝ) (hK : 0 ≤ K) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (max x 0) K)
    ((continuous_id.max continuous_const).min continuous_const) K (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) hK)]
      exact min_le_right _ _)

private lemma trunc_apply (K : ℝ) (hK : 0 ≤ K) (x : ℝ) : trunc K hK x = min (max x 0) K := rfl

/-- `def:selected`: the Helly limit is nondecreasing and concave on `[0,∞)` with values in
`[0, L_*]`, and the limit law has mean at most `M` and lives on `ℝ₊`. -/
theorem limit_props :
    MonotoneOn S.Vlim (Ici 0) ∧ ConcaveOn ℝ (Ici 0) S.Vlim ∧
    (∀ x, 0 ≤ x → 0 ≤ S.Vlim x ∧ S.Vlim x ≤ P.Lstar) ∧
    S.ηlim (Iio 0) = 0 ∧ Integrable id S.ηlim ∧ ∫ x, x ∂S.ηlim ≤ P.M ∧
    S.νlim (Icc 0 P.Lstar)ᶜ = 0 := by
  obtain ⟨hmono, hconc, hbd⟩ := Vn_facts S
  obtain ⟨gmono, gconc, -, gbd, gscale⟩ :=
    concave_limit_props (f := S.Vn) hmono hconc (fun n x _ => hbd n x) S.V_conv
  -- bounds on `[0, ∞)`
  have hb : ∀ x, 0 ≤ x → 0 ≤ S.Vlim x ∧ S.Vlim x ≤ P.Lstar := by
    intro x hx
    rcases hx.lt_or_eq with hx | rfl
    · exact gbd x hx
    · rw [S.Vlim_zero]; exact ⟨le_rfl, P.Lstar_pos.le⟩
  -- monotonicity on `[0, ∞)`
  have hm : MonotoneOn S.Vlim (Ici 0) := by
    intro a ha b hb' hab
    rcases (show (0:ℝ) ≤ a from ha).lt_or_eq with ha' | rfl
    · exact gmono ha' (show (0:ℝ) < b from ha'.trans_le hab) hab
    · rw [S.Vlim_zero]; exact (hb b hb').1
  -- `t V(y) ≤ V(t y)` for `t ∈ [0,1]`, `y ≥ 0`
  have key : ∀ t y : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ y → t * S.Vlim y ≤ S.Vlim (t * y) := by
    intro t y ht0 ht1 hy
    rcases ht0.lt_or_eq with ht | rfl
    · rcases hy.lt_or_eq with hy | rfl
      · exact gscale y hy t ht ht1
      · simp [S.Vlim_zero]
    · simp [S.Vlim_zero]
  -- concavity on `[0, ∞)`
  have hc : ConcaveOn ℝ (Ici 0) S.Vlim := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb0 hab
    have hx' : (0:ℝ) ≤ x := hx
    have hy' : (0:ℝ) ≤ y := hy
    rcases hx'.lt_or_eq with hx0 | rfl
    · rcases hy'.lt_or_eq with hy0 | rfl
      · exact gconc.2 hx0 hy0 ha hb0 hab
      · simp only [smul_eq_mul, mul_zero, add_zero, S.Vlim_zero]
        exact key a x ha (by linarith) hx'
    · simp only [smul_eq_mul, mul_zero, zero_add, S.Vlim_zero]
      exact key b y hb0 (by linarith) hy'
  -- the laws
  have hprob : ∀ n, IsProbabilityMeasure (gridMeasure (S.h n) (S.N n) (S.η n)) :=
    fun n => gridMeasure_isProb (S.isApproxEq n).law
  have := S.ηlim_prob
  have hη0 : S.ηlim (Iio 0) = 0 := by
    refine le_antisymm (WeakConv.measure_open_le hprob S.ηlim_prob S.η_conv isOpen_Iio
      (Eventually.of_forall fun n => ?_)) zero_le
    refine (measure_mono_null ?_
      (gridMeasure_compl_Icc (S.h_pos n).le (S.isApproxEq n).law)).le
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and, not_le]
    intro h0
    exact absurd h0 (not_le.2 hx)
  have hnn : ∀ᵐ x ∂S.ηlim, 0 ≤ x := by
    rw [ae_iff]; simp only [not_le]; exact hη0
  -- truncated means
  have hM : ∀ k : ℕ, ∫ x, min (max x 0) (k : ℝ) ∂S.ηlim ≤ P.M := by
    intro k
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    refine le_of_tendsto' (S.η_conv (trunc k hk)) (fun n => ?_)
    rw [integral_gridMeasure (S.isApproxEq n).law.nonneg, ← (S.isApproxEq n).law.mean]
    refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_
      ((S.isApproxEq n).law.nonneg l)
    rw [trunc_apply]
    refine (min_le_left _ _).trans (le_of_eq (max_eq_left ?_))
    exact mul_nonneg (Nat.cast_nonneg l) (S.h_pos n).le
  have hsup : ∀ x : ℝ, ENNReal.ofReal x = ⨆ k : ℕ, ENNReal.ofReal (min (max x 0) k) := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · rw [ENNReal.ofReal_of_nonpos hx, max_eq_right hx]
      symm
      refine le_antisymm (iSup_le fun k => ?_) zero_le
      rw [min_eq_left (Nat.cast_nonneg k)]; simp
    · rw [max_eq_left hx.le]
      refine le_antisymm (le_iSup_of_le ⌈x⌉₊ ?_)
        (iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      rw [min_eq_left (Nat.le_ceil x)]
  have hlin : ∫⁻ x, ENNReal.ofReal x ∂S.ηlim ≤ ENNReal.ofReal P.M := by
    calc ∫⁻ x, ENNReal.ofReal x ∂S.ηlim
        = ∫⁻ x, ⨆ k : ℕ, ENNReal.ofReal (min (max x 0) k) ∂S.ηlim := lintegral_congr hsup
      _ = ⨆ k : ℕ, ∫⁻ x, ENNReal.ofReal (min (max x 0) k) ∂S.ηlim := by
          refine lintegral_iSup (fun k => ?_) (fun k k' hkk' x => ?_)
          · exact (ENNReal.continuous_ofReal.comp
              ((continuous_id.max continuous_const).min continuous_const)).measurable
          · exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hkk'))
      _ ≤ ENNReal.ofReal P.M := by
          refine iSup_le fun k => ?_
          have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
          have h1 := ofReal_integral_eq_lintegral_ofReal ((trunc k hk).integrable S.ηlim)
            (Eventually.of_forall fun x => le_min (le_max_right _ _) hk)
          simp only [trunc_apply] at h1
          rw [← h1]
          exact ENNReal.ofReal_le_ofReal (hM k)
  have hint : Integrable id S.ηlim :=
    ⟨measurable_id.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).2 (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  have hmean : ∫ x, x ∂S.ηlim ≤ P.M := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal P.M_pos.le hlin
  -- the value distributions
  have hνprob : ∀ n, IsProbabilityMeasure
      ((gridMeasure (S.h n) (S.N n) (S.η n)).map (interp (S.h n) (S.N n) (S.V n))) := fun n =>
    (Measure.isProbabilityMeasure_map_iff
      (continuous_interp (S.h_pos n)).measurable.aemeasurable).2 (hprob n)
  have hν : S.νlim (Icc 0 P.Lstar)ᶜ = 0 := by
    refine le_antisymm (WeakConv.measure_open_le hνprob S.νlim_prob S.ν_conv
      isClosed_Icc.isOpen_compl (Eventually.of_forall fun n => ?_)) zero_le
    rw [Measure.map_apply (continuous_interp (S.h_pos n)).measurable measurableSet_Icc.compl]
    have : interp (S.h n) (S.N n) (S.V n) ⁻¹' (Icc 0 P.Lstar)ᶜ = ∅ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_Icc, mem_empty_iff_false, iff_false, not_not]
      exact hbd n x
    rw [this, measure_empty]
  exact ⟨hm, hc, hb, hη0, hint, hmean, hν⟩

end SelectedSeq

end Molico
