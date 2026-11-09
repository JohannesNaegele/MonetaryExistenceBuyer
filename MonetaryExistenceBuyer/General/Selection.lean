import MonetaryExistenceBuyer.Model
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable maximisers of the buyer problem

For a continuous increasing utility `u` and an admissible value function `V`, the value
`H_V(b,s)` of `def:bellman` is measurable in `(b, s)`, and a maximiser `d ∈ [0, b]` can be chosen
measurably (`rem:physicaloutput`: "such a choice exists because the objective is continuous and
the feasible transfer interval is compact"). Since `V` and `u` are only controlled on `[0, ∞)`,
the measurability statement clamps the arguments to `[0, ∞)`.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace Molico

variable {u V : ℝ → ℝ}

/-! ### The clamped objective

For `t ∈ [0,1]` and `b, s ≥ 0`, `clampF u V (b, s) t = obj u V b s (t * b)`; the clamping makes
`clampF` jointly continuous on all of `(ℝ × ℝ) × ℝ`. -/

/-- The buyer objective in the normalised transfer variable `t` (`d = t b⁺`), with all arguments
of `u` and `V` clamped to `[0, ∞)`. -/
private def clampF (u V : ℝ → ℝ) (q : ℝ × ℝ) (t : ℝ) : ℝ :=
  posPart u (posPart V (q.2 + t * max q.1 0) - posPart V q.2) +
    posPart V (max q.1 0 - t * max q.1 0)

/-- `sup_{t ∈ [c, 1]} clampF u V q t`. -/
private def clampG (u V : ℝ → ℝ) (c : ℝ) (q : ℝ × ℝ) : ℝ := sSup (clampF u V q '' Icc c 1)

private lemma continuous_clampF (hu : ContinuousOn u (Ici 0)) (hV : IsValueFn V) :
    Continuous ↿(clampF u V) := by
  have hVt : Continuous (posPart V) := continuous_posPart hV.continuousOn
  have hut : Continuous (posPart u) := continuous_posPart hu
  show Continuous fun p : (ℝ × ℝ) × ℝ => clampF u V p.1 p.2
  unfold clampF
  fun_prop

private lemma clampF_eq (hV : IsValueFn V) {b s t : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s)
    (ht : t ∈ Icc 0 1) : clampF u V (b, s) t = obj u V b s (t * b) := by
  have h1 : 0 ≤ s + t * b := by nlinarith [ht.1]
  have h2 : 0 ≤ b - t * b := by nlinarith [ht.2]
  have h3 : 0 ≤ V (s + t * b) - V s := hV.gain_nonneg hs (mul_nonneg ht.1 hb)
  simp only [clampF, obj, gain, posPart, max_eq_left hb]
  rw [max_eq_left h1, max_eq_left hs, max_eq_left h2, max_eq_left h3]

private lemma image_clampF (hV : IsValueFn V) {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) :
    clampF u V (b, s) '' Icc 0 1 = obj u V b s '' Icc 0 b := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * b, ⟨mul_nonneg ht.1 hb, by nlinarith [ht.2]⟩, (clampF_eq hV hb hs ht).symm⟩
  · rintro ⟨d, hd, rfl⟩
    rcases hb.eq_or_lt with rfl | hb'
    · have hd0 : d = 0 := le_antisymm hd.2 hd.1
      subst hd0
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        rw [clampF_eq hV le_rfl hs ⟨le_rfl, zero_le_one⟩, zero_mul]⟩
    · have ht : d / b ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hd.1 hb, (div_le_one hb').mpr hd.2⟩
      exact ⟨d / b, ht, by rw [clampF_eq hV hb hs ht, div_mul_cancel₀ d hb'.ne']⟩

private lemma clampG_zero_eq (hV : IsValueFn V) {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) :
    clampG u V 0 (b, s) = bellH u V b s := by
  unfold clampG bellH
  rw [image_clampF hV hb hs]

/-- `(b, s) ↦ H_V(b⁺, s⁺)` is measurable. -/
theorem measurable_bellH_clamp (hu : ContinuousOn u (Ici 0)) (hum : MonotoneOn u (Ici 0))
    (hV : IsValueFn V) : Measurable fun p : ℝ × ℝ => bellH u V (max p.1 0) (max p.2 0) := by
  have hG : Continuous (clampG u V 0) :=
    isCompact_Icc.continuous_sSup (continuous_clampF hu hV)
  have e : (fun p : ℝ × ℝ => bellH u V (max p.1 0) (max p.2 0)) =
      fun p => clampG u V 0 (max p.1 0, max p.2 0) := by
    funext p
    exact (clampG_zero_eq hV (le_max_right _ _) (le_max_right _ _)).symm
  rw [e]
  exact (hG.comp ((continuous_fst.max continuous_const).prodMk
    (continuous_snd.max continuous_const))).measurable

/-- A measurable selection of maximisers of the buyer problem `H_V(b,s)`. -/
theorem exists_measurable_argmax (hu : ContinuousOn u (Ici 0)) (hum : MonotoneOn u (Ici 0))
    (hV : IsValueFn V) :
    ∃ dsel : ℝ × ℝ → ℝ, Measurable dsel ∧ ∀ b s, 0 ≤ b → 0 ≤ s →
      dsel (b, s) ∈ Icc 0 b ∧ obj u V b s (dsel (b, s)) = bellH u V b s := by
  have hF := continuous_clampF hu hV
  have hFq : ∀ q, Continuous (clampF u V q) := fun q => hF.comp (Continuous.prodMk_right q)
  have hG : ∀ c, Continuous (clampG u V c) := fun c => isCompact_Icc.continuous_sSup hF
  have hle : ∀ c q t, t ∈ Icc c 1 → clampF u V q t ≤ clampG u V c q := fun c q t ht =>
    le_csSup (isCompact_Icc.image (hFq q)).bddAbove ⟨t, ht, rfl⟩
  have hmem : ∀ c q, c ≤ 1 → clampG u V c q ∈ clampF u V q '' Icc c 1 := fun c q hc =>
    (isCompact_Icc.image (hFq q)).sSup_mem ((nonempty_Icc.2 hc).image _)
  -- the argmax set in the normalised variable and its largest element
  set A : ℝ × ℝ → Set ℝ := fun q => Icc 0 1 ∩ clampF u V q ⁻¹' {clampG u V 0 q} with hAdef
  set τ : ℝ × ℝ → ℝ := fun q => sSup (A q) with hτdef
  have hAc : ∀ q, IsCompact (A q) := fun q =>
    isCompact_Icc.inter_right (isClosed_singleton.preimage (hFq q))
  have hAne : ∀ q, (A q).Nonempty := fun q => by
    obtain ⟨t, ht, he⟩ := hmem 0 q zero_le_one
    exact ⟨t, ht, he⟩
  have hτA : ∀ q, τ q ∈ A q := fun q => (hAc q).sSup_mem (hAne q)
  have hτle : ∀ q t, t ∈ A q → t ≤ τ q := fun q t ht => le_csSup (hAc q).bddAbove ht
  have hτm : Measurable τ := by
    refine measurable_of_Ici fun c => ?_
    rcases le_or_gt c 0 with hc0 | hc0
    · convert MeasurableSet.univ
      ext q
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact hc0.trans (hτA q).1.1
    rcases le_or_gt c 1 with hc1 | hc1
    · have e : τ ⁻¹' Ici c = {q | clampG u V 0 q ≤ clampG u V c q} := by
        ext q
        simp only [mem_preimage, mem_Ici, mem_ofPred_eq]
        constructor
        · intro h
          have hA := hτA q
          have h2 : clampF u V q (τ q) = clampG u V 0 q := hA.2
          rw [← h2]
          exact hle c q (τ q) ⟨h, hA.1.2⟩
        · intro h
          obtain ⟨t, ht, he⟩ := hmem c q hc1
          have ht01 : t ∈ Icc (0:ℝ) 1 := ⟨hc0.le.trans ht.1, ht.2⟩
          have h1 : clampF u V q t ≤ clampG u V 0 q := hle 0 q t ht01
          have htA : t ∈ A q := ⟨ht01, le_antisymm h1 (by rw [he]; exact h)⟩
          exact ht.1.trans (hτle q t htA)
      rw [e]
      exact measurableSet_le (hG 0).measurable (hG c).measurable
    · convert MeasurableSet.empty
      ext q
      simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false, not_le]
      exact (hτA q).1.2.trans_lt hc1
  refine ⟨fun q => τ q * max q.1 0, hτm.mul (measurable_fst.max measurable_const),
    fun b s hb hs => ?_⟩
  have hA := hτA (b, s)
  simp only [max_eq_left hb]
  refine ⟨⟨mul_nonneg hA.1.1 hb, by nlinarith [hA.1.2]⟩, ?_⟩
  rw [← clampF_eq hV hb hs hA.1, ← clampG_zero_eq hV hb hs]
  exact hA.2

end Molico
