import MonetaryExistenceBuyer.General.Bargain
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Reinserting physical output (`rem:physicaloutput`)

Given a transfer kernel `ν` that reproduces the meeting measure `Γ` of an equilibrium and is
supported on maximisers of the buyer problem at every pair, the trade kernel
`κ_{b,s} = (d ↦ (K⁻¹(Δ_V(s,d)), d))_# ν_{b,s}` makes `(V, η, κ)` a stationary monetary equilibrium
in relaxed strategies of `def:generaleq` with `θ = 1`: `κ` is supported on the bargaining sets
(`mem_bargainSet_of_argmax`), the Bellman equation is `buyerreduction_bellman`, the wealth
transitions are unchanged, and positive output is equivalent to `Δ_V(s,d) > 0`.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory

noncomputable section

namespace Molico.Environment

variable (E : Environment)

/-- The trade map `((b,s),d) ↦ (K⁻¹(Δ_V(s,d)), d)`, made measurable by clamping the arguments
of `V` and the gain to `[0,∞)`. -/
private def trade (V : ℝ → ℝ) (x : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (E.Kinv (max (posPart V (x.1.2 + x.2) - posPart V x.1.2) 0), x.2)

private lemma measurable_trade {V : ℝ → ℝ} (hV : ContinuousOn V (Ici 0)) :
    Measurable (E.trade V) := by
  have hc : Continuous (posPart V) := continuous_posPart hV
  have h1 : Continuous fun x : (ℝ × ℝ) × ℝ => posPart V (x.1.2 + x.2) - posPart V x.1.2 := by
    fun_prop
  exact (E.measurable_Kinv_max.comp h1.measurable).prodMk measurable_snd

private lemma trade_eq {V : ℝ → ℝ} (hV : IsValueFn V) {b s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) :
    E.trade V ((b, s), d) = (E.Kinv (gain V s d), d) := by
  simp only [trade, posPart_eq (f := V) (add_nonneg hs hd), posPart_eq (f := V) hs]
  rw [max_eq_left (show 0 ≤ V (s + d) - V s from hV.gain_nonneg hs hd)]
  rfl

/-- The graph map `d ↦ (g d, d)` of a measurable function is a measurable embedding. -/
private lemma measurableEmbedding_graph {g : ℝ → ℝ} (hg : Measurable g) :
    MeasurableEmbedding fun d : ℝ => (g d, d) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := Prod.snd) (hg.prodMk measurable_id) ?_
    measurable_snd (fun d => rfl)
  have : range (fun d : ℝ => (g d, d)) = {p : ℝ × ℝ | p.1 = g p.2} := by
    ext p
    constructor
    · rintro ⟨d, rfl⟩; rfl
    · intro hp; exact ⟨p.2, Prod.ext hp.symm rfl⟩
  rw [this]
  exact measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)

private lemma measurableEmbedding_trade {V : ℝ → ℝ} (hV : ContinuousOn V (Ici 0)) (a : ℝ × ℝ) :
    MeasurableEmbedding fun d => E.trade V (a, d) := by
  have hc : Continuous (posPart V) := continuous_posPart hV
  have h1 : Continuous fun d : ℝ => posPart V (a.2 + d) - posPart V a.2 := by fun_prop
  exact measurableEmbedding_graph (E.measurable_Kinv_max.comp h1.measurable)

/-- The trade kernel `κ = (id × ν)_# trade`. -/
private def tk (V : ℝ → ℝ) (ν : Kernel (ℝ × ℝ) ℝ) : Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  Kernel.map (Kernel.id ×ₖ ν) (E.trade V)

private lemma tk_apply {V : ℝ → ℝ} (hV : ContinuousOn V (Ici 0)) (ν : Kernel (ℝ × ℝ) ℝ)
    [IsMarkovKernel ν] (a : ℝ × ℝ) :
    E.tk V ν a = (ν a).map (fun d => E.trade V (a, d)) := by
  rw [tk, Kernel.map_apply _ (E.measurable_trade hV), Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map (E.measurable_trade hV) measurable_prodMk_left]
  rfl

private lemma isMarkovKernel_tk {V : ℝ → ℝ} (hV : ContinuousOn V (Ici 0))
    (ν : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel ν] : IsMarkovKernel (E.tk V ν) :=
  Kernel.IsMarkovKernel.map _ (E.measurable_trade hV)

private lemma id_prod_tk {V : ℝ → ℝ} (hV : ContinuousOn V (Ici 0)) (ν : Kernel (ℝ × ℝ) ℝ)
    [IsMarkovKernel ν] :
    Kernel.id ×ₖ E.tk V ν =
      Kernel.map (Kernel.id ×ₖ ν) (fun x : (ℝ × ℝ) × ℝ => (x.1, E.trade V x)) := by
  have hΦ : Measurable fun x : (ℝ × ℝ) × ℝ => (x.1, E.trade V x) :=
    measurable_fst.prodMk (E.measurable_trade hV)
  have ht : ∀ a : ℝ × ℝ, Measurable fun d => E.trade V (a, d) := fun a =>
    (E.measurable_trade hV).comp measurable_prodMk_left
  have := E.isMarkovKernel_tk hV ν
  ext1 a
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, E.tk_apply hV,
    Kernel.map_apply _ hΦ, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map measurable_prodMk_left (ht a), Measure.map_map hΦ measurable_prodMk_left]
  rfl

/-- `rem:physicaloutput`, given a transfer kernel. -/
theorem physicaloutput_of_kernel (T : ThreatRule) {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ}
    {Γ : Measure (ℝ × ℝ × ℝ)} (h : IsEquilibrium E.u E.β M V η Γ) (hT : T.Admissible V)
    (ν : Kernel (ℝ × ℝ) ℝ) [IsMarkovKernel ν]
    (hrep : Γ.map (fun p => ((p.1, p.2.1), p.2.2)) = (η.prod η) ⊗ₘ ν)
    (hsupp : ∀ b s, 0 ≤ b → 0 ≤ s →
      ∀ᵐ d ∂(ν (b, s)), d ∈ Icc 0 b ∧ obj E.u V b s d = bellH E.u V b s) :
    ∃ κ : Kernel (ℝ × ℝ) (ℝ × ℝ), E.IsGeneralEquilibrium 1 T M V η κ ∧
      ((∀ b s, 0 ≤ b → 0 ≤ s → ∃ d, ν (b, s) = Measure.dirac d) → IsDeterministicKernel κ) := by
  have := h.isProb_η
  have hV := h.value
  have hVc := hV.continuousOn
  have := E.isMarkovKernel_tk hVc ν
  set κ := E.tk V ν with hκ
  have mtr := E.measurable_trade hVc
  -- support on the bargaining sets
  have hsuppκ : ∀ b s, 0 ≤ b → 0 ≤ s → κ (b, s) (E.bargainSet 1 T V b s)ᶜ = 0 := by
    intro b s hb hs
    rw [hκ, E.tk_apply hVc, (E.measurableEmbedding_trade hVc (b, s)).map_apply]
    refine measure_mono_null ?_ (ae_iff.mp (hsupp b s hb hs))
    intro d hd
    simp only [mem_ofPred_eq]
    intro hgood
    apply hd
    show E.trade V ((b, s), d) ∈ E.bargainSet 1 T V b s
    rw [E.trade_eq hV hs hgood.1.1]
    exact E.mem_bargainSet_of_argmax T hV hb hs hgood.1 hgood.2
  -- the meeting distribution
  have hρ : Measurable fun p : ℝ × ℝ × ℝ => ((p.1, p.2.1), p.2.2) := by fun_prop
  have hΦ : Measurable fun x : (ℝ × ℝ) × ℝ => (x.1, E.trade V x) := measurable_fst.prodMk mtr
  have hΦρ : Measurable fun p : ℝ × ℝ × ℝ =>
      ((p.1, p.2.1), E.trade V ((p.1, p.2.1), p.2.2)) := hΦ.comp hρ
  have hΞ : Ξ η κ = Γ.map fun p : ℝ × ℝ × ℝ =>
      ((p.1, p.2.1), E.trade V ((p.1, p.2.1), p.2.2)) := by
    rw [Ξ, Measure.compProd_eq_comp_prod, hκ, E.id_prod_tk hVc, ← Measure.map_comp _ _ hΦ,
      ← Measure.compProd_eq_comp_prod, ← hrep, Measure.map_map hΦ hρ]
    rfl
  -- `Γ`-a.e. seller wealth is nonnegative
  have hneg : Γ {p : ℝ × ℝ × ℝ | p.2.1 < 0} = 0 := by
    have hm : Measurable pairBS := by unfold pairBS; fun_prop
    have e : {p : ℝ × ℝ × ℝ | p.2.1 < 0} = pairBS ⁻¹' (univ ×ˢ Iio 0) := by
      ext p; simp [pairBS]
    rw [e, ← Measure.map_apply hm (MeasurableSet.univ.prod measurableSet_Iio), h.marginal,
      Measure.prod_prod, h.η_nonneg, mul_zero]
  refine ⟨κ, ?_, ?_⟩
  · refine
      { V_cont := hVc
        V_nonneg := fun x hx => hV.nonneg hx
        threat := hT
        isProb_η := inferInstance
        η_nonneg := h.η_nonneg
        integrable_id := h.integrable_id
        mean := h.mean
        markov := inferInstance
        support := hsuppκ
        bellman_integrable_b := fun m hm =>
          E.buyerreduction_integrable_b T hV h.η_nonneg hsuppκ hm
        bellman_integrable_s := fun m hm =>
          E.buyerreduction_integrable_s T h.η_nonneg hsuppκ hm
        bellman := fun m hm =>
          (E.buyerreduction_bellman T hV h.η_nonneg hsuppκ hm).mpr (h.bellman m hm)
        stationary := ?_
        monetary := ?_ }
    · rw [hΞ, Measure.map_map (by fun_prop) hΦρ, Measure.map_map (by fun_prop) hΦρ]
      exact h.stationary
    · have hS : MeasurableSet {z : (ℝ × ℝ) × (ℝ × ℝ) | 0 < z.2.1} :=
        measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)
      -- `Γ`-a.e. payment is nonnegative
      have hdneg : Γ {p : ℝ × ℝ × ℝ | p.2.2 < 0} = 0 := by
        refine measure_mono_null ?_ h.Γ_meeting
        intro p hp hm
        exact absurd hm.1 (not_le.2 hp)
      rw [hΞ, Measure.map_apply hΦρ hS]
      intro h0
      apply h.monetary
      refine measure_mono_null ?_ (measure_union_null (measure_union_null h0 hneg) hdneg)
      intro p hg
      by_cases hs : p.2.1 < 0
      · exact Or.inl (Or.inr hs)
      by_cases hd : p.2.2 < 0
      · exact Or.inr hd
      · left; left
        replace hs := not_lt.mp hs
        replace hd := not_lt.mp hd
        simp only [mem_preimage, mem_ofPred_eq]
        rw [E.trade_eq hV hs hd]
        exact E.Kinv_pos hg
  · intro hdir b s hb hs
    obtain ⟨d, hd⟩ := hdir b s hb hs
    refine ⟨E.trade V ((b, s), d), ?_⟩
    have hmd : Measurable fun d => E.trade V ((b, s), d) := mtr.comp measurable_prodMk_left
    rw [hκ, E.tk_apply hVc, hd, Measure.map_dirac' hmd]

end Molico.Environment
