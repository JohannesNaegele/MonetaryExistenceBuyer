import MonetaryExistenceBuyer.General
import MonetaryExistenceBuyer.General.Composite
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Automatic bounds for stationary values (`lem:stationaryvaluebound`)

In `def:generaleq` the value function is only assumed continuous and nonnegative. Under
`ass:utility` on the composite utility `u = U ∘ K⁻¹`, every stationary equilibrium nevertheless
has `0 ≤ V(m) ≤ ū/σ` for `η`-almost every `m` (and on the support of `η`), and `V ∈ L¹(η)`.
Here `σ = r/π` (`def:effectivediscount`).

The proof follows the manuscript. Writing `Ξ` for the meeting distribution and
`B = b - d`, `S = s + d` for the post-trade wealth maps:

1. (`integrable_increments`) The continuation-value increments `V(B) - V(b)` and `V(S) - V(s)`
   are `Ξ`-integrable. On the bargaining set the seller's increment is nonnegative and the
   buyer's is at least `-ū` (participation constraints and `U(q) = u(K(q)) ≤ ū`). For the
   truncations `V_N = min(V, N)`, stationarity `eq:generalstationarity` gives
   `∫ [V_N(S) - V_N(s)] dΞ = ∫ [V_N(b) - V_N(B)] dΞ ≤ ū`, and Fatou's lemma lets `N → ∞`.
2. (`integrable_value`) Averaging the Bellman equation `eq:generalbellman` over `η` and using
   Fubini, `r V` is `η`-a.e. equal to `π` times an `η`-integrable function.
3. (`value_le_ae`) Dropping production costs and bounding `U ≤ ū` in `eq:generalbellman` gives
   `(1 + r) V ≤ P V + π ū` for the one-period wealth transition `P`; since `P` fixes constants,
   `rc = πū` for `c = ū/σ`, and `P` is positive, `W = (V - c)₊` satisfies `(1 + r) W ≤ P W`.
   Stationarity gives `∫ P W dη = ∫ W dη < ∞`, hence `W = 0` `η`-a.e.
4. (`value_le_of_mem_support`) Continuity of `V` extends the bound to `supp η`.

Measurability: `U`, `K` are only continuous on `Q = [0, q̄)` and `V` only on `[0, ∞)`; we use
the Borel versions `𝟙_Q U`, `𝟙_Q K` and `V ∘ max(·, 0)` (`posPart`), which agree with the
originals wherever the relevant measures live.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Molico.Environment

variable (E : Environment)

/-- `def:effectivediscount`: `σ = 1/β - 1 = r/π`. -/
def σ : ℝ := E.r / E.π

lemma σ_pos : 0 < E.σ := div_pos E.r_pos E.π_pos

lemma σ_eq : E.σ = 1 / E.β - 1 := (E.one_div_β_sub_one).symm

/-! ### Borel versions of `U` and `K` -/

/-- `Q = [0, q̄)` is a Borel set. -/
private lemma measurableSet_Q : MeasurableSet E.Q :=
  (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

/-- `U` is continuous on `Q`, so `𝟙_Q U` is Borel. -/
private lemma measurable_indicator_U : Measurable (E.Q.indicator E.U) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise (s := E.Q) (g := (0 : ℝ → ℝ)) E.U_cont
    continuousOn_const E.measurableSet_Q

/-- `K` is continuous on `Q`, so `𝟙_Q K` is Borel. -/
private lemma measurable_indicator_K : Measurable (E.Q.indicator E.K) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise (s := E.Q) (g := (0 : ℝ → ℝ)) E.K_cont
    continuousOn_const E.measurableSet_Q

/-- `U(q) = u(K(q)) ≤ ū` for `q ∈ Q` (`def:compositeutility`, `ass:utility` (U6)). -/
private lemma U_le_ubar (U : AdmissibleUtility) (hu : U.u = E.u) {q : ℝ} (hq : q ∈ E.Q) :
    E.U q ≤ U.ubar := by
  have : E.U q = U.u (E.K q) := by rw [hu, Environment.u, E.Kinv_K hq]
  rw [this]
  exact U.le_ubar (E.K_nonneg hq)

/-- The Borel set of admissible meeting records `((b, s), (q, d))`: nonnegative wealths,
`q ∈ Q`, `0 ≤ d ≤ b`, and both participation constraints of `eq:tradefeasible`, written with the
Borel versions of `U`, `K`, `V`. It contains every bargaining set `ℬ^θ_{V,T}(b,s)`, `b, s ≥ 0`. -/
private def goodSet (V : ℝ → ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {z | 0 ≤ z.1.1 ∧ 0 ≤ z.1.2 ∧ z.2.1 ∈ E.Q ∧ 0 ≤ z.2.2 ∧ z.2.2 ≤ z.1.1 ∧
    posPart V z.1.1 ≤ E.Q.indicator E.U z.2.1 + posPart V (z.1.1 - z.2.2) ∧
    posPart V z.1.2 ≤ -E.Q.indicator E.K z.2.1 + posPart V (z.1.2 + z.2.2)}

private lemma measurableSet_goodSet {V : ℝ → ℝ} (hV : ContinuousOn V (Ici 0)) :
    MeasurableSet (E.goodSet V) := by
  have hVt : Measurable (posPart V) := (continuous_posPart hV).measurable
  have hU := E.measurable_indicator_U
  have hK := E.measurable_indicator_K
  exact (measurableSet_le measurable_const measurable_fst.fst).inter
    ((measurableSet_le measurable_const measurable_fst.snd).inter
    ((measurable_snd.fst E.measurableSet_Q).inter
    ((measurableSet_le measurable_const measurable_snd.snd).inter
    ((measurableSet_le measurable_snd.snd measurable_fst.fst).inter
    ((measurableSet_le (hVt.comp measurable_fst.fst)
      ((hU.comp measurable_snd.fst).add
        (hVt.comp (measurable_fst.fst.sub measurable_snd.snd)))).inter
    (measurableSet_le (hVt.comp measurable_fst.snd)
      ((hK.comp measurable_snd.fst).neg.add
        (hVt.comp (measurable_fst.snd.add measurable_snd.snd)))))))))

variable {E}

/-! ### Generic measure-theoretic helpers -/

/-- Bounded continuous functions are integrable against finite measures. -/
private lemma integrable_of_continuous_of_bounded {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {φ : X → ℝ} (hφ : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- `Integrable.integral_compProd` for the measure `μ ⊗ₘ κ`. -/
private lemma integrable_integral_compProd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ] {f : α × β → ℝ}
    (hf : Integrable f (μ ⊗ₘ κ)) : Integrable (fun a => ∫ b, f (a, b) ∂κ a) μ := by
  rw [Measure.compProd] at hf
  simpa using hf.integral_compProd

/-- `min(a, N) - min(b, N) → a - b` as `N → ∞` (eventually constant). -/
private lemma tendsto_min_sub (a b : ℝ) :
    Tendsto (fun N : ℕ => min a N - min b N) atTop (𝓝 (a - b)) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈max a b⌉₊) fun N hN => ?_
  have hN' : max a b ≤ N := (Nat.le_ceil _).trans (Nat.cast_le.2 hN)
  rw [min_eq_left ((le_max_left a b).trans hN'), min_eq_left ((le_max_right a b).trans hN')]

/-- Fatou's lemma in the form used below: a pointwise limit of functions whose positive parts
have `lintegral` at most `C` has positive part with `lintegral` at most `C`. -/
private lemma lintegral_ofReal_le_of_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {φ : X → ℝ} (hf : ∀ N, Measurable (f N))
    (hlim : ∀ x, Tendsto (fun N => f N x) atTop (𝓝 (φ x))) {C : ℝ}
    (hC : ∀ N, ∫⁻ x, ENNReal.ofReal (f N x) ∂μ ≤ ENNReal.ofReal C) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂μ ≤ ENNReal.ofReal C :=
  calc ∫⁻ x, ENNReal.ofReal (φ x) ∂μ
      = ∫⁻ x, liminf (fun N => ENNReal.ofReal (f N x)) atTop ∂μ := by
        refine lintegral_congr fun x => ?_
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hlim x)).liminf_eq.symm
    _ ≤ liminf (fun N => ∫⁻ x, ENNReal.ofReal (f N x) ∂μ) atTop :=
        lintegral_liminf_le fun N => ENNReal.measurable_ofReal.comp (hf N)
    _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le' (Eventually.of_forall hC).frequently

/-- `∫⁻ φ₊ ≤ ∫⁻ (φ - c)₊ + c` against a probability measure. -/
private lemma lintegral_ofReal_le_shift {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (φ : X → ℝ) (c : ℝ) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂μ ≤
      (∫⁻ x, ENNReal.ofReal (φ x - c) ∂μ) + ENNReal.ofReal c := by
  calc ∫⁻ x, ENNReal.ofReal (φ x) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (φ x - c) + ENNReal.ofReal c) ∂μ := by
        refine lintegral_mono fun x => ?_
        have := ENNReal.ofReal_add_le (p := φ x - c) (q := c)
        rwa [sub_add_cancel] at this
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

namespace IsGeneralEquilibrium

variable {θ : ℝ} {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ} {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}

/-! ### Almost-sure facts about `η`, `κ`, and `Ξ` -/

private lemma ae_nonneg (h : E.IsGeneralEquilibrium θ T M V η κ) : ∀ᵐ x ∂η, 0 ≤ x := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h.η_nonneg] with x hx
  simpa using hx

private lemma posPart_nonneg (h : E.IsGeneralEquilibrium θ T M V η κ) (y : ℝ) :
    0 ≤ posPart V y :=
  h.V_nonneg _ (le_max_right _ _)

private lemma ae_mem_bargainSet (h : E.IsGeneralEquilibrium θ T M V η κ) {b s : ℝ} (hb : 0 ≤ b)
    (hs : 0 ≤ s) : ∀ᵐ x ∂κ (b, s), x ∈ E.bargainSet θ T V b s := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.support b s hb hs)] with x hx
  simpa using hx

private lemma ae_prod_nonneg (h : E.IsGeneralEquilibrium θ T M V η κ) :
    ∀ᵐ p ∂(η.prod η), 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  have := h.isProb_η
  refine (Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => 0 ≤ p.1 ∧ 0 ≤ p.2) ?_).2 ?_
  · exact (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  filter_upwards [h.ae_nonneg] with b hb
  filter_upwards [h.ae_nonneg] with s hs
  exact ⟨hb, hs⟩

/-- `Ξ`-almost every meeting record is admissible: `κ_{b,s}` lives on the bargaining set. -/
private lemma ae_goodSet (h : E.IsGeneralEquilibrium θ T M V η κ) :
    ∀ᵐ z ∂(Ξ η κ), z ∈ E.goodSet V := by
  have := h.isProb_η
  have := h.markov
  rw [Ξ]
  refine (Measure.ae_compProd_iff (p := fun z => z ∈ E.goodSet V) ?_).2 ?_
  · exact E.measurableSet_goodSet h.V_cont
  filter_upwards [h.ae_prod_nonneg] with p hp
  filter_upwards [h.ae_mem_bargainSet hp.1 hp.2] with x hx
  obtain ⟨hQ, hd0, hdb, hB, hS⟩ := hx.1
  simp only [goodSet, mem_ofPred_eq]
  refine ⟨hp.1, hp.2, hQ, hd0, hdb, ?_, ?_⟩
  · rw [Set.indicator_of_mem hQ, posPart_eq hp.1, posPart_eq (sub_nonneg.2 hdb)]
    exact hB
  · rw [Set.indicator_of_mem hQ, posPart_eq hp.2, posPart_eq (add_nonneg hp.2 hd0)]
    exact hS

/-- The `b`-marginal of `Ξ` is `η`. -/
private lemma map_b (h : E.IsGeneralEquilibrium θ T M V η κ) :
    (Ξ η κ).map (fun z => z.1.1) = η := by
  have := h.isProb_η
  have := h.markov
  have h1 : (Ξ η κ).map Prod.fst = η.prod η := Measure.fst_compProd (η.prod η) κ
  rw [show (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1) = Prod.fst ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_fst measurable_fst, h1, Measure.map_fst_prod, measure_univ,
    one_smul]

/-- The `s`-marginal of `Ξ` is `η`. -/
private lemma map_s (h : E.IsGeneralEquilibrium θ T M V η κ) :
    (Ξ η κ).map (fun z => z.1.2) = η := by
  have := h.isProb_η
  have := h.markov
  have h1 : (Ξ η κ).map Prod.fst = η.prod η := Measure.fst_compProd (η.prod η) κ
  rw [show (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2) = Prod.snd ∘ Prod.fst from rfl,
    ← Measure.map_map measurable_snd measurable_fst, h1, Measure.map_snd_prod, measure_univ,
    one_smul]

/-- `eq:generalstationarity` tested against a bounded continuous `g`: the post-trade wealths
`B`, `S` and the pre-trade wealths `b`, `s` have the same total law `2η` under `Ξ`. -/
private lemma integral_post_eq_pre (h : E.IsGeneralEquilibrium θ T M V η κ) {g : ℝ → ℝ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ y, |g y| ≤ C) :
    ∫ z, g (z.1.1 - z.2.2) ∂(Ξ η κ) + ∫ z, g (z.1.2 + z.2.2) ∂(Ξ η κ) =
      ∫ z, g z.1.1 ∂(Ξ η κ) + ∫ z, g z.1.2 ∂(Ξ η κ) := by
  have := h.isProb_η
  have := h.markov
  have : IsProbabilityMeasure (Ξ η κ) := by unfold Ξ; infer_instance
  have mB : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 - z.2.2 :=
    measurable_fst.fst.sub measurable_snd.snd
  have mS : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 + z.2.2 :=
    measurable_fst.snd.add measurable_snd.snd
  have e1 : ∫ y, g y ∂η = ∫ z, g z.1.1 ∂(Ξ η κ) := by
    conv_lhs => rw [← h.map_b]
    rw [integral_map measurable_fst.fst.aemeasurable hg.aestronglyMeasurable]
  have e2 : ∫ y, g y ∂η = ∫ z, g z.1.2 ∂(Ξ η κ) := by
    conv_lhs => rw [← h.map_s]
    rw [integral_map measurable_fst.snd.aemeasurable hg.aestronglyMeasurable]
  have e3 : ∫ y, g y ∂η =
      2⁻¹ * ∫ z, g (z.1.1 - z.2.2) ∂(Ξ η κ) + 2⁻¹ * ∫ z, g (z.1.2 + z.2.2) ∂(Ξ η κ) := by
    have : IsFiniteMeasure ((Ξ η κ).map fun z => z.1.1 - z.2.2) := inferInstance
    have : IsFiniteMeasure ((Ξ η κ).map fun z => z.1.2 + z.2.2) := inferInstance
    conv_lhs => rw [h.stationary]
    rw [integral_add_measure, integral_smul_measure, integral_smul_measure,
      integral_map mB.aemeasurable hg.aestronglyMeasurable,
      integral_map mS.aemeasurable hg.aestronglyMeasurable]
    · simp [ENNReal.toReal_inv]
    · exact (integrable_of_continuous_of_bounded _ hg hC).smul_measure (by simp)
    · exact (integrable_of_continuous_of_bounded _ hg hC).smul_measure (by simp)
  linarith

/-! ### Step 1: integrable continuation-value increments -/

/-- Step 1 of `lem:stationaryvaluebound`: the buyer's increment `V(b - d) - V(b)` (shifted by
`ū`) and the seller's increment `V(s + d) - V(s)` are `Ξ`-integrable. On the bargaining set the
seller's increment is `≥ K(q) ≥ 0` and the buyer's is `≥ -U(q) ≥ -ū`; for the truncations
`V_N = min(V, N)` stationarity gives `∫ [V_N(S) - V_N(s)] dΞ = ∫ [V_N(b) - V_N(B)] dΞ ≤ ū`, and
Fatou's lemma lets `N → ∞`. -/
private lemma integrable_increments (U : AdmissibleUtility) (hu : U.u = E.u)
    (h : E.IsGeneralEquilibrium θ T M V η κ) :
    Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      posPart V (z.1.1 - z.2.2) - posPart V z.1.1 + U.ubar) (Ξ η κ) ∧
    Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => posPart V (z.1.2 + z.2.2) - posPart V z.1.2)
      (Ξ η κ) := by
  have := h.isProb_η
  have := h.markov
  have : IsProbabilityMeasure (Ξ η κ) := by unfold Ξ; infer_instance
  have hVt : Continuous (posPart V) := continuous_posPart h.V_cont
  have hVt0 := h.posPart_nonneg
  have hū := U.ubar_pos
  -- a.e. lower bounds from the participation constraints
  have hDB : ∀ᵐ z ∂(Ξ η κ), -U.ubar ≤ posPart V (z.1.1 - z.2.2) - posPart V z.1.1 := by
    filter_upwards [h.ae_goodSet] with z hz
    obtain ⟨-, -, hQ, -, -, hB, -⟩ := hz
    rw [Set.indicator_of_mem hQ] at hB
    linarith [E.U_le_ubar U hu hQ]
  have hDS : ∀ᵐ z ∂(Ξ η κ), 0 ≤ posPart V (z.1.2 + z.2.2) - posPart V z.1.2 := by
    filter_upwards [h.ae_goodSet] with z hz
    obtain ⟨-, -, hQ, -, -, -, hS⟩ := hz
    rw [Set.indicator_of_mem hQ] at hS
    linarith [E.K_nonneg hQ]
  -- truncations `V_N = min(V, N)`
  set g : ℕ → ℝ → ℝ := fun N y => min (posPart V y) N
  have hgc : ∀ N, Continuous (g N) := fun N => hVt.min continuous_const
  have hgb : ∀ N y, |g N y| ≤ N := fun N y => by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact abs_le.2 ⟨le_min (by linarith [hVt0 y]) (by linarith), min_le_right _ _⟩
  have mB : Continuous fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 - z.2.2 :=
    continuous_fst.fst.sub continuous_snd.snd
  have mS : Continuous fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 + z.2.2 :=
    continuous_fst.snd.add continuous_snd.snd
  have i1 : ∀ N, Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g N (z.1.1 - z.2.2)) (Ξ η κ) :=
    fun N => integrable_of_continuous_of_bounded _ ((hgc N).comp mB) fun z => hgb N _
  have i2 : ∀ N, Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g N z.1.1) (Ξ η κ) :=
    fun N => integrable_of_continuous_of_bounded _ ((hgc N).comp continuous_fst.fst)
      fun z => hgb N _
  have i3 : ∀ N, Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g N (z.1.2 + z.2.2)) (Ξ η κ) :=
    fun N => integrable_of_continuous_of_bounded _ ((hgc N).comp mS) fun z => hgb N _
  have i4 : ∀ N, Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g N z.1.2) (Ξ η κ) :=
    fun N => integrable_of_continuous_of_bounded _ ((hgc N).comp continuous_fst.snd)
      fun z => hgb N _
  have i12 : ∀ N, Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g N (z.1.1 - z.2.2) - g N z.1.1)
      (Ξ η κ) := fun N => (i1 N).sub (i2 N)
  have i34 : ∀ N, Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g N (z.1.2 + z.2.2) - g N z.1.2)
      (Ξ η κ) := fun N => (i3 N).sub (i4 N)
  have i12' : ∀ N, Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => g N (z.1.1 - z.2.2) - g N z.1.1 + U.ubar) (Ξ η κ) :=
    fun N => (i12 N).add (integrable_const _)
  -- the truncated increments integrate to zero in total (stationarity)
  have hid : ∀ N, ∫ z, (g N (z.1.1 - z.2.2) - g N z.1.1) ∂(Ξ η κ) +
      ∫ z, (g N (z.1.2 + z.2.2) - g N z.1.2) ∂(Ξ η κ) = 0 := by
    intro N
    rw [integral_sub (i1 N) (i2 N), integral_sub (i3 N) (i4 N)]
    linarith [h.integral_post_eq_pre (hgc N) (hgb N)]
  -- truncation preserves the lower bounds
  have hS_nonneg : ∀ N, 0 ≤ᵐ[Ξ η κ] fun z => g N (z.1.2 + z.2.2) - g N z.1.2 := fun N => by
    filter_upwards [hDS] with z hz
    exact sub_nonneg.2 (min_le_min (by linarith) le_rfl)
  have hB_lower : ∀ N, ∀ᵐ z ∂(Ξ η κ), -U.ubar ≤ g N (z.1.1 - z.2.2) - g N z.1.1 := fun N => by
    filter_upwards [hDB] with z hz
    have : min (posPart V z.1.1) (N : ℝ) - U.ubar ≤ min (posPart V (z.1.1 - z.2.2)) N := by
      rw [← min_sub_sub_right]
      exact min_le_min (by linarith) (by linarith)
    simp only [g]
    linarith
  -- the uniform bounds `∫ [V_N(S) - V_N(s)] ≤ ū` and `∫ [V_N(B) - V_N(b) + ū] ≤ ū`
  have hSint : ∀ N, ∫ z, (g N (z.1.2 + z.2.2) - g N z.1.2) ∂(Ξ η κ) ≤ U.ubar := by
    intro N
    have hlow : -U.ubar ≤ ∫ z, (g N (z.1.1 - z.2.2) - g N z.1.1) ∂(Ξ η κ) := by
      have := integral_mono_ae (integrable_const (-U.ubar)) (i12 N) (hB_lower N)
      simpa using this
    linarith [hid N]
  have hBint : ∀ N, ∫ z, (g N (z.1.1 - z.2.2) - g N z.1.1 + U.ubar) ∂(Ξ η κ) ≤ U.ubar := by
    intro N
    rw [integral_add (i12 N) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
    have := integral_nonneg_of_ae (hS_nonneg N)
    linarith [hid N]
  -- Fatou
  have hS_lint : ∫⁻ z, ENNReal.ofReal (posPart V (z.1.2 + z.2.2) - posPart V z.1.2) ∂(Ξ η κ) ≤
      ENNReal.ofReal U.ubar := by
    refine lintegral_ofReal_le_of_tendsto (f := fun N z => g N (z.1.2 + z.2.2) - g N z.1.2)
      (fun N => (((hgc N).comp mS).sub ((hgc N).comp continuous_fst.snd)).measurable)
      (fun z => tendsto_min_sub _ _) fun N => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (i34 N) (hS_nonneg N)]
    exact ENNReal.ofReal_le_ofReal (hSint N)
  have hB_lint : ∫⁻ z, ENNReal.ofReal (posPart V (z.1.1 - z.2.2) - posPart V z.1.1 + U.ubar)
      ∂(Ξ η κ) ≤ ENNReal.ofReal U.ubar := by
    refine lintegral_ofReal_le_of_tendsto
      (f := fun N z => g N (z.1.1 - z.2.2) - g N z.1.1 + U.ubar)
      (fun N => ((((hgc N).comp mB).sub ((hgc N).comp continuous_fst.fst)).add
        continuous_const).measurable)
      (fun z => (tendsto_min_sub _ _).add_const _) fun N => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (i12' N)
      (by filter_upwards [hB_lower N] with z hz; simp only [Pi.zero_apply]; linarith)]
    exact ENNReal.ofReal_le_ofReal (hBint N)
  refine ⟨⟨(((hVt.comp mB).sub (hVt.comp continuous_fst.fst)).add
      continuous_const).aestronglyMeasurable, ?_⟩,
    ⟨((hVt.comp mS).sub (hVt.comp continuous_fst.snd)).aestronglyMeasurable, ?_⟩⟩
  · rw [hasFiniteIntegral_iff_ofReal
      (by filter_upwards [hDB] with z hz; simp only [Pi.zero_apply]; linarith)]
    exact hB_lint.trans_lt ENNReal.ofReal_lt_top
  · rw [hasFiniteIntegral_iff_ofReal hDS]
    exact hS_lint.trans_lt ENNReal.ofReal_lt_top

/-! ### Step 2: `V ∈ L¹(η)` -/

/-- `lem:stationaryvaluebound`, integrability: `V ∈ L¹(η)`. Averaging `eq:generalbellman` over
`η`, Fubini identifies `r V(m)` (for `η`-a.e. `m`) with `π` times the sum of two `η`-integrable
functions, the iterated integrals of the buyer's surplus `U(q) + V(b-d) - V(b)` and the seller's
surplus `-K(q) + V(s+d) - V(s)`, which are `Ξ`-integrable by `integrable_increments`. -/
theorem integrable_value (U : AdmissibleUtility) (hu : U.u = E.u)
    {θ : ℝ} {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ} {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    (h : E.IsGeneralEquilibrium θ T M V η κ) : Integrable V η := by
  have := h.isProb_η
  have := h.markov
  have : IsProbabilityMeasure (Ξ η κ) := by unfold Ξ; infer_instance
  obtain ⟨hDB, hDS⟩ := integrable_increments U hu h
  have hVt : Continuous (posPart V) := continuous_posPart h.V_cont
  have hU := E.measurable_indicator_U
  have hK := E.measurable_indicator_K
  -- the buyer's and seller's surplus as Borel functions on `Ξ`
  set IB : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z =>
    E.Q.indicator E.U z.2.1 + posPart V (z.1.1 - z.2.2) - posPart V z.1.1
  set IS : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z =>
    -E.Q.indicator E.K z.2.1 + posPart V (z.1.2 + z.2.2) - posPart V z.1.2
  have mIB : Measurable IB :=
    ((hU.comp measurable_snd.fst).add
      (hVt.measurable.comp (measurable_fst.fst.sub measurable_snd.snd))).sub
      (hVt.measurable.comp measurable_fst.fst)
  have mIS : Measurable IS :=
    ((hK.comp measurable_snd.fst).neg.add
      (hVt.measurable.comp (measurable_fst.snd.add measurable_snd.snd))).sub
      (hVt.measurable.comp measurable_fst.snd)
  have iIB : Integrable IB (Ξ η κ) := by
    refine hDB.mono' mIB.aestronglyMeasurable ?_
    filter_upwards [h.ae_goodSet] with z hz
    obtain ⟨-, -, hQ, -, -, hB, -⟩ := hz
    have hUq := E.U_le_ubar U hu hQ
    rw [Set.indicator_of_mem hQ] at hB
    simp only [IB, Set.indicator_of_mem hQ, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have iIS : Integrable IS (Ξ η κ) := by
    refine hDS.mono' mIS.aestronglyMeasurable ?_
    filter_upwards [h.ae_goodSet] with z hz
    obtain ⟨-, -, hQ, -, -, -, hS⟩ := hz
    have hKq := E.K_nonneg hQ
    rw [Set.indicator_of_mem hQ] at hS
    simp only [IS, Set.indicator_of_mem hQ, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- Fubini: the iterated integrals are `η`-integrable
  have hF : Integrable (fun m => ∫ s, (∫ x, IB ((m, s), x) ∂κ (m, s)) ∂η) η :=
    (integrable_integral_compProd iIB).integral_prod_left
  have hG : Integrable (fun m => ∫ b, (∫ x, IS ((b, m), x) ∂κ (b, m)) ∂η) η :=
    (integrable_integral_compProd iIS).integral_prod_right
  -- `eq:generalbellman` identifies `V` with them `η`-a.e.
  have hV : V =ᵐ[η] fun m => E.π / E.r * ((∫ s, (∫ x, IB ((m, s), x) ∂κ (m, s)) ∂η) +
      ∫ b, (∫ x, IS ((b, m), x) ∂κ (b, m)) ∂η) := by
    filter_upwards [h.ae_nonneg] with m hm
    have hb := h.bellman m hm
    have e1 : ∫ s, (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η =
        ∫ s, (∫ x, IB ((m, s), x) ∂κ (m, s)) ∂η := by
      refine integral_congr_ae ?_
      filter_upwards [h.ae_nonneg] with s hs
      refine integral_congr_ae ?_
      filter_upwards [h.ae_mem_bargainSet hm hs] with x hx
      obtain ⟨hQ, -, hdb, -, -⟩ := hx.1
      simp only [IB, Jb, Set.indicator_of_mem hQ, posPart_eq hm, posPart_eq (sub_nonneg.2 hdb)]
    have e2 : ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η =
        ∫ b, (∫ x, IS ((b, m), x) ∂κ (b, m)) ∂η := by
      refine integral_congr_ae ?_
      filter_upwards [h.ae_nonneg] with b hb
      refine integral_congr_ae ?_
      filter_upwards [h.ae_mem_bargainSet hb hm] with x hx
      obtain ⟨hQ, hd0, -, -, -⟩ := hx.1
      simp only [IS, Js, Set.indicator_of_mem hQ, posPart_eq hm, posPart_eq (add_nonneg hm hd0)]
    rw [e1, e2] at hb
    have hr := E.r_pos
    field_simp
    linarith
  exact ((hF.add hG).const_mul _).congr hV.symm

/-! ### Step 3: the a.e. bound `V ≤ ū/σ` -/

/-- The one-period buyer transition applied to `(V - c)₊`:
`m ↦ ∫∫ (V(m - d) - c)₊ dκ_{m,s}(q,d) dη(s)`. -/
private def PB (V : ℝ → ℝ) (c : ℝ) (η : Measure ℝ) (κ : Kernel (ℝ × ℝ) (ℝ × ℝ)) (m : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2) - c) ∂κ (m, s) ∂η

/-- The one-period seller transition applied to `(V - c)₊`:
`m ↦ ∫∫ (V(m + d) - c)₊ dκ_{b,m}(q,d) dη(b)`. -/
private def PS (V : ℝ → ℝ) (c : ℝ) (η : Measure ℝ) (κ : Kernel (ℝ × ℝ) (ℝ × ℝ)) (m : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ b, ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2) - c) ∂κ (b, m) ∂η

/-- Buyer side of `eq:generalbellman` at `m, s ≥ 0`, with `U(q) ≤ ū`:
`∫ (J^b - V(m)) dκ_{m,s} + V(m) ≤ ū + ∫ V(m - d) dκ_{m,s}` (as `ℝ≥0∞`-valued integrals; the
inequality is trivial if the Bochner integral is undefined). -/
private lemma buyer_inner_le (U : AdmissibleUtility) (hu : U.u = E.u)
    (h : E.IsGeneralEquilibrium θ T M V η κ) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) + ENNReal.ofReal (V m) ≤
      ENNReal.ofReal U.ubar + ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) := by
  have := h.markov
  have hmem := h.ae_mem_bargainSet hm hs
  have hV0 := h.V_nonneg m hm
  have hVt0 := h.posPart_nonneg
  have h0 : 0 ≤ᵐ[κ (m, s)] fun x => E.Jb V m s x.1 x.2 - V m := by
    filter_upwards [hmem] with x hx
    exact sub_nonneg.2 hx.1.2.2.2.1
  have h1 : ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ≤
      ∫⁻ x, ENNReal.ofReal (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s) := by
    by_cases hfi : Integrable (fun x => E.Jb V m s x.1 x.2 - V m) (κ (m, s))
    · exact (ofReal_integral_eq_lintegral_ofReal hfi h0).le
    · rw [integral_undef hfi, ENNReal.ofReal_zero]
      apply zero_le
  calc ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) + ENNReal.ofReal (V m)
      ≤ ∫⁻ x, ENNReal.ofReal (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s) +
          ∫⁻ _x, ENNReal.ofReal (V m) ∂κ (m, s) := by
        rw [lintegral_const, measure_univ, mul_one]
        exact add_le_add h1 le_rfl
    _ = ∫⁻ x, (ENNReal.ofReal (E.Jb V m s x.1 x.2 - V m) + ENNReal.ofReal (V m)) ∂κ (m, s) :=
        (lintegral_add_right _ measurable_const).symm
    _ ≤ ∫⁻ x, (ENNReal.ofReal U.ubar + ENNReal.ofReal (posPart V (m - x.2))) ∂κ (m, s) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hmem] with x hx
        obtain ⟨hQ, -, hdb, hB, -⟩ := hx.1
        rw [← ENNReal.ofReal_add (sub_nonneg.2 hB) hV0,
          ← ENNReal.ofReal_add U.ubar_pos.le (hVt0 (m - x.2))]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [posPart_eq (sub_nonneg.2 hdb)]
        have := E.U_le_ubar U hu hQ
        simp only [Jb]
        linarith
    _ = ENNReal.ofReal U.ubar + ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- Seller side of `eq:generalbellman` at `b, m ≥ 0`, dropping the production cost `K(q) ≥ 0`:
`∫ (J^s - V(m)) dκ_{b,m} + V(m) ≤ ∫ V(m + d) dκ_{b,m}`. -/
private lemma seller_inner_le (h : E.IsGeneralEquilibrium θ T M V η κ) {b m : ℝ} (hb : 0 ≤ b)
    (hm : 0 ≤ m) :
    ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) + ENNReal.ofReal (V m) ≤
      ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) := by
  have := h.markov
  have hmem := h.ae_mem_bargainSet hb hm
  have hV0 := h.V_nonneg m hm
  have h0 : 0 ≤ᵐ[κ (b, m)] fun x => E.Js V b m x.1 x.2 - V m := by
    filter_upwards [hmem] with x hx
    exact sub_nonneg.2 hx.1.2.2.2.2
  have h1 : ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ≤
      ∫⁻ x, ENNReal.ofReal (E.Js V b m x.1 x.2 - V m) ∂κ (b, m) := by
    by_cases hfi : Integrable (fun x => E.Js V b m x.1 x.2 - V m) (κ (b, m))
    · exact (ofReal_integral_eq_lintegral_ofReal hfi h0).le
    · rw [integral_undef hfi, ENNReal.ofReal_zero]
      apply zero_le
  calc ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) + ENNReal.ofReal (V m)
      ≤ ∫⁻ x, ENNReal.ofReal (E.Js V b m x.1 x.2 - V m) ∂κ (b, m) +
          ∫⁻ _x, ENNReal.ofReal (V m) ∂κ (b, m) := by
        rw [lintegral_const, measure_univ, mul_one]
        exact add_le_add h1 le_rfl
    _ = ∫⁻ x, (ENNReal.ofReal (E.Js V b m x.1 x.2 - V m) + ENNReal.ofReal (V m)) ∂κ (b, m) :=
        (lintegral_add_right _ measurable_const).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hmem] with x hx
        obtain ⟨hQ, hd0, -, -, hS⟩ := hx.1
        rw [← ENNReal.ofReal_add (sub_nonneg.2 hS) hV0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [posPart_eq (add_nonneg hm hd0)]
        have := E.K_nonneg hQ
        simp only [Js]
        linarith

/-- `eq:generalbellman` at `m ≥ 0` with production costs dropped and `U ≤ ū`:
`(r + 2π) V(m) ≤ π ū + π ∫∫ V(m-d) dκ_{m,s} dη(s) + π ∫∫ V(m+d) dκ_{b,m} dη(b)`, i.e.
`(1 + r) V(m) ≤ (P V)(m) + π ū` for the one-period wealth transition `P`. -/
private lemma bellman_le (U : AdmissibleUtility) (hu : U.u = E.u)
    (h : E.IsGeneralEquilibrium θ T M V η κ) {m : ℝ} (hm : 0 ≤ m) :
    ENNReal.ofReal ((E.r + 2 * E.π) * V m) ≤
      ENNReal.ofReal E.π * (ENNReal.ofReal U.ubar +
        ∫⁻ s, ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) ∂η +
        ∫⁻ b, ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) ∂η) := by
  have := h.isProb_η
  have := h.markov
  have hV0 := h.V_nonneg m hm
  have hπ := E.π_pos
  have hr := E.r_pos
  have hA0 : 0 ≤ᵐ[η] fun s => ∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s) := by
    filter_upwards [h.ae_nonneg] with s hs
    refine integral_nonneg_of_ae ?_
    filter_upwards [h.ae_mem_bargainSet hm hs] with x hx
    exact sub_nonneg.2 hx.1.2.2.2.1
  have hC0 : 0 ≤ᵐ[η] fun b => ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m) := by
    filter_upwards [h.ae_nonneg] with b hb
    refine integral_nonneg_of_ae ?_
    filter_upwards [h.ae_mem_bargainSet hb hm] with x hx
    exact sub_nonneg.2 hx.1.2.2.2.2
  have hA := integral_nonneg_of_ae hA0
  have hC := integral_nonneg_of_ae hC0
  have e1 := ofReal_integral_eq_lintegral_ofReal (h.bellman_integrable_b m hm) hA0
  have e2 := ofReal_integral_eq_lintegral_ofReal (h.bellman_integrable_s m hm) hC0
  -- the integrated inner bounds
  have hB : ∫⁻ s, ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η +
      ENNReal.ofReal (V m) ≤ ENNReal.ofReal U.ubar +
        ∫⁻ s, ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) ∂η := by
    calc ∫⁻ s, ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η +
          ENNReal.ofReal (V m)
        = ∫⁻ s, (ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) +
            ENNReal.ofReal (V m)) ∂η := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ s, (ENNReal.ofReal U.ubar +
            ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s)) ∂η := by
          refine lintegral_mono_ae ?_
          filter_upwards [h.ae_nonneg] with s hs
          exact buyer_inner_le U hu h hm hs
      _ = _ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have hS : ∫⁻ b, ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η +
      ENNReal.ofReal (V m) ≤
        ∫⁻ b, ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) ∂η := by
    calc ∫⁻ b, ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η +
          ENNReal.ofReal (V m)
        = ∫⁻ b, (ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) +
            ENNReal.ofReal (V m)) ∂η := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [h.ae_nonneg] with b hb
          exact seller_inner_le h hb hm
  -- assemble, using `eq:generalbellman`
  calc ENNReal.ofReal ((E.r + 2 * E.π) * V m)
      = ENNReal.ofReal (E.r * V m) + ENNReal.ofReal E.π * ENNReal.ofReal (V m) +
          ENNReal.ofReal E.π * ENNReal.ofReal (V m) := by
        rw [← ENNReal.ofReal_mul hπ.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal E.π * ∫⁻ s, ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η
          + ENNReal.ofReal E.π *
            ∫⁻ b, ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η
          + ENNReal.ofReal E.π * ENNReal.ofReal (V m)
          + ENNReal.ofReal E.π * ENNReal.ofReal (V m) := by
        rw [h.bellman m hm, ENNReal.ofReal_add (mul_nonneg hπ.le hA) (mul_nonneg hπ.le hC),
          ENNReal.ofReal_mul hπ.le, ENNReal.ofReal_mul hπ.le, e1, e2]
    _ = ENNReal.ofReal E.π *
          (∫⁻ s, ENNReal.ofReal (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η +
            ENNReal.ofReal (V m)) +
        ENNReal.ofReal E.π *
          (∫⁻ b, ENNReal.ofReal (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η +
            ENNReal.ofReal (V m)) := by ring
    _ ≤ ENNReal.ofReal E.π * (ENNReal.ofReal U.ubar +
          ∫⁻ s, ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) ∂η) +
        ENNReal.ofReal E.π *
          ∫⁻ b, ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) ∂η := by
        gcongr
    _ = _ := by ring

/-- The buyer transition of `V` is at most that of `(V - c)₊`, plus `c`. -/
private lemma PB_shift (h : E.IsGeneralEquilibrium θ T M V η κ) (c : ℝ) (m : ℝ) :
    ∫⁻ s, ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) ∂η ≤
      PB V c η κ m + ENNReal.ofReal c := by
  have := h.isProb_η
  have := h.markov
  calc ∫⁻ s, ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) ∂η
      ≤ ∫⁻ s, ((∫⁻ x, ENNReal.ofReal (posPart V (m - x.2) - c) ∂κ (m, s)) +
          ENNReal.ofReal c) ∂η :=
        lintegral_mono fun s => lintegral_ofReal_le_shift _ _ c
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        rfl

/-- The seller transition of `V` is at most that of `(V - c)₊`, plus `c`. -/
private lemma PS_shift (h : E.IsGeneralEquilibrium θ T M V η κ) (c : ℝ) (m : ℝ) :
    ∫⁻ b, ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) ∂η ≤
      PS V c η κ m + ENNReal.ofReal c := by
  have := h.isProb_η
  have := h.markov
  calc ∫⁻ b, ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) ∂η
      ≤ ∫⁻ b, ((∫⁻ x, ENNReal.ofReal (posPart V (m + x.2) - c) ∂κ (b, m)) +
          ENNReal.ofReal c) ∂η :=
        lintegral_mono fun b => lintegral_ofReal_le_shift _ _ c
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        rfl

/-- The supersolution inequality for `W = (V - c)₊`, `c = ū/σ`: for `m ≥ 0`,
`(r + 2π) W(m) ≤ π [(P_b W)(m) + (P_s W)(m)]`, i.e. `(1 + r) W ≤ P W`. Uses `rc = πū` and
positivity of the transition. -/
private lemma W_ineq (U : AdmissibleUtility) (hu : U.u = E.u)
    (h : E.IsGeneralEquilibrium θ T M V η κ) {m : ℝ} (hm : 0 ≤ m) :
    ENNReal.ofReal (E.r + 2 * E.π) * ENNReal.ofReal (V m - U.ubar / E.σ) ≤
      ENNReal.ofReal E.π * (PB V (U.ubar / E.σ) η κ m + PS V (U.ubar / E.σ) η κ m) := by
  have hπ := E.π_pos
  have hr := E.r_pos
  have hū := U.ubar_pos
  have hc : 0 ≤ U.ubar / E.σ := div_nonneg hū.le E.σ_pos.le
  have hrc : E.r * (U.ubar / E.σ) = E.π * U.ubar := by
    rw [σ]
    field_simp
  rw [← ENNReal.ofReal_mul (by positivity), mul_sub, ENNReal.ofReal_sub _ (by positivity),
    tsub_le_iff_right]
  calc ENNReal.ofReal ((E.r + 2 * E.π) * V m)
      ≤ ENNReal.ofReal E.π * (ENNReal.ofReal U.ubar +
          ∫⁻ s, ∫⁻ x, ENNReal.ofReal (posPart V (m - x.2)) ∂κ (m, s) ∂η +
          ∫⁻ b, ∫⁻ x, ENNReal.ofReal (posPart V (m + x.2)) ∂κ (b, m) ∂η) :=
        bellman_le U hu h hm
    _ ≤ ENNReal.ofReal E.π * (ENNReal.ofReal U.ubar +
          (PB V (U.ubar / E.σ) η κ m + ENNReal.ofReal (U.ubar / E.σ)) +
          (PS V (U.ubar / E.σ) η κ m + ENNReal.ofReal (U.ubar / E.σ))) := by
        gcongr
        · exact PB_shift h _ m
        · exact PS_shift h _ m
    _ = ENNReal.ofReal E.π * (PB V (U.ubar / E.σ) η κ m + PS V (U.ubar / E.σ) η κ m) +
          ENNReal.ofReal E.π * (ENNReal.ofReal U.ubar + ENNReal.ofReal (U.ubar / E.σ) +
            ENNReal.ofReal (U.ubar / E.σ)) := by ring
    _ = ENNReal.ofReal E.π * (PB V (U.ubar / E.σ) η κ m + PS V (U.ubar / E.σ) η κ m) +
          ENNReal.ofReal ((E.r + 2 * E.π) * (U.ubar / E.σ)) := by
        congr 1
        rw [← ENNReal.ofReal_add hū.le hc, ← ENNReal.ofReal_add (by positivity) hc,
          ← ENNReal.ofReal_mul hπ.le]
        congr 1
        linear_combination (-1 : ℝ) * hrc

/-- Fubini for the buyer transition: `∫ P_b W dη = ∫ W(B) dΞ`. -/
private lemma lintegral_PB (h : E.IsGeneralEquilibrium θ T M V η κ) (c : ℝ) :
    ∫⁻ m, PB V c η κ m ∂η =
      ∫⁻ z, ENNReal.ofReal (posPart V (z.1.1 - z.2.2) - c) ∂(Ξ η κ) := by
  have := h.isProb_η
  have := h.markov
  have hVt : Continuous (posPart V) := continuous_posPart h.V_cont
  have hf : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (posPart V (z.1.1 - z.2.2) - c) :=
    ENNReal.measurable_ofReal.comp
      ((hVt.measurable.comp (measurable_fst.fst.sub measurable_snd.snd)).sub measurable_const)
  rw [Ξ, Measure.lintegral_compProd hf,
    lintegral_prod _ (Measurable.lintegral_kernel_prod_right' hf).aemeasurable]
  rfl

/-- Fubini for the seller transition: `∫ P_s W dη = ∫ W(S) dΞ`. -/
private lemma lintegral_PS (h : E.IsGeneralEquilibrium θ T M V η κ) (c : ℝ) :
    ∫⁻ m, PS V c η κ m ∂η =
      ∫⁻ z, ENNReal.ofReal (posPart V (z.1.2 + z.2.2) - c) ∂(Ξ η κ) := by
  have := h.isProb_η
  have := h.markov
  have hVt : Continuous (posPart V) := continuous_posPart h.V_cont
  have hf : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (posPart V (z.1.2 + z.2.2) - c) :=
    ENNReal.measurable_ofReal.comp
      ((hVt.measurable.comp (measurable_fst.snd.add measurable_snd.snd)).sub measurable_const)
  rw [Ξ, Measure.lintegral_compProd hf,
    lintegral_prod_symm _ (Measurable.lintegral_kernel_prod_right' hf).aemeasurable]
  rfl

/-- `eq:generalstationarity` for nonnegative Borel `g`: `∫ g(B) dΞ + ∫ g(S) dΞ = 2 ∫ g dη`. -/
private lemma lintegral_stationary (h : E.IsGeneralEquilibrium θ T M V η κ) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z, g (z.1.1 - z.2.2) ∂(Ξ η κ) + ∫⁻ z, g (z.1.2 + z.2.2) ∂(Ξ η κ) = 2 * ∫⁻ y, g y ∂η := by
  have mB : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 - z.2.2 :=
    measurable_fst.fst.sub measurable_snd.snd
  have mS : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 + z.2.2 :=
    measurable_fst.snd.add measurable_snd.snd
  have e : ∫⁻ y, g y ∂η =
      2⁻¹ * ∫⁻ z, g (z.1.1 - z.2.2) ∂(Ξ η κ) + 2⁻¹ * ∫⁻ z, g (z.1.2 + z.2.2) ∂(Ξ η κ) := by
    conv_lhs => rw [h.stationary]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_map hg mB, lintegral_map hg mS, smul_eq_mul, smul_eq_mul]
  rw [e, mul_add, ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero
    ENNReal.ofNat_ne_top, one_mul, one_mul]

/-- `lem:stationaryvaluebound`: `V(m) ≤ ū/σ` for `η`-almost every `m`. With `W = (V - ū/σ)₊`,
the supersolution inequality `W_ineq` integrates (Fubini and `eq:generalstationarity`) to
`(r + 2π) ∫ W dη ≤ 2π ∫ W dη`; since `∫ W dη ≤ ∫ V dη < ∞` (`integrable_value`) and `r > 0`,
`∫ W dη = 0`. -/
theorem value_le_ae (U : AdmissibleUtility) (hu : U.u = E.u)
    {θ : ℝ} {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ} {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    (h : E.IsGeneralEquilibrium θ T M V η κ) : ∀ᵐ m ∂η, V m ≤ U.ubar / E.σ := by
  have := h.isProb_η
  have := h.markov
  have hint := h.integrable_value U hu
  have hVt : Continuous (posPart V) := continuous_posPart h.V_cont
  have hc : 0 ≤ U.ubar / E.σ := div_nonneg U.ubar_pos.le E.σ_pos.le
  have mW : Measurable fun y => ENNReal.ofReal (posPart V y - U.ubar / E.σ) :=
    ENNReal.measurable_ofReal.comp (hVt.sub continuous_const).measurable
  have hWV : (fun m => ENNReal.ofReal (V m - U.ubar / E.σ)) =ᵐ[η]
      fun y => ENNReal.ofReal (posPart V y - U.ubar / E.σ) := by
    filter_upwards [h.ae_nonneg] with m hm
    rw [posPart_eq hm]
  -- `∫ W dη < ∞`
  have hI : ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η < ∞ := by
    calc ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η
        = ∫⁻ m, ENNReal.ofReal (V m - U.ubar / E.σ) ∂η := (lintegral_congr_ae hWV).symm
      _ ≤ ∫⁻ m, ‖V m‖ₑ ∂η :=
          lintegral_mono fun m =>
            (ENNReal.ofReal_le_ofReal (by linarith)).trans (Real.ofReal_le_enorm _)
      _ < ∞ := hint.hasFiniteIntegral
  -- measurability of the transitions
  have mPB : Measurable (PB V (U.ubar / E.σ) η κ) := by
    have : Measurable fun p : ℝ × ℝ =>
        ∫⁻ x, ENNReal.ofReal (posPart V (p.1 - x.2) - U.ubar / E.σ) ∂κ p :=
      Measurable.lintegral_kernel_prod_right'
        (mW.comp (measurable_fst.fst.sub measurable_snd.snd))
    exact this.lintegral_prod_right'
  have mPS : Measurable (PS V (U.ubar / E.σ) η κ) := by
    have : Measurable fun p : ℝ × ℝ =>
        ∫⁻ x, ENNReal.ofReal (posPart V (p.2 + x.2) - U.ubar / E.σ) ∂κ p :=
      Measurable.lintegral_kernel_prod_right'
        (mW.comp (measurable_fst.snd.add measurable_snd.snd))
    exact this.lintegral_prod_left'
  -- integrate the supersolution inequality
  have key : ENNReal.ofReal (E.r + 2 * E.π) *
      ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η ≤
      ENNReal.ofReal E.π * (2 * ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η) := by
    calc ENNReal.ofReal (E.r + 2 * E.π) * ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η
        = ∫⁻ m, ENNReal.ofReal (E.r + 2 * E.π) * ENNReal.ofReal (V m - U.ubar / E.σ) ∂η := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_congr_ae hWV]
      _ ≤ ∫⁻ m, ENNReal.ofReal E.π *
            (PB V (U.ubar / E.σ) η κ m + PS V (U.ubar / E.σ) η κ m) ∂η := by
          refine lintegral_mono_ae ?_
          filter_upwards [h.ae_nonneg] with m hm
          exact W_ineq U hu h hm
      _ = ENNReal.ofReal E.π *
            (∫⁻ m, PB V (U.ubar / E.σ) η κ m ∂η + ∫⁻ m, PS V (U.ubar / E.σ) η κ m ∂η) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left mPB]
      _ = _ := by rw [lintegral_PB h, lintegral_PS h, lintegral_stationary h mW]
  -- hence `∫ W dη = 0`
  have hI0 : ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η = 0 := by
    by_contra hne
    have hlt : ENNReal.ofReal E.π * (2 * ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η) <
        ENNReal.ofReal (E.r + 2 * E.π) *
          ∫⁻ y, ENNReal.ofReal (posPart V y - U.ubar / E.σ) ∂η := by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal E.π * 2), mul_comm (ENNReal.ofReal (E.r + 2 * E.π))]
      refine ENNReal.mul_lt_mul_right hne hI.ne ?_
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul E.π_pos.le]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [E.r_pos, E.π_pos])).2
        (by linarith [E.r_pos])
    exact absurd key (not_le.2 hlt)
  have hW0 := (lintegral_eq_zero_iff mW).1 hI0
  filter_upwards [hW0, h.ae_nonneg] with m hm hm0
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero, posPart_eq hm0] at hm
  linarith

/-- `lem:stationaryvaluebound`: `V(m) ≤ ū/σ` for every `m ≥ 0` in the support of `η`, i.e. every
`m ≥ 0` all of whose neighbourhoods have positive `η`-measure (by continuity of `V`). -/
theorem value_le_of_mem_support (U : AdmissibleUtility) (hu : U.u = E.u)
    {θ : ℝ} {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ} {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    (h : E.IsGeneralEquilibrium θ T M V η κ) {m : ℝ} (hm : 0 ≤ m)
    (hsupp : ∀ ε > 0, η (Metric.ball m ε) ≠ 0) : V m ≤ U.ubar / E.σ := by
  by_contra hlt
  rw [not_le] at hlt
  -- `V > ū/σ` on a relative neighbourhood of `m` in `[0, ∞)`
  have hev : ∀ᶠ y in 𝓝[Ici 0] m, U.ubar / E.σ < V y :=
    (h.V_cont m hm).eventually (lt_mem_nhds hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  apply hsupp ε hε
  have hae := h.value_le_ae U hu
  rw [ae_iff] at hae
  have h1 : η (Metric.ball m ε ∩ Ici 0) = 0 :=
    measure_mono_null (fun y hy => not_le.2 (hball hy)) hae
  have h2 : Metric.ball m ε ⊆ (Metric.ball m ε ∩ Ici 0) ∪ Iio 0 := fun y hy => by
    by_cases hy0 : 0 ≤ y
    · exact Or.inl ⟨hy, hy0⟩
    · exact Or.inr (not_le.1 hy0)
  exact measure_mono_null h2 (measure_union_null h1 h.η_nonneg)

end IsGeneralEquilibrium

end Molico.Environment
