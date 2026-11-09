import MonetaryExistenceBuyer.Limit.Basic
import MonetaryExistenceBuyer.Prelim.Device
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Semicontinuity.Basic

/-!
# A toolkit for weak convergence (`WeakConv`)

Used throughout §4–§6: conversion to Mathlib's `ProbabilityMeasure` topology, Portmanteau,
continuous mapping, products, uniqueness of limits, upper semicontinuous integrands
(Billingsley, Problem 2.6), integrands continuous on a closed carrier, `lem:device` (b), and
Prokhorov extraction for tight sequences.

Standing assumptions on the state space `X`: Borel, pseudo-metrizable, second countable
(true for `ℝ`, `ℝ³`, `ℝ≥0∞ × ℝ`, `ℝ≥0∞⁵`).
-/

open Set Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

noncomputable section

namespace Molico

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [PseudoMetrizableSpace X] [SecondCountableTopology X]

set_option linter.unusedSectionVars false

/-- A probability measure as an element of `ProbabilityMeasure X`. -/
def toPM {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (hμ : IsProbabilityMeasure μ) :
    ProbabilityMeasure Y := ⟨μ, hμ⟩

@[simp] theorem toPM_toMeasure {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (hμ : IsProbabilityMeasure μ) : ((toPM μ hμ : ProbabilityMeasure Y) : Measure Y) = μ := rfl

/-- `weakConv_iff_tendsto` on an arbitrary space with opens measurable. -/
theorem weakConv_iff_tendsto_of_opens {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {μs : ℕ → Measure Y} {μ : Measure Y}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) :
    WeakConv μs μ ↔ Tendsto (fun n => toPM (μs n) (hμs n)) atTop (𝓝 (toPM μ hμ)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  rfl

/-- `WeakConv` is convergence in Mathlib's topology of `ProbabilityMeasure`. -/
theorem weakConv_iff_tendsto {μs : ℕ → Measure X} {μ : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) :
    WeakConv μs μ ↔ Tendsto (fun n => toPM (μs n) (hμs n)) atTop (𝓝 (toPM μ hμ)) :=
  weakConv_iff_tendsto_of_opens hμs hμ


theorem WeakConv.comp {μs : ℕ → Measure X} {μ : Measure X} (h : WeakConv μs μ) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : WeakConv (fun n => μs (φ n)) μ := by
  intro f; exact (h f).comp hφ.tendsto_atTop

/-- The weak limit of probability measures is a probability measure... -/
theorem WeakConv.isProbabilityMeasure {μs : ℕ → Measure X} {μ : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsFiniteMeasure μ) (h : WeakConv μs μ) :
    IsProbabilityMeasure μ := by
  have h1 := h (BoundedContinuousFunction.const X (1 : ℝ))
  have hconst : ∀ n, ∫ _x, (BoundedContinuousFunction.const X (1 : ℝ)) _x ∂μs n = 1 := by
    intro n
    have := hμs n
    simp
  simp only [hconst] at h1
  have h2 : ∫ _x, (BoundedContinuousFunction.const X (1 : ℝ)) _x ∂μ = 1 :=
    tendsto_nhds_unique h1 tendsto_const_nhds
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    measureReal_def] at h2
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 h2⟩

/-- ... and it is unique. -/
theorem WeakConv.unique {μs : ℕ → Measure X} {μ ν : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ)
    (hν : IsProbabilityMeasure ν) (h1 : WeakConv μs μ) (h2 : WeakConv μs ν) : μ = ν := by
  have := hμ; have := hν
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => tendsto_nhds_unique (h1 f) (h2 f)

/-- Portmanteau, closed sets: eventual lower bounds pass to the limit. -/
theorem WeakConv.le_measure_closed {μs : ℕ → Measure X} {μ : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) (h : WeakConv μs μ)
    {C : Set X} (hC : IsClosed C) {c : ℝ≥0∞} (hc : ∀ᶠ n in atTop, c ≤ μs n C) : c ≤ μ C := by
  have ht := (weakConv_iff_tendsto hμs hμ).1 h
  have hl := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto ht hC
  simp only [toPM_toMeasure] at hl
  exact (le_limsup_of_frequently_le' hc.frequently).trans hl

/-- Portmanteau, open sets: eventual upper bounds pass to the limit. -/
theorem WeakConv.measure_open_le {μs : ℕ → Measure X} {μ : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) (h : WeakConv μs μ)
    {U : Set X} (hU : IsOpen U) {c : ℝ≥0∞} (hc : ∀ᶠ n in atTop, μs n U ≤ c) : μ U ≤ c := by
  have ht := (weakConv_iff_tendsto hμs hμ).1 h
  have hl := ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht hU
  simp only [toPM_toMeasure] at hl
  exact hl.trans (liminf_le_of_frequently_le' hc.frequently)

/-- `lem:device` (b) for `WeakConv`: if `μ_n` is carried by `E_n`, the limit is carried by
`E_∞ = ⋂_k closure (⋃_{n ≥ k} E_n)`. -/
theorem WeakConv.measure_compl_limsup {μs : ℕ → Measure X} {μ : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) (h : WeakConv μs μ)
    {E : ℕ → Set X} (hE : ∀ n, μs n (E n)ᶜ = 0) : μ (⋂ k, closure (⋃ n ≥ k, E n))ᶜ = 0 := by
  have hk : ∀ k, μ (closure (⋃ n ≥ k, E n))ᶜ = 0 := by
    intro k
    have hcl : IsClosed (closure (⋃ n ≥ k, E n)) := isClosed_closure
    have h1 : (1 : ℝ≥0∞) ≤ μ (closure (⋃ n ≥ k, E n)) := by
      refine h.le_measure_closed hμs hμ hcl ?_
      filter_upwards [eventually_ge_atTop k] with n hn
      have := hμs n
      have h0 : μs n (closure (⋃ n ≥ k, E n))ᶜ = 0 :=
        measure_mono_null
          (compl_subset_compl.2 ((subset_biUnion_of_mem (u := E) hn).trans subset_closure))
          (hE n)
      rw [(prob_compl_eq_zero_iff hcl.measurableSet).1 h0]
    have := hμ
    exact (prob_compl_eq_zero_iff hcl.measurableSet).2 (le_antisymm prob_le_one h1)
  rw [compl_iInter]
  exact measure_iUnion_null hk

/-- Continuous mapping. -/
theorem WeakConv.map {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μs : ℕ → Measure X} {μ : Measure X} (hμs : ∀ n, IsProbabilityMeasure (μs n))
    (hμ : IsProbabilityMeasure μ) (h : WeakConv μs μ) {f : X → Y} (hf : Continuous f) :
    WeakConv (fun n => (μs n).map f) (μ.map f) := by
  intro g
  have key : ∀ ν : Measure X,
      ∫ y, g y ∂(ν.map f) = ∫ x, (g.compContinuous ⟨f, hf⟩) x ∂ν := by
    intro ν
    rw [integral_map hf.measurable.aemeasurable g.continuous.aestronglyMeasurable]
    rfl
  simp only [key]
  exact h _

/-- Products. -/
theorem WeakConv.prod {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [PseudoMetrizableSpace Y] [SecondCountableTopology Y]
    {μs : ℕ → Measure X} {μ : Measure X} {νs : ℕ → Measure Y} {ν : Measure Y}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ)
    (hνs : ∀ n, IsProbabilityMeasure (νs n)) (hν : IsProbabilityMeasure ν)
    (h1 : WeakConv μs μ) (h2 : WeakConv νs ν) :
    WeakConv (fun n => (μs n).prod (νs n)) (μ.prod ν) := by
  have := hμ; have := hν
  have hp : ∀ n, IsProbabilityMeasure ((μs n).prod (νs n)) := fun n => by
    have := hμs n; have := hνs n; infer_instance
  rw [weakConv_iff_tendsto_of_opens hp inferInstance]
  have t1 := (weakConv_iff_tendsto hμs hμ).1 h1
  have t2 := (weakConv_iff_tendsto hνs hν).1 h2
  exact (ProbabilityMeasure.continuous_prod.tendsto (toPM μ hμ, toPM ν hν)).comp
    (t1.prodMk_nhds t2)

/-- The layer-cake form of Portmanteau for nonnegative lower semicontinuous integrands. -/
theorem lintegral_le_liminf_lintegral_of_lsc {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} {μs : ℕ → Measure Ω} {f : Ω → ℝ}
    (hf : LowerSemicontinuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(μs i)) := by
  have hmeas : Measurable f := hf.measurable
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) hmeas.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a}) :=
        lintegral_mono (fun t ↦ h_opens _ (hf.isOpen_preimage t))
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a}) :=
        lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

/-- Upper semicontinuous bounded integrands (Billingsley, Problem 2.6):
`limsup ∫ f dμ_n ≤ ∫ f dμ`, in the form: eventually `∫ f dμ_n ≤ ∫ f dμ + ε`. -/
theorem WeakConv.eventually_integral_le_of_usc {μs : ℕ → Measure X} {μ : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) (h : WeakConv μs μ)
    {f : X → ℝ} (hf : UpperSemicontinuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in atTop, ∫ x, f x ∂μs n ≤ ∫ x, f x ∂μ + ε := by
  have ht := (weakConv_iff_tendsto hμs hμ).1 h
  have h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G) := fun G hG => by
    simpa using ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht hG
  set g : X → ℝ := fun x => C - f x with hg_def
  have hg_lsc : LowerSemicontinuous g := fun x y hy =>
    (hf x (C - y) (by simp only [hg_def] at hy; linarith)).mono fun x' hx' => by
      simp only [hg_def]; linarith
  have hg_nn : 0 ≤ g := fun x => by
    simp only [hg_def, Pi.zero_apply]; linarith [(abs_le.1 (hC x)).2]
  have hf_meas : Measurable f := hf.measurable
  have hf_int : ∀ ν : Measure X, IsProbabilityMeasure ν → Integrable f ν := fun ν hν =>
    Integrable.of_bound hf_meas.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hg_int : ∀ ν : Measure X, IsProbabilityMeasure ν → Integrable g ν := fun ν hν =>
    (integrable_const C).sub (hf_int ν hν)
  have hlin : ∀ ν : Measure X, IsProbabilityMeasure ν →
      ∫⁻ x, ENNReal.ofReal (g x) ∂ν = ENNReal.ofReal (C - ∫ x, f x ∂ν) := by
    intro ν hν
    rw [← ofReal_integral_eq_lintegral_ofReal (hg_int ν hν) (Eventually.of_forall hg_nn),
      hg_def, integral_sub (integrable_const C) (hf_int ν hν), integral_const]
    simp
  have key := lintegral_le_liminf_lintegral_of_lsc hg_lsc hg_nn h_opens
  rw [hlin μ hμ] at key
  have hfun : (fun i => ∫⁻ x, ENNReal.ofReal (g x) ∂μs i) =
      fun i => ENNReal.ofReal (C - ∫ x, f x ∂μs i) := funext fun i => hlin _ (hμs i)
  rw [hfun] at key
  have hfC : ∀ n, ∫ x, f x ∂μs n ≤ C := fun n => by
    have := hμs n
    calc ∫ x, f x ∂μs n ≤ ∫ _x, C ∂μs n :=
          integral_mono (hf_int _ (hμs n)) (integrable_const C) fun x => (abs_le.1 (hC x)).2
      _ = C := by simp
  by_cases hA : C - ∫ x, f x ∂μ - ε < 0
  · exact Eventually.of_forall fun n => by linarith [hfC n]
  · replace hA : 0 ≤ C - ∫ x, f x ∂μ - ε := not_lt.1 hA
    have hlt : ENNReal.ofReal (C - ∫ x, f x ∂μ - ε) < ENNReal.ofReal (C - ∫ x, f x ∂μ) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]; linarith
    filter_upwards [eventually_lt_of_lt_liminf (hlt.trans_le key)] with n hn
    rw [ENNReal.ofReal_lt_ofReal_iff'] at hn
    linarith [hn.1]

/-- Integrands continuous and bounded on a closed set carrying all the measures. -/
theorem WeakConv.tendsto_integral_of_continuousOn {μs : ℕ → Measure X} {μ : Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) (hμ : IsProbabilityMeasure μ) (h : WeakConv μs μ)
    {C : Set X} (hC : IsClosed C) (hμsC : ∀ n, μs n Cᶜ = 0) {f : X → ℝ} (hf : ContinuousOn f C)
    {B : ℝ} (hB : ∀ x ∈ C, |f x| ≤ B) :
    Tendsto (fun n => ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have := hμ
  have hμC : μ Cᶜ = 0 := by
    have h1 : (1 : ℝ≥0∞) ≤ μ C := h.le_measure_closed hμs hμ hC (Eventually.of_forall fun n => by
      have := hμs n
      rw [(prob_compl_eq_zero_iff hC.measurableSet).1 (hμsC n)])
    exact (prob_compl_eq_zero_iff hC.measurableSet).2 (le_antisymm prob_le_one h1)
  let F : BoundedContinuousFunction C ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (C.domRestrict f) hf.domRestrict B
      (fun x => by rw [Real.norm_eq_abs]; exact hB x x.2)
  obtain ⟨g, -, hg⟩ := BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed F hC
  have hgf : ∀ x ∈ C, g x = f x := fun x hx => by
    have := congrArg (fun G : BoundedContinuousFunction C ℝ => G ⟨x, hx⟩) hg
    simpa [F] using this
  have hae : ∀ ν : Measure X, ν Cᶜ = 0 → ∫ x, f x ∂ν = ∫ x, g x ∂ν := fun ν hν => by
    refine integral_congr_ae ?_
    have hCae : ∀ᵐ x ∂ν, x ∈ C := mem_ae_iff.2 hν
    filter_upwards [hCae] with x hx using (hgf x hx).symm
  have hfun : (fun n => ∫ x, f x ∂μs n) = fun n => ∫ x, g x ∂μs n :=
    funext fun n => hae _ (hμsC n)
  rw [hfun, hae μ hμC]
  exact h g

/-- Prokhorov extraction: a tight sequence of probability measures has a weakly convergent
subsequence. -/
theorem exists_subseq_weakConv {μs : ℕ → Measure X} (hμs : ∀ n, IsProbabilityMeasure (μs n))
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∀ n, μs n Kᶜ ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      WeakConv (fun n => μs (φ n)) μ := by
  classical
  -- Pass to the (Hausdorff) separation quotient `Q` of `X`, where Mathlib's Prokhorov applies.
  let Q := SeparationQuotient X
  let mQ : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  let mk : X → Q := SeparationQuotient.mk
  have hmk_cont : Continuous mk := SeparationQuotient.continuous_mk
  have hmk_meas : Measurable mk := hmk_cont.measurable
  -- every Borel set of `X` is the preimage of a Borel set of `Q`
  have hborel : borel X = MeasurableSpace.comap mk (borel Q) := by
    rw [borel, borel, MeasurableSpace.comap_generateFrom]
    congr 1
    ext U
    constructor
    · intro hU
      exact ⟨mk '' U, SeparationQuotient.isOpenMap_mk U hU,
        SeparationQuotient.preimage_image_mk_open hU⟩
    · rintro ⟨V, hV, rfl⟩
      exact hV.preimage hmk_cont
  have hpre : ∀ B : Set X, MeasurableSet B → ∃ A : Set Q, MeasurableSet A ∧ mk ⁻¹' A = B := by
    intro B hB
    have hB' : MeasurableSet[borel X] B := by rw [← BorelSpace.measurable_eq]; exact hB
    rw [hborel] at hB'
    exact MeasurableSpace.measurableSet_comap.1 hB'
  -- a measurable section of `mk`
  let s : Q → X := Function.surjInv SeparationQuotient.surjective_mk
  have hs : ∀ q, mk (s q) = q := Function.surjInv_eq _
  have hs_meas : Measurable s := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := hpre B hB
    have hsA : s ⁻¹' (mk ⁻¹' A) = A := by ext q; simp [hs]
    rw [hsA]; exact hA
  have hsmk : ∀ ν : Measure X, (ν.map mk).map s = ν := by
    intro ν
    rw [Measure.map_map hs_meas hmk_meas]
    ext B hB
    rw [Measure.map_apply (hs_meas.comp hmk_meas) hB]
    obtain ⟨A, hA, rfl⟩ := hpre B hB
    congr 1
    ext x; simp [hs]
  -- bounded continuous functions on `X` descend to `Q`
  have hlift : ∀ f : BoundedContinuousFunction X ℝ, Continuous (fun q => f (s q)) := by
    intro f
    rw [SeparationQuotient.isQuotientMap_mk.continuous_iff]
    have hfs : (fun q => f (s q)) ∘ SeparationQuotient.mk = f := by
      funext x
      have hin : Inseparable (s (mk x)) x := SeparationQuotient.mk_eq_mk.1 (hs (mk x))
      exact (hin.map f.continuous).eq
    rw [hfs]; exact f.continuous
  let gf : BoundedContinuousFunction X ℝ → BoundedContinuousFunction Q ℝ := fun f =>
    BoundedContinuousFunction.ofNormedAddCommGroup (fun q => f (s q)) (hlift f) ‖f‖
      (fun q => f.norm_coe_le_norm (s q))
  have hint : ∀ (f : BoundedContinuousFunction X ℝ) (ν : Measure Q),
      ∫ x, f x ∂(ν.map s) = ∫ q, gf f q ∂ν := by
    intro f ν
    rw [integral_map hs_meas.aemeasurable f.continuous.aestronglyMeasurable]
    rfl
  -- the push-forward maps between the spaces of probability measures
  let Φ : ProbabilityMeasure X → ProbabilityMeasure Q := fun μ => μ.map mk
  let Ψ : ProbabilityMeasure Q → ProbabilityMeasure X := fun ν => ν.map s
  have hΨΦ : ∀ μ, Ψ (Φ μ) = μ := fun μ => by
    apply Subtype.ext
    simp only [Ψ, Φ, ProbabilityMeasure.val_eq_to_measure, ProbabilityMeasure.toMeasure_map]
    exact hsmk _
  have hΨ : Continuous Ψ := by
    rw [continuous_iff_continuousAt]
    intro ν
    unfold ContinuousAt
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have h0 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1
      (tendsto_id (x := 𝓝 ν)) (gf f)
    simpa only [Ψ, ProbabilityMeasure.toMeasure_map, hint, id] using h0
  -- tightness of the pushed-forward sequence, and Prokhorov in `Q`
  let S : Set (ProbabilityMeasure Q) := range (fun n => Φ (toPM (μs n) (hμs n)))
  have htQ : IsTightMeasureSet {((ν : ProbabilityMeasure Q) : Measure Q) | ν ∈ S} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    obtain ⟨K, hK, hKε⟩ := htight ε hε
    have hKQ : IsCompact (mk '' K) := hK.image hmk_cont
    refine ⟨mk '' K, hKQ, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    simp only [Φ, ProbabilityMeasure.toMeasure_map, toPM_toMeasure]
    rw [Measure.map_apply hmk_meas hKQ.isClosed.measurableSet.compl]
    refine le_trans (measure_mono ?_) (hKε n)
    rw [preimage_compl]
    exact compl_subset_compl.2 (subset_preimage_image _ _)
  have hcomp : IsCompact (Ψ '' closure S) :=
    (isCompact_closure_of_isTightMeasureSet htQ).image hΨ
  have hmem : ∀ n, toPM (μs n) (hμs n) ∈ Ψ '' closure S := fun n =>
    ⟨_, subset_closure ⟨n, rfl⟩, hΨΦ _⟩
  obtain ⟨μ', -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hmem
  refine ⟨φ, hφ, (μ' : Measure X), inferInstance, ?_⟩
  exact (weakConv_iff_tendsto (fun n => hμs (φ n)) inferInstance).2 hlim

/-- Prokhorov extraction for measures carried by a fixed compact set; the limit is carried by
its closure (no separation axiom needed). -/
theorem exists_subseq_weakConv_of_compact_closure {μs : ℕ → Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) {K : Set X} (hK : IsCompact K)
    (hsupp : ∀ n, μs n Kᶜ = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ (closure K)ᶜ = 0 ∧
      WeakConv (fun n => μs (φ n)) μ := by
  obtain ⟨φ, hφ, μ, hμ, hconv⟩ :=
    exists_subseq_weakConv hμs fun ε _ => ⟨K, hK, fun n => by rw [hsupp n]; exact zero_le⟩
  refine ⟨φ, hφ, μ, hμ, ?_, hconv⟩
  have hKm : MeasurableSet (closure K) := isClosed_closure.measurableSet
  have h1 : (1 : ℝ≥0∞) ≤ μ (closure K) :=
    hconv.le_measure_closed (fun n => hμs (φ n)) hμ isClosed_closure
      (Eventually.of_forall fun n => by
        have := hμs (φ n)
        have h0 : μs (φ n) (closure K)ᶜ = 0 :=
          measure_mono_null (compl_subset_compl.2 subset_closure) (hsupp (φ n))
        rw [(prob_compl_eq_zero_iff hKm).1 h0])
  exact (prob_compl_eq_zero_iff hKm).2 (le_antisymm prob_le_one h1)

/-- Prokhorov extraction for measures carried by a compact set, in a Hausdorff space; the limit is
carried by it too. -/
theorem exists_subseq_weakConv_of_compact_of_t2 [T2Space X] {μs : ℕ → Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) {K : Set X} (hK : IsCompact K)
    (hsupp : ∀ n, μs n Kᶜ = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ Kᶜ = 0 ∧
      WeakConv (fun n => μs (φ n)) μ := by
  simpa only [hK.isClosed.closure_eq] using exists_subseq_weakConv_of_compact_closure hμs hK hsupp

/-- Prokhorov extraction for measures carried by a fixed compact set; the limit is carried by
it too. -/
theorem exists_subseq_weakConv_of_compact [T2Space X] {μs : ℕ → Measure X}
    (hμs : ∀ n, IsProbabilityMeasure (μs n)) {K : Set X} (hK : IsCompact K)
    (hsupp : ∀ n, μs n Kᶜ = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ Kᶜ = 0 ∧
      WeakConv (fun n => μs (φ n)) μ := by
  -- (needs a separation axiom; without `T2Space X` see `..._of_compact_closure`)
  exact exists_subseq_weakConv_of_compact_of_t2 hμs hK hsupp

end Molico
