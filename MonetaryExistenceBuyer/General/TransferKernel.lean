import MonetaryExistenceBuyer.General.Selection
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Transfer kernels of an equilibrium (`rem:physicaloutput`)

Disintegrating the meeting measure `Γ` of an equilibrium over `(b, s)` gives a transfer kernel
`ν` with `Γ = (η ⊗ η) ⊗ ν` (after regrouping `(b, s, d)` as `((b, s), d)`). It is supported on
maximisers of the buyer problem for `η ⊗ η`-a.e. pair; on the exceptional pairs it is replaced by
a Dirac mass at a measurable maximiser (`exists_measurable_argmax`), so that the support
property holds at every pair. If `Γ` is deterministic, `ν` can be taken Dirac everywhere.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory

noncomputable section

namespace Molico

/-- The buyer objective with all arguments of `u` and `V` clamped to `[0, ∞)`; it is continuous
on all of `(ℝ × ℝ) × ℝ` and agrees with `obj` on meeting triples with `s ≥ 0`. -/
private def objc (u V : ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  posPart u (posPart V (p.1.2 + p.2) - posPart V p.1.2) + posPart V (p.1.1 - p.2)

/-- Triples `((b, s), d)` with `b, s ≥ 0`, `d ∈ [0, b]` and `d` a maximiser of the buyer
problem, written with the clamped objective and value. -/
private def goodSet (u V : ℝ → ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1.1 ∧
    objc u V p = bellH u V (max p.1.1 0) (max p.1.2 0)}

private lemma objc_eq {u V : ℝ → ℝ} (hV : IsValueFn V) {b s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hdb : d ≤ b) : objc u V ((b, s), d) = obj u V b s d := by
  have h1 : 0 ≤ s + d := add_nonneg hs hd
  have h2 : 0 ≤ b - d := sub_nonneg.2 hdb
  have h3 : 0 ≤ V (s + d) - V s := hV.gain_nonneg hs hd
  simp only [objc, obj, gain, posPart, max_eq_left h1, max_eq_left hs, max_eq_left h2,
    max_eq_left h3]

private lemma mem_goodSet_iff {u V : ℝ → ℝ} (hV : IsValueFn V) {b s d : ℝ} (hb : 0 ≤ b)
    (hs : 0 ≤ s) :
    ((b, s), d) ∈ goodSet u V ↔ d ∈ Icc 0 b ∧ obj u V b s d = bellH u V b s := by
  simp only [goodSet, mem_ofPred_eq, mem_Icc, max_eq_left hb, max_eq_left hs]
  constructor
  · rintro ⟨-, -, hd, hdb, he⟩
    exact ⟨⟨hd, hdb⟩, by rw [← objc_eq hV hs hd hdb, he]⟩
  · rintro ⟨⟨hd, hdb⟩, he⟩
    exact ⟨hb, hs, hd, hdb, by rw [objc_eq hV hs hd hdb, he]⟩

private lemma measurableSet_goodSet {u V : ℝ → ℝ} (hu : ContinuousOn u (Ici 0))
    (hum : MonotoneOn u (Ici 0)) (hV : IsValueFn V) : MeasurableSet (goodSet u V) := by
  have hu' : Continuous (posPart u) := continuous_posPart hu
  have hV' : Continuous (posPart V) := continuous_posPart hV.continuousOn
  have hc : Continuous (objc u V) := by
    unfold objc
    fun_prop
  have hH : Measurable fun p : (ℝ × ℝ) × ℝ => bellH u V (max p.1.1 0) (max p.1.2 0) :=
    (measurable_bellH_clamp hu hum hV).comp measurable_fst
  have e : goodSet u V = {p | 0 ≤ p.1.1} ∩ ({p | 0 ≤ p.1.2} ∩ ({p | 0 ≤ p.2} ∩
      ({p | p.2 ≤ p.1.1} ∩ {p | objc u V p = bellH u V (max p.1.1 0) (max p.1.2 0)}))) := rfl
  rw [e]
  exact (measurableSet_le measurable_const measurable_fst.fst).inter
    ((measurableSet_le measurable_const measurable_fst.snd).inter
    ((measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_fst.fst).inter
    (measurableSet_eq_fun hc.measurable hH))))

/-- A transfer kernel reproducing `Γ`, supported on maximisers at every pair, and Dirac if `Γ` is
deterministic. -/
theorem exists_transfer_kernel {u : ℝ → ℝ} (hu : ContinuousOn u (Ici 0))
    (hum : MonotoneOn u (Ici 0)) {β M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ}
    {Γ : Measure (ℝ × ℝ × ℝ)} (h : IsEquilibrium u β M V η Γ) :
    ∃ ν : Kernel (ℝ × ℝ) ℝ, IsMarkovKernel ν ∧
      Γ.map (fun p => ((p.1, p.2.1), p.2.2)) = (η.prod η) ⊗ₘ ν ∧
      (∀ b s, 0 ≤ b → 0 ≤ s →
        ∀ᵐ d ∂(ν (b, s)), d ∈ Icc 0 b ∧ obj u V b s d = bellH u V b s) ∧
      (IsDeterministic Γ → ∀ b s, 0 ≤ b → 0 ≤ s → ∃ d, ν (b, s) = Measure.dirac d) := by
  classical
  have hV := h.value
  have := h.isProb_η
  have := h.isProb_Γ
  obtain ⟨dsel, hdsel, hdsel_spec⟩ := exists_measurable_argmax hu hum hV
  set e : ℝ × ℝ × ℝ → (ℝ × ℝ) × ℝ := fun p => ((p.1, p.2.1), p.2.2) with he_def
  have he : Measurable e := (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  set Γ' := Γ.map e with hΓ'
  have : IsProbabilityMeasure Γ' := by rw [hΓ']; infer_instance
  set S := goodSet u V with hS_def
  have hS : MeasurableSet S := measurableSet_goodSet hu hum hV
  -- almost-sure facts on `Γ`
  have hη : ∀ᵐ x ∂η, 0 ≤ x := by
    have hI : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by ext x; simp
    rw [ae_iff, hI]
    exact h.η_nonneg
  have hηη : ∀ᵐ x ∂(η.prod η), 0 ≤ x.1 ∧ 0 ≤ x.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hη,
      Measure.quasiMeasurePreserving_snd.ae hη] with x h1 h2
    exact ⟨h1, h2⟩
  have hΓnn : ∀ᵐ p ∂Γ, 0 ≤ p.1 ∧ 0 ≤ p.2.1 := by
    have hP : Measurable pairBS := measurable_fst.prodMk measurable_snd.fst
    rw [← h.marginal] at hηη
    exact ae_of_ae_map hP.aemeasurable hηη
  have hΓm : ∀ᵐ p ∂Γ, p ∈ meetingSet := ae_iff.2 h.Γ_meeting
  have hΓS : ∀ᵐ p ∂Γ, e p ∈ S := by
    filter_upwards [hΓnn, hΓm, h.argmax] with p hnn hm ha
    exact (mem_goodSet_iff hV hnn.1 hnn.2).2 ⟨⟨hm.1, hm.2⟩, ha⟩
  have hΓ'S : ∀ᵐ q ∂Γ', q ∈ S := (ae_map_iff he.aemeasurable hS).2 hΓS
  have hfst : Γ'.fst = η.prod η := by
    rw [Measure.fst, hΓ', Measure.map_map measurable_fst he]
    exact h.marginal
  by_cases hdet : IsDeterministic Γ
  · -- deterministic case: a Dirac kernel at a measurable maximiser agreeing with `d_V`
    obtain ⟨dV, hdV, hdVae⟩ := hdet
    set G' : Set (ℝ × ℝ) := {x | (x, dV x) ∈ S} with hG'_def
    have hG' : MeasurableSet G' := (measurable_id.prodMk hdV) hS
    set d' : ℝ × ℝ → ℝ := G'.piecewise dV dsel with hd'_def
    have hd' : Measurable d' := hdV.piecewise hG' hdsel
    have hd'good : ∀ b s, 0 ≤ b → 0 ≤ s → ((b, s), d' (b, s)) ∈ S := by
      intro b s hb hs
      by_cases hx : (b, s) ∈ G'
      · rw [hd'_def, Set.piecewise_eq_of_mem _ _ _ hx]
        exact hx
      · rw [hd'_def, Set.piecewise_eq_of_notMem _ _ _ hx]
        exact (mem_goodSet_iff hV hb hs).2 (hdsel_spec b s hb hs)
    refine ⟨Kernel.deterministic d' hd', inferInstance, ?_, ?_, ?_⟩
    · have hae : ∀ᵐ q ∂Γ', q.2 = d' q.1 := by
        have : ∀ᵐ p ∂Γ, (e p).2 = d' (e p).1 := by
          filter_upwards [hdVae, hΓS] with p hp hpS
          have hx : (p.1, p.2.1) ∈ G' := by
            show ((p.1, p.2.1), dV (p.1, p.2.1)) ∈ S
            rw [← hp]
            exact hpS
          show p.2.2 = d' (p.1, p.2.1)
          rw [hd'_def, Set.piecewise_eq_of_mem _ _ _ hx]
          exact hp
        exact (ae_map_iff he.aemeasurable
          (measurableSet_eq_fun measurable_snd (hd'.comp measurable_fst))).2 this
      rw [Measure.compProd_deterministic, ← hfst, Measure.fst,
        Measure.map_map (by fun_prop : Measurable fun a => (a, d' a)) measurable_fst]
      conv_lhs => rw [← Measure.map_id (μ := Γ')]
      refine Measure.map_congr ?_
      filter_upwards [hae] with q hq
      exact Prod.ext rfl hq
    · intro b s hb hs
      rw [Kernel.deterministic_apply, ae_dirac_eq]
      exact (mem_goodSet_iff hV hb hs).1 (hd'good b s hb hs)
    · intro _ b s _ _
      exact ⟨d' (b, s), Kernel.deterministic_apply _ _⟩
  · -- general case: disintegrate, and repair the kernel on a null set of pairs
    set κ := Γ'.condKernel with hκ_def
    have hdis : (η.prod η) ⊗ₘ κ = Γ' := by
      rw [← hfst]
      exact Γ'.disintegrate κ
    set G : Set (ℝ × ℝ) := {x | κ x (Prod.mk x ⁻¹' Sᶜ) = 0} with hG_def
    have hG : MeasurableSet G :=
      (Kernel.measurable_kernel_prodMk_left hS.compl) (measurableSet_singleton 0)
    have haeG : ∀ᵐ x ∂(η.prod η), x ∈ G := by
      have h2 : ∀ᵐ q ∂((η.prod η) ⊗ₘ κ), q ∈ S := by rw [hdis]; exact hΓ'S
      filter_upwards [Measure.ae_ae_of_ae_compProd h2] with x hx
      exact ae_iff.1 hx
    refine ⟨Kernel.piecewise hG κ (Kernel.deterministic dsel hdsel), inferInstance, ?_, ?_, ?_⟩
    · refine hdis.symm.trans (Measure.compProd_congr ?_)
      filter_upwards [haeG] with x hx
      rw [Kernel.piecewise_apply, ite_eq_left hx]
    · intro b s hb hs
      by_cases hx : (b, s) ∈ G
      · rw [Kernel.piecewise_apply, ite_eq_left hx]
        have : ∀ᵐ d ∂(κ (b, s)), ((b, s), d) ∈ S := ae_iff.2 hx
        filter_upwards [this] with d hd
        exact (mem_goodSet_iff hV hb hs).1 hd
      · rw [Kernel.piecewise_apply, ite_eq_right hx, Kernel.deterministic_apply, ae_dirac_eq]
        exact hdsel_spec b s hb hs
    · intro hd
      exact absurd hd hdet

end Molico
