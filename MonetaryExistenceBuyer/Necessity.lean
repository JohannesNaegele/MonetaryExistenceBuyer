import MonetaryExistenceBuyer.Model

/-!
# Necessity of the activation condition (`prop:necessity`)

If `β c₀ ≤ 1`, no stationary monetary equilibrium exists, even in relaxed strategies.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

namespace IsEquilibrium

variable {u : ℝ → ℝ} {β M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ} {Γ : Measure (ℝ × ℝ × ℝ)}

lemma ae_η_nonneg (h : IsEquilibrium u β M V η Γ) : ∀ᵐ x ∂η, 0 ≤ x := by
  rw [ae_iff]
  have e : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [e]; exact h.η_nonneg

lemma map_fst (h : IsEquilibrium u β M V η Γ) : Γ.map (fun p => p.1) = η := by
  haveI := h.isProb_η
  have e : (fun p : ℝ × ℝ × ℝ => p.1) = Prod.fst ∘ pairBS := rfl
  rw [e, ← Measure.map_map measurable_fst (by unfold pairBS; fun_prop), h.marginal,
    Measure.map_fst_prod]
  simp

lemma map_snd (h : IsEquilibrium u β M V η Γ) : Γ.map (fun p => p.2.1) = η := by
  haveI := h.isProb_η
  have e : (fun p : ℝ × ℝ × ℝ => p.2.1) = Prod.snd ∘ pairBS := rfl
  rw [e, ← Measure.map_map measurable_snd (by unfold pairBS; fun_prop), h.marginal,
    Measure.map_snd_prod]
  simp

/-- `Γ`-almost every meeting triple lies in the closed region `b, s ≥ 0`, `0 ≤ d ≤ b`. -/
lemma ae_good (h : IsEquilibrium u β M V η Γ) :
    ∀ᵐ p ∂Γ, 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ p.1 := by
  have h1 : ∀ᵐ p ∂Γ, 0 ≤ p.1 := by
    have := h.ae_η_nonneg
    rw [← h.map_fst] at this
    exact ae_of_ae_map (by fun_prop) this
  have h2 : ∀ᵐ p ∂Γ, 0 ≤ p.2.1 := by
    have := h.ae_η_nonneg
    rw [← h.map_snd] at this
    exact ae_of_ae_map (by fun_prop) this
  have h3 : ∀ᵐ p ∂Γ, p ∈ meetingSet := ae_iff.2 h.Γ_meeting
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  exact ⟨hp1, hp2, hp3.1, hp3.2⟩

lemma ae_prod_nonneg (h : IsEquilibrium u β M V η Γ) :
    ∀ᵐ q ∂(η.prod η), 0 ≤ q.1 ∧ 0 ≤ q.2 := by
  haveI := h.isProb_η
  have hs : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  have := (ae_map_iff (μ := Γ) (f := pairBS) (by unfold pairBS; fun_prop) hs).2 (by
    filter_upwards [h.ae_good] with p hp
    exact ⟨hp.1, hp.2.1⟩)
  rw [h.marginal] at this
  simpa using this

end IsEquilibrium

/-- `prop:necessity`: if `β c₀ ≤ 1` there is no stationary monetary equilibrium, even in relaxed
strategies. -/
theorem necessity (U : AdmissibleUtility) {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβc : β * U.c0 ≤ 1) {V : ℝ → ℝ} {η : Measure ℝ} {Γ : Measure (ℝ × ℝ × ℝ)}
    (h : IsEquilibrium U.u β M V η Γ) : False := by
  haveI := h.isProb_η
  haveI := h.isProb_Γ
  have hV := h.value
  -- continuous bounded versions of `V` and `u`
  set Vt := posPart V with hVt_def
  set ut := posPart U.u with hut_def
  have hVt : Continuous Vt := continuous_posPart hV.continuousOn
  have eqV : ∀ {x}, 0 ≤ x → Vt x = V x := fun hx => posPart_eq hx
  have equ : ∀ {x}, 0 ≤ x → ut x = U.u x := fun hx => posPart_eq hx
  have hut : Continuous ut := continuous_posPart U.continuousOn
  set C := hV.sup
  have Vt0 : ∀ x, 0 ≤ Vt x := hV.posPart_nonneg
  have VtC : ∀ x, Vt x ≤ C := hV.posPart_le
  have ut0 : ∀ x, 0 ≤ ut x := posPart_u_nonneg U
  have utb : ∀ x, ut x ≤ U.ubar := posPart_u_le U
  have hgood := h.ae_good
  have intC : ∀ {X : Type} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
      [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ),
      Continuous f → (∀ x, |f x| ≤ C + U.ubar) → Integrable f μ := by
    intro X _ _ _ _ μ _ f hf hb
    exact Integrable.of_bound hf.aestronglyMeasurable (C + U.ubar)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have absV : ∀ x, |Vt x| ≤ C + U.ubar := fun x => by
    rw [abs_of_nonneg (Vt0 x)]; linarith [VtC x, U.ubar_pos]
  -- the integrands on `Γ`
  set fB : ℝ × ℝ × ℝ → ℝ := fun p => Vt (p.1 - p.2.2) with hfB
  set fS : ℝ × ℝ × ℝ → ℝ := fun p => Vt (p.2.1 + p.2.2) with hfS
  set f1 : ℝ × ℝ × ℝ → ℝ := fun p => Vt p.1 with hf1
  set f2 : ℝ × ℝ × ℝ → ℝ := fun p => Vt p.2.1 with hf2
  set fu : ℝ × ℝ × ℝ → ℝ := fun p => ut (Vt (p.2.1 + p.2.2) - Vt p.2.1) with hfu
  have iB : Integrable fB Γ := intC Γ fB (by fun_prop) (fun p => absV _)
  have iS : Integrable fS Γ := intC Γ fS (by fun_prop) (fun p => absV _)
  have i1 : Integrable f1 Γ := intC Γ f1 (by fun_prop) (fun p => absV _)
  have i2 : Integrable f2 Γ := intC Γ f2 (by fun_prop) (fun p => absV _)
  have iu : Integrable fu Γ := intC Γ fu (by fun_prop) (fun p => by
    simp only [fu]; rw [abs_of_nonneg (ut0 _)]; linarith [utb (Vt (p.2.1 + p.2.2) - Vt p.2.1),
      hV.sup_nonneg])
  -- marginals
  have hv1 : ∫ x, Vt x ∂η = ∫ p, f1 p ∂Γ := by
    conv_lhs => rw [← h.map_fst]
    rw [integral_map (by fun_prop) hVt.aestronglyMeasurable]
  have hv2 : ∫ x, Vt x ∂η = ∫ p, f2 p ∂Γ := by
    conv_lhs => rw [← h.map_snd]
    rw [integral_map (by fun_prop) hVt.aestronglyMeasurable]
  -- stationarity: `v̄ = ½ ∫ V(b-d) dΓ + ½ ∫ V(s+d) dΓ`
  have hstat : ∫ x, Vt x ∂η = 2⁻¹ * ∫ p, fB p ∂Γ + 2⁻¹ * ∫ p, fS p ∂Γ := by
    have mB : Measurable postB := by unfold postB; fun_prop
    have mS : Measurable postS := by unfold postS; fun_prop
    haveI : IsFiniteMeasure (Γ.map postB) := inferInstance
    haveI : IsFiniteMeasure (Γ.map postS) := inferInstance
    conv_lhs => rw [h.stationary]
    rw [integral_add_measure, integral_smul_measure, integral_smul_measure,
      integral_map mB.aemeasurable hVt.aestronglyMeasurable,
      integral_map mS.aemeasurable hVt.aestronglyMeasurable]
    · simp [fB, fS, postB, postS, ENNReal.toReal_inv]
    · exact (intC _ Vt hVt absV).smul_measure (by simp)
    · exact (intC _ Vt hVt absV).smul_measure (by simp)
  -- the Bellman equation averaged over `η`
  obtain ⟨G, hG, hGb, hGeq⟩ := exists_continuous_bellH U hV
  have absG : ∀ q, |G q| ≤ C + U.ubar := fun q => by
    rw [abs_of_nonneg (hGb q).1]; linarith [(hGb q).2]
  have hbell : ∫ x, Vt x ∂η = β * ∫ p, (fu p + fB p) ∂Γ := by
    have step1 : ∫ x, Vt x ∂η = ∫ x, β * ∫ s, G (x, s) ∂η ∂η := by
      refine integral_congr_ae ?_
      filter_upwards [h.ae_η_nonneg] with x hx
      rw [eqV hx, h.bellman x hx, bellT]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h.ae_η_nonneg] with s hs
      exact (hGeq x s hx hs).symm
    have iG : Integrable G (η.prod η) := intC _ G hG absG
    rw [step1, integral_const_mul, ← integral_prod G iG, ← h.marginal,
      integral_map (by unfold pairBS; fun_prop) hG.aestronglyMeasurable]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hgood, h.argmax] with p hp hpa
    simp only [pairBS, fu, fB]
    rw [hGeq p.1 p.2.1 hp.1 hp.2.1, ← hpa, obj, gain,
      eqV (show 0 ≤ p.2.1 + p.2.2 by linarith [hp.2.1, hp.2.2.1]), eqV hp.2.1,
      eqV (show 0 ≤ p.1 - p.2.2 by linarith [hp.2.2.2])]
    rw [equ (show 0 ≤ V (p.2.1 + p.2.2) - V p.2.1 from hV.gain_nonneg hp.2.1 hp.2.2.1)]
  -- strictness from positive monetary trade: `∫ u(Δ) dΓ < c₀ ∫ Δ dΓ`
  set fD : ℝ × ℝ × ℝ → ℝ := fun p => fS p - f2 p with hfD
  have iD : Integrable fD Γ := iS.sub i2
  have hstrict : ∫ p, fu p ∂Γ < U.c0 * ∫ p, fD p ∂Γ := by
    rw [← integral_const_mul, ← sub_pos, ← integral_sub (iD.const_mul _) iu]
    have hnn : 0 ≤ᵐ[Γ] fun p => U.c0 * fD p - fu p := by
      filter_upwards [hgood] with p hp
      simp only [fD, fS, f2, fu, Pi.zero_apply]
      have hg : 0 ≤ Vt (p.2.1 + p.2.2) - Vt p.2.1 := by
        rw [eqV (by linarith [hp.2.1, hp.2.2.1]), eqV hp.2.1]
        exact hV.gain_nonneg hp.2.1 hp.2.2.1
      rw [equ hg]
      linarith [U.le_c0_mul hg]
    rw [integral_pos_iff_support_of_nonneg_ae hnn ((iD.const_mul _).sub iu)]
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr h.monetary) (measure_mono_ae ?_)
    filter_upwards [hgood] with p hp hmon
    simp only [Function.mem_support, fD, fS, f2, fu]
    have e1 : Vt (p.2.1 + p.2.2) - Vt p.2.1 = gain V p.2.1 p.2.2 := by
      rw [eqV (by linarith [hp.2.1, hp.2.2.1]), eqV hp.2.1]; rfl
    rw [e1, equ hmon.le]
    have := U.lt_c0_mul hmon
    linarith
  -- assemble the contradiction
  have hDnn : 0 ≤ ∫ p, fD p ∂Γ := integral_nonneg_of_ae (by
    filter_upwards [hgood] with p hp
    simp only [fD, fS, f2, Pi.zero_apply]
    rw [eqV (by linarith [hp.2.1, hp.2.2.1]), eqV hp.2.1]
    exact hV.gain_nonneg hp.2.1 hp.2.2.1)
  have hBnn : 0 ≤ ∫ p, fB p ∂Γ := integral_nonneg fun p => Vt0 _
  have hDdef : ∫ p, fD p ∂Γ = ∫ p, fS p ∂Γ - ∫ p, f2 p ∂Γ := integral_sub iS i2
  rw [integral_add iu iB] at hbell
  have hβc' : β * U.c0 * ∫ p, fD p ∂Γ ≤ ∫ p, fD p ∂Γ := by
    nlinarith
  have hβB : β * ∫ p, fB p ∂Γ ≤ ∫ p, fB p ∂Γ := by nlinarith
  nlinarith

end Molico
