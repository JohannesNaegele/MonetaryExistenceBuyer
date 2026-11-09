import MonetaryExistenceBuyer.Saturation.Final

/-!
# Exclusion of a positive jump at the origin (§7 of `existence-theorem.tex`)

* `valuelaw` — `prop:valuelaw`: at every level `a` inside the jump, `ν([0,a]) ≥ μ_c` and
  `σ a = ∫ u((a - y)₊) dν`; hence `ν({0}) ≥ μ_c`.
* `nojump` — `thm:nojump`: no bad sequence exists.

Both are derived here from the statements of §5–§6.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

lemma SelectedSeq.jump_nonneg (S : SelectedSeq P) : 0 ≤ S.jump := by
  obtain ⟨-, -, hb, -⟩ := S.limit_props
  exact le_csInf ((nonempty_Ioi).image _) (by
    rintro _ ⟨x, hx, rfl⟩; exact (hb x (le_of_lt hx)).1)

/-- `prop:valuelaw` (value distribution at every normalization level), eqs. `eq:valuelaw`,
`eq:zerovaluemass`. -/
theorem valuelaw (S : SelectedSeq P) (hbad : S.IsBad) :
    (∀ a, 0 < a → a < S.jump →
      ENNReal.ofReal P.μc ≤ S.νlim (Icc 0 a) ∧
      P.σ * a = ∫ y, P.U.u (max (a - y) 0) ∂S.νlim) ∧
    ENNReal.ofReal P.μc ≤ S.νlim {0} := by
  haveI := S.νlim_prob
  have hlevel : ∀ a, 0 < a → a < S.jump →
      ENNReal.ofReal P.μc ≤ S.νlim (Icc 0 a) ∧
      P.σ * a = ∫ y, P.U.u (max (a - y) 0) ∂S.νlim := by
    intro a ha haJ
    obtain ⟨NL⟩ := normalizedLimit_exists S ha haJ
    haveI := NL.α_prob
    -- `thm:noplateau` and `prop:pin`: `W(x) = L = J' = a` for `x > 0`
    have hfp := NL.noplateau ha haJ
    obtain ⟨hδ, hWL, hLJ, hJa⟩ := NL.pin ha haJ hfp
    obtain ⟨-, -, -, -, -, -, -, hEW, hproj, -, -⟩ := NL.props ha haJ
    have hL : NL.Lsup = a := hLJ.trans hJa
    -- finite compatible states have value `≤ a`, infinite ones value `≥ a`
    have hstates : ∀ p ∈ NL.EW, (p.1 ≠ ⊤ → 0 ≤ p.2 ∧ p.2 ≤ a) ∧ (p.1 = ⊤ → a ≤ p.2) := by
      intro p hp
      rcases hp with (hp | hp) | hp
      · obtain ⟨hp1, hp2⟩ := hp
        refine ⟨fun _ => ⟨hp2.1, hp2.2.trans hJa.le⟩, fun h => ?_⟩
        rw [mem_singleton_iff] at hp1
        rw [hp1] at h; exact absurd h ENNReal.zero_ne_top
      · obtain ⟨z, hz, rfl⟩ := hp
        have hz' : 0 < z := by
          unfold NormalizedLimit.Xplus at hz; rw [if_pos hδ] at hz; exact hz
        refine ⟨fun _ => ?_, fun h => absurd h ENNReal.ofReal_ne_top⟩
        simp only
        rw [hWL z hz', hL]; exact ⟨ha.le, le_rfl⟩
      · obtain ⟨hp1, hp2⟩ := hp
        rw [mem_singleton_iff] at hp1
        exact ⟨fun h => absurd hp1 h, fun _ => hL ▸ hp2.1⟩
    have hae : ∀ᵐ p ∂NL.α, p ∈ NL.EW := ae_iff.2 hEW
    refine ⟨?_, ?_⟩
    · -- `prop:non-escape` and the value marginal `eq:valueprojection`
      have hsub : {p : ℝ≥0∞ × ℝ | p.1 ≤ ENNReal.ofReal (P.U.c0 * P.Cstar / a)} ⊆
          (Prod.snd ⁻¹' Icc 0 a) ∪ NL.EWᶜ := by
        intro p hp
        by_cases hpe : p ∈ NL.EW
        · left
          exact (hstates p hpe).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp)
        · right; exact hpe
      rw [← hproj, Measure.map_apply measurable_snd measurableSet_Icc]
      calc ENNReal.ofReal P.μc
          ≤ NL.α {p : ℝ≥0∞ × ℝ | p.1 ≤ ENNReal.ofReal (P.U.c0 * P.Cstar / a)} := NL.nonEscape ha haJ
        _ ≤ NL.α ((Prod.snd ⁻¹' Icc 0 a) ∪ NL.EWᶜ) := measure_mono hsub
        _ ≤ NL.α (Prod.snd ⁻¹' Icc 0 a) + NL.α NL.EWᶜ := measure_union_le _ _
        _ = NL.α (Prod.snd ⁻¹' Icc 0 a) := by rw [hEW, add_zero]
    · -- `lem:bellmaninfinity` and the value marginal
      have hbi := NL.bellmanInfinity ha haJ
      rw [hL] at hbi
      have hcont : Continuous (fun y : ℝ => P.U.u (max (a - y) 0)) :=
        P.U.continuousOn.comp_continuous (by fun_prop) (fun y => mem_Ici.2 (le_max_right _ _))
      have hms : MeasurableSet {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤} :=
        show MeasurableSet (Prod.fst ⁻¹' ({⊤}ᶜ : Set ℝ≥0∞)) from
          measurable_fst (measurableSet_singleton ⊤).compl
      rw [hbi, ← hproj, integral_map measurable_snd.aemeasurable hcont.aestronglyMeasurable,
        ← integral_indicator hms]
      refine integral_congr_ae ?_
      filter_upwards [hae] with p hp
      by_cases hp1 : p.1 = ⊤
      · rw [indicator_of_notMem (show p ∉ {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤} from fun h => h hp1)]
        have := (hstates p hp).2 hp1
        rw [max_eq_right (by linarith), P.U.u_zero]
      · rw [indicator_of_mem (show p ∈ {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤} from hp1)]
        have := (hstates p hp).1 hp1
        rw [max_eq_left (by linarith)]
  refine ⟨hlevel, ?_⟩
  -- continuity from above along the levels `a_k = J₀/(k+2) ↓ 0`
  have hJ : 0 < S.jump := hbad
  set s : ℕ → Set ℝ := fun k => Icc 0 (S.jump / ((k : ℝ) + 2)) with hs
  have hanti : Antitone s := fun i j hij => Icc_subset_Icc le_rfl
    (div_le_div_of_nonneg_left hJ.le (by positivity) (by gcongr))
  have hinter : ⋂ k, s k = {0} := by
    ext x
    simp only [hs, mem_iInter, mem_Icc, mem_singleton_iff]
    constructor
    · intro hx
      have hx0 := (hx 0).1
      by_contra hne
      have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
      obtain ⟨k, hk⟩ := exists_nat_gt (S.jump / x)
      have h1 := (hx k).2
      rw [le_div_iff₀ (by positivity)] at h1
      rw [div_lt_iff₀ hxpos] at hk
      nlinarith
    · rintro rfl k; exact ⟨le_rfl, by positivity⟩
  have ht := tendsto_measure_iInter_atTop (μ := S.νlim)
    (fun k => measurableSet_Icc.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at ht
  refine ge_of_tendsto' ht (fun k => (hlevel _ (by positivity) ?_).1)
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-- `thm:nojump` (contradiction from zero-value sellers): no bad sequence exists. -/
theorem nojump (S : SelectedSeq P) : ¬ S.IsBad := by
  intro hbad
  haveI := S.νlim_prob
  obtain ⟨hval, hatom⟩ := valuelaw S hbad
  have hc1 := P.c0_gt_one
  -- `μ_c c₀ = σ c₀/(c₀ - 1) > σ`
  have hgt : P.σ < P.μc * P.U.c0 := by
    unfold Primitives.μc
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)]
    nlinarith [P.σ_pos]
  have hlim : Tendsto (fun x => P.μc * (P.U.u x / x)) (𝓝[>] 0) (𝓝 (P.μc * P.U.c0)) :=
    P.U.tendsto_div_zero.const_mul _
  -- choose `ℓ ∈ (0, J₀)` so small that `μ_c u(ℓ) > σ ℓ`
  obtain ⟨ℓ, hℓ, hℓ0⟩ :=
    ((hlim.eventually (lt_mem_nhds hgt)).and (Ioo_mem_nhdsGT (show (0:ℝ) < S.jump from hbad))).exists
  obtain ⟨-, hbell⟩ := hval ℓ hℓ0.1 hℓ0.2
  have hμ : P.μc ≤ (S.νlim {0}).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hatom
  have hcont : Continuous (fun y : ℝ => P.U.u (max (ℓ - y) 0)) :=
    P.U.continuousOn.comp_continuous (by fun_prop) (fun y => mem_Ici.2 (le_max_right _ _))
  have hint : Integrable (fun y => P.U.u (max (ℓ - y) 0)) S.νlim :=
    Integrable.of_bound hcont.aestronglyMeasurable P.U.ubar (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (P.U.nonneg (le_max_right _ _))]
      exact P.U.le_ubar (le_max_right _ _))
  have hnn : 0 ≤ᵐ[S.νlim] fun y => P.U.u (max (ℓ - y) 0) :=
    ae_of_all _ fun y => P.U.nonneg (le_max_right _ _)
  -- the final display in the proof of `thm:nojump`
  have hge := setIntegral_le_integral (s := {0}) hint hnn
  rw [integral_singleton, sub_zero, max_eq_left hℓ0.1.le, smul_eq_mul, ← hbell] at hge
  have hu : 0 < P.U.u ℓ := P.U.pos hℓ0.1
  have h1 : P.σ * ℓ < P.μc * P.U.u ℓ := by
    have := hℓ
    rw [← mul_div_assoc, lt_div_iff₀ hℓ0.1] at this
    linarith
  have h2 : P.μc * P.U.u ℓ ≤ S.νlim.real {0} * P.U.u ℓ :=
    mul_le_mul_of_nonneg_right hμ hu.le
  linarith

end Molico
