import MonetaryExistenceBuyer.Limit.Props
import MonetaryExistenceBuyer.Grid.Existence

/-!
# Existence of selected sequences (`def:selected`)

`thm:approx` provides approximant equilibria with the amplitude floor on every grid with
`R ≥ R_amp`. Along `h_n ↓ 0`, `R_n ↑ ∞` a subsequence converges in the sense of `SelectedSeq`.
The extraction (`SelectedSeq.extract`) combines Helly's selection theorem, Arzelà–Ascoli and
Prokhorov's theorem (see the footnote in `def:selected`).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

/-- The interpolants of approximant equilibria with the floor `eq:floor` are nondecreasing and
concave on `[0,∞)`, with values in `[0, L_*]`. -/
private lemma interp_facts {P : Primitives} {h : ℕ → ℝ} {N : ℕ → ℕ} {V η : ℕ → ℕ → ℝ}
    {κ : ℕ → ℕ → ℕ → ℕ → ℝ} (h_pos : ∀ n, 0 < h n)
    (isApproxEq : ∀ n, Grid.IsApproxEq P (h n) (N n) (V n) (η n) (κ n))
    (floor : ∀ n, P.ℓ0 ≤ V n (N n) ∧ V n (N n) ≤ P.Lstar) :
    (∀ n, MonotoneOn (interp (h n) (N n) (V n)) (Ici 0)) ∧
      (∀ n, ConcaveOn ℝ (Ici 0) (interp (h n) (N n) (V n))) ∧
      (∀ n x, 0 ≤ interp (h n) (N n) (V n) x ∧ interp (h n) (N n) (V n) x ≤ P.Lstar) := by
  refine ⟨fun n => (interp_monotone (h_pos n) (isApproxEq n).cone.incr).monotoneOn _,
    fun n => interp_concaveOn (h_pos n) (isApproxEq n).cone.incr, fun n x => ?_⟩
  have h1 := interp_mem_Icc (h_pos n) (isApproxEq n).cone.incr x
  rw [(isApproxEq n).cone.zero] at h1
  exact ⟨h1.1, h1.2.trans (floor n).2⟩

/-- The compactness step of `def:selected`: every sequence of approximant equilibria along
`h_n ↓ 0`, `R_n ↑ ∞` with the floor `eq:floor` has a subsequence that is a selected sequence. -/
theorem SelectedSeq.extract (P : Primitives) (h : ℕ → ℝ) (N : ℕ → ℕ) (V η : ℕ → ℕ → ℝ)
    (κ : ℕ → ℕ → ℕ → ℕ → ℝ) (h_pos : ∀ n, 0 < h n) (h_tendsto : Tendsto h atTop (𝓝 0))
    (R_tendsto : Tendsto (fun n => (N n : ℝ) * h n) atTop atTop)
    (R_ge : ∀ n, P.Ramp ≤ (N n : ℝ) * h n)
    (isApproxEq : ∀ n, Grid.IsApproxEq P (h n) (N n) (V n) (η n) (κ n))
    (floor : ∀ n, P.ℓ0 ≤ V n (N n) ∧ V n (N n) ≤ P.Lstar) :
    ∃ S : SelectedSeq P, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, S.h n = h (φ n) ∧ S.N n = N (φ n) ∧ S.V n = V (φ n) ∧ S.η n = η (φ n) ∧
        S.κ n = κ (φ n) := by
  obtain ⟨hmono, hconc, hbd⟩ := interp_facts h_pos isApproxEq floor
  -- Helly's selection for the interpolated values
  obtain ⟨φ₁, hφ₁, g, hg⟩ := helly_concave (f := fun n => interp (h n) (N n) (V n))
    (B := P.Lstar) hmono hconc (fun n x _ => hbd n x)
  -- Prokhorov for the laws: tightness by Markov's inequality
  have hprob : ∀ n, IsProbabilityMeasure (gridMeasure (h n) (N n) (η n)) :=
    fun n => gridMeasure_isProb (isApproxEq n).law
  have htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧
      ∀ n, gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n)) Kᶜ ≤ ε := by
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact ⟨∅, isCompact_empty, fun n => le_top⟩
    have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hT : 0 < P.M / ε.toReal := div_pos P.M_pos hε'
    refine ⟨Icc 0 (P.M / ε.toReal), isCompact_Icc, fun n => ?_⟩
    have hsub : (Icc 0 (P.M / ε.toReal))ᶜ ⊆
        (Icc 0 ((N (φ₁ n) : ℝ) * h (φ₁ n)))ᶜ ∪ Ioi (P.M / ε.toReal) := by
      intro x hx
      simp only [mem_compl_iff, mem_Icc, not_and, not_le, mem_union, mem_Ioi] at hx ⊢
      by_cases hx0 : 0 ≤ x
      · exact Or.inr (hx hx0)
      · exact Or.inl (fun h' => absurd h' hx0)
    calc gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n)) (Icc 0 (P.M / ε.toReal))ᶜ
        ≤ gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n))
            ((Icc 0 ((N (φ₁ n) : ℝ) * h (φ₁ n)))ᶜ ∪ Ioi (P.M / ε.toReal)) := measure_mono hsub
      _ ≤ gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n)) (Icc 0 ((N (φ₁ n) : ℝ) * h (φ₁ n)))ᶜ +
            gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n)) (Ioi (P.M / ε.toReal)) :=
          measure_union_le _ _
      _ = gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n)) (Ioi (P.M / ε.toReal)) := by
          rw [gridMeasure_compl_Icc (h_pos _).le (isApproxEq _).law, zero_add]
      _ = ENNReal.ofReal
            ((gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n))).real (Ioi (P.M / ε.toReal))) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (P.M / (P.M / ε.toReal)) :=
          ENNReal.ofReal_le_ofReal (gridMeasure_Ioi_le (h_pos _).le (isApproxEq _).law hT)
      _ = ε := by rw [div_div_cancel₀ P.M_pos.ne', ENNReal.ofReal_toReal hεtop]
  obtain ⟨φ₂, hφ₂, μη, hμη, hconvη⟩ := exists_subseq_weakConv
    (μs := fun n => gridMeasure (h (φ₁ n)) (N (φ₁ n)) (η (φ₁ n))) (fun n => hprob (φ₁ n)) htight
  -- Prokhorov for the value distributions, carried by `[0, L_*]`
  have hνprob : ∀ n, IsProbabilityMeasure
      ((gridMeasure (h n) (N n) (η n)).map (interp (h n) (N n) (V n))) := fun n =>
    (Measure.isProbabilityMeasure_map_iff
      (continuous_interp (h_pos n)).measurable.aemeasurable).2 (hprob n)
  have hνsupp : ∀ n,
      ((gridMeasure (h n) (N n) (η n)).map (interp (h n) (N n) (V n))) (Icc 0 P.Lstar)ᶜ = 0 := by
    intro n
    rw [Measure.map_apply (continuous_interp (h_pos n)).measurable measurableSet_Icc.compl]
    have : interp (h n) (N n) (V n) ⁻¹' (Icc 0 P.Lstar)ᶜ = ∅ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_Icc, mem_empty_iff_false, iff_false, not_not]
      exact hbd n x
    rw [this, measure_empty]
  obtain ⟨φ₃, hφ₃, μν, hμν, -, hconvν⟩ := exists_subseq_weakConv_of_compact
    (μs := fun n => (gridMeasure (h (φ₁ (φ₂ n))) (N (φ₁ (φ₂ n))) (η (φ₁ (φ₂ n)))).map
      (interp (h (φ₁ (φ₂ n))) (N (φ₁ (φ₂ n))) (V (φ₁ (φ₂ n)))))
    (fun n => hνprob _) isCompact_Icc (fun n => hνsupp _)
  -- the composed subsequence
  have hφ : StrictMono (fun n => φ₁ (φ₂ (φ₃ n))) := hφ₁.comp (hφ₂.comp hφ₃)
  have h23 : StrictMono (fun n => φ₂ (φ₃ n)) := hφ₂.comp hφ₃
  have hg' : TendstoLocallyUniformlyOn
      (fun n => interp (h (φ₁ (φ₂ (φ₃ n)))) (N (φ₁ (φ₂ (φ₃ n)))) (V (φ₁ (φ₂ (φ₃ n)))))
      (Function.update g 0 0) atTop (Ioi 0) := by
    have hg'' : TendstoLocallyUniformlyOn
        (fun n => interp (h (φ₁ (φ₂ (φ₃ n)))) (N (φ₁ (φ₂ (φ₃ n)))) (V (φ₁ (φ₂ (φ₃ n)))))
        g atTop (Ioi 0) := by
      intro u hu x hx
      obtain ⟨t, ht, hev⟩ := hg u hu x hx
      exact ⟨t, ht, h23.tendsto_atTop.eventually hev⟩
    exact hg''.congr_right fun x hx => (Function.update_of_ne (ne_of_gt hx) _ _).symm
  exact ⟨{ h := fun n => h (φ₁ (φ₂ (φ₃ n)))
           N := fun n => N (φ₁ (φ₂ (φ₃ n)))
           V := fun n => V (φ₁ (φ₂ (φ₃ n)))
           η := fun n => η (φ₁ (φ₂ (φ₃ n)))
           κ := fun n => κ (φ₁ (φ₂ (φ₃ n)))
           h_pos := fun n => h_pos _
           h_tendsto := h_tendsto.comp hφ.tendsto_atTop
           R_tendsto := R_tendsto.comp hφ.tendsto_atTop
           R_ge := fun n => R_ge _
           isApproxEq := fun n => isApproxEq _
           floor := fun n => floor _
           Vlim := Function.update g 0 0
           Vlim_zero := Function.update_self _ _ _
           V_conv := hg'
           ηlim := μη
           ηlim_prob := hμη
           η_conv := hconvη.comp hφ₃
           νlim := μν
           νlim_prob := hμν
           ν_conv := hconvν }, fun n => φ₁ (φ₂ (φ₃ n)), hφ, fun n => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- `def:selected`: selected sequences exist (`thm:approx` + `SelectedSeq.extract`). -/
theorem SelectedSeq.nonempty (P : Primitives) : Nonempty (SelectedSeq P) := by
  -- the grids `h_n = 1/(n+1)`, `N_n = ⌈(R_amp + n)(n+1)⌉`
  set h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hh
  set N : ℕ → ℕ := fun n => ⌈(P.Ramp + n) * ((n : ℝ) + 1)⌉₊ with hN
  have h_pos : ∀ n, 0 < h n := fun n => by simp only [hh]; positivity
  have hR : ∀ n, P.Ramp + n ≤ (N n : ℝ) * h n := fun n => by
    simp only [hh, hN]
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    exact Nat.le_ceil _
  have hRamp0 : 0 ≤ P.Ramp := by
    have := P.uniformfloor.2.2.1; linarith [P.M_pos]
  have R_ge : ∀ n, P.Ramp ≤ (N n : ℝ) * h n := fun n =>
    le_trans (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) (hR n)
  have R_tendsto : Tendsto (fun n => (N n : ℝ) * h n) atTop atTop :=
    tendsto_atTop_mono (fun n => (le_add_of_nonneg_left hRamp0).trans (hR n))
      tendsto_natCast_atTop_atTop
  have h_tendsto : Tendsto h atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex := fun n => approx P (h_pos n) (R_ge n)
  choose V η κ hE hfl hfu using hex
  obtain ⟨S, -⟩ := SelectedSeq.extract P h N V η κ h_pos h_tendsto R_tendsto R_ge hE
    (fun n => ⟨hfl n, hfu n⟩)
  exact ⟨S⟩

end Molico
