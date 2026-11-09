import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Passage of support conditions (`lem:device`)

(a) is the Portmanteau theorem (Mathlib). (b) says that if `μ_n(E_n) = 1` then the limit `μ` is
carried by `E_∞ = ⋂_k closure (⋃_{n ≥ k} E_n)`, and every point of `E_∞` is a limit of points
`x_j ∈ E_{n_j}` with `n_j → ∞`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Molico

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/-- `lem:device` (a): the Portmanteau inequalities for closed and open sets. -/
theorem device_a {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (h : Tendsto μs atTop (𝓝 μ)) :
    (∀ C, IsClosed C → limsup (fun n => (μs n : Measure Ω) C) atTop ≤ (μ : Measure Ω) C) ∧
    (∀ U, IsOpen U → (μ : Measure Ω) U ≤ liminf (fun n => (μs n : Measure Ω) U) atTop) :=
  ⟨fun _ hC => ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hC,
    fun _ hU => ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hU⟩

/-- `lem:device` (b), first part: `μ(E_∞) = 1`. -/
theorem device_b {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (h : Tendsto μs atTop (𝓝 μ)) {E : ℕ → Set Ω} (hE : ∀ n, (μs n : Measure Ω) (E n) = 1) :
    (μ : Measure Ω) (⋂ k, closure (⋃ n ≥ k, E n)) = 1 := by
  have hk : ∀ k, (μ : Measure Ω) (closure (⋃ n ≥ k, E n)) = 1 := by
    intro k
    refine le_antisymm prob_le_one ?_
    have hev : ∀ᶠ n in atTop, (μs n : Measure Ω) (closure (⋃ n ≥ k, E n)) = 1 := by
      filter_upwards [eventually_ge_atTop k] with n hn
      refine le_antisymm prob_le_one ?_
      rw [← hE n]
      exact measure_mono (subset_closure.trans' (subset_biUnion_of_mem (u := E) hn))
    calc (1 : ℝ≥0∞) = limsup (fun n => (μs n : Measure Ω) (closure (⋃ n ≥ k, E n))) atTop := by
          rw [limsup_congr hev, limsup_const]
      _ ≤ _ := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h isClosed_closure
  rw [← prob_compl_eq_zero_iff (MeasurableSet.iInter fun k => isClosed_closure.measurableSet),
    compl_iInter]
  exact measure_iUnion_null fun k => (prob_compl_eq_zero_iff isClosed_closure.measurableSet).2 (hk k)

/-- `lem:device` (b), second part: every point of `E_∞` is a limit of points `x_j ∈ E_{n_j}`
with `n_j → ∞`. -/
theorem device_b_points {E : ℕ → Set Ω} {x : Ω} (hx : x ∈ ⋂ k, closure (⋃ n ≥ k, E n)) :
    ∃ n : ℕ → ℕ, ∃ y : ℕ → Ω, Tendsto n atTop atTop ∧ (∀ j, y j ∈ E (n j)) ∧
      Tendsto y atTop (𝓝 x) := by
  have hj : ∀ j : ℕ, ∃ n, j ≤ n ∧ ∃ y ∈ E n, dist x y < 1 / ((j : ℝ) + 1) := by
    intro j
    have := Metric.mem_closure_iff.1 (mem_iInter.1 hx j) (1 / ((j : ℝ) + 1)) (by positivity)
    obtain ⟨y, hy, hd⟩ := this
    simp only [mem_iUnion] at hy
    obtain ⟨n, hn, hyn⟩ := hy
    exact ⟨n, hn, y, hyn, hd⟩
  choose n hn y hy hd using hj
  refine ⟨n, y, tendsto_atTop_mono hn tendsto_id, hy, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun j => dist_nonneg) (fun j => (dist_comm (y j) x).le.trans (hd j).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end Molico
