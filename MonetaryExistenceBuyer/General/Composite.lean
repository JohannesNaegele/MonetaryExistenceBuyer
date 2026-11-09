import MonetaryExistenceBuyer.General
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The inverse cost `K⁻¹` and the composite utility `u = U ∘ K⁻¹` (`def:compositeutility`)

Elementary properties used to translate between the general model (`def:generaleq`) and the
buyer-takes-all specialization (`def:eq`).
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace Molico.Environment

variable (E : Environment)

theorem Kinv_mem {x : ℝ} (hx : 0 ≤ x) : E.Kinv x ∈ E.Q := (E.Kinv_spec hx).1

theorem K_Kinv {x : ℝ} (hx : 0 ≤ x) : E.K (E.Kinv x) = x := (E.Kinv_spec hx).2

private lemma zero_mem_Q : (0 : ℝ) ∈ E.Q := ⟨le_rfl, by simpa using E.qbar_pos⟩

/-- `Q` is an initial segment of `[0, ∞)`. -/
private lemma mem_Q_of_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ∈ E.Q) : p ∈ E.Q :=
  ⟨hp, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hpq) hq.2⟩

theorem K_nonneg {q : ℝ} (hq : q ∈ E.Q) : 0 ≤ E.K q := by
  have := E.K_strictMono.monotoneOn E.zero_mem_Q hq hq.1
  rwa [E.K_zero] at this

theorem Kinv_K {q : ℝ} (hq : q ∈ E.Q) : E.Kinv (E.K q) = q :=
  E.K_strictMono.injOn (E.Kinv_mem (E.K_nonneg hq)) hq (E.K_Kinv (E.K_nonneg hq))

theorem Kinv_zero : E.Kinv 0 = 0 := by
  have := E.Kinv_K E.zero_mem_Q
  rwa [E.K_zero] at this

theorem Kinv_strictMonoOn : StrictMonoOn E.Kinv (Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) ≤ x := hx
  have hy' : (0:ℝ) ≤ y := hy
  rw [← E.K_strictMono.lt_iff_lt (E.Kinv_mem hx') (E.Kinv_mem hy'), E.K_Kinv hx', E.K_Kinv hy']
  exact hxy

theorem Kinv_pos {x : ℝ} (hx : 0 < x) : 0 < E.Kinv x := by
  have := E.Kinv_strictMonoOn (mem_Ici.2 le_rfl) (show x ∈ Ici 0 from hx.le) hx
  rwa [E.Kinv_zero] at this

private lemma Kinv_right {a : ℝ} (ha : 0 ≤ a) : ContinuousWithinAt E.Kinv (Ici a) a := by
  refine E.Kinv_strictMonoOn.continuousWithinAt_right_of_exists_between
    (mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.2 ha)) fun b hb => ?_
  have hQ := E.Kinv_mem ha
  obtain ⟨r', -, hr', hr'Q⟩ := ENNReal.lt_iff_exists_real_btwn.1 hQ.2
  have hlt : E.Kinv a < r' := (ENNReal.ofReal_lt_ofReal_iff'.1 hr').1
  set q := min b r'
  have hq0 : 0 ≤ q := hQ.1.trans (lt_min hb hlt).le
  have hqQ : q ∈ E.Q := ⟨hq0, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_right _ _)) hr'Q⟩
  refine ⟨E.K q, E.K_nonneg hqQ, ?_⟩
  rw [E.Kinv_K hqQ]
  exact ⟨lt_min hb hlt, min_le_left _ _⟩

private lemma Kinv_left {a : ℝ} (ha : 0 < a) : ContinuousWithinAt E.Kinv (Iic a) a := by
  refine E.Kinv_strictMonoOn.continuousWithinAt_left_of_exists_between
    (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds ha)) fun b hb => ?_
  have hpos := E.Kinv_pos ha
  set q := max b 0
  have hqlt : q < E.Kinv a := max_lt hb hpos
  have hqQ : q ∈ E.Q := E.mem_Q_of_le (le_max_right _ _) hqlt.le (E.Kinv_mem ha.le)
  refine ⟨E.K q, E.K_nonneg hqQ, ?_⟩
  rw [E.Kinv_K hqQ]
  exact ⟨le_max_left _ _, hqlt⟩

theorem continuousOn_Kinv : ContinuousOn E.Kinv (Ici 0) := by
  intro a ha
  have ha' : (0:ℝ) ≤ a := ha
  rcases ha'.eq_or_lt with rfl | hpos
  · exact E.Kinv_right le_rfl
  · exact (continuousAt_iff_continuous_left_right.2
      ⟨E.Kinv_left hpos, E.Kinv_right ha'⟩).continuousWithinAt

theorem measurable_Kinv_max : Measurable fun x : ℝ => E.Kinv (max x 0) := by
  refine Monotone.measurable fun x y hxy => ?_
  exact E.Kinv_strictMonoOn.monotoneOn (mem_Ici.2 (le_max_right x 0))
    (mem_Ici.2 (le_max_right y 0)) (max_le_max hxy le_rfl)

theorem u_zero : E.u 0 = 0 := by
  simp [u, E.Kinv_zero, E.U_zero]

theorem u_monotoneOn : MonotoneOn E.u (Ici 0) := fun _ hx _ hy hxy =>
  E.U_strictMono.monotoneOn (E.Kinv_mem hx) (E.Kinv_mem hy)
    (E.Kinv_strictMonoOn.monotoneOn hx hy hxy)

theorem continuousOn_u : ContinuousOn E.u (Ici 0) :=
  E.U_cont.comp E.continuousOn_Kinv fun _ hx => E.Kinv_mem hx

/-- Output whose cost is at most `x` gives utility at most `u(x)`. -/
theorem U_le_u {q x : ℝ} (hq : q ∈ E.Q) (hx : 0 ≤ x) (hK : E.K q ≤ x) : E.U q ≤ E.u x := by
  have h1 : q ≤ E.Kinv x := by
    have := E.Kinv_strictMonoOn.monotoneOn (show E.K q ∈ Ici 0 from E.K_nonneg hq)
      (show x ∈ Ici 0 from hx) hK
    rwa [E.Kinv_K hq] at this
  exact E.U_strictMono.monotoneOn hq (E.Kinv_mem hx) h1

end Molico.Environment
