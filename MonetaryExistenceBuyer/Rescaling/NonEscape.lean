import MonetaryExistenceBuyer.Rescaling.Props

/-!
# The non-escaping normalized wealth mass (`prop:non-escape`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

/-- Concavity through the origin in index form: `V(k) ≤ k V(1)`. -/
private lemma core_le_nat_mul_one {V : ℕ → ℝ} {N : ℕ} (hV : IncrSeq V N) (hV0 : V 0 = 0) :
    ∀ k ≤ N, V k ≤ k * V 1 := by
  intro k hk
  induction k with
  | zero => simp [hV0]
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := hV.step_anti (x := 0) (y := k) (Nat.zero_le k) hk
    simp only [zero_add, hV0, sub_zero] at h2
    push_cast
    linarith

/-- All slopes up to index `l + 1` are at least the slope at `l + 1`: `k (V(l+1) - V(l)) ≤ V(k)`
for `k ≤ l + 1`. -/
private lemma core_nat_mul_slope_le {V : ℕ → ℝ} {N : ℕ} (hV : IncrSeq V N) (hV0 : V 0 = 0)
    {l : ℕ} (hl : l + 1 ≤ N) : ∀ k ≤ l + 1, (k : ℝ) * (V (l + 1) - V l) ≤ V k := by
  intro k hk
  induction k with
  | zero => simp [hV0]
  | succ k ih =>
    have h1 := ih (by omega)
    have h2 := hV.step_anti (x := k) (y := l) (by omega) hl
    push_cast
    linarith

/-- The first-row Bellman estimate (`eq:originrow`, first half, in index form): the sellers whose
next slope exceeds `V(1)/c₀` carry mass at least `μ_c`. -/
private lemma core_sum {h : ℝ} {N : ℕ} {V η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ}
    (E : Grid.IsApproxEq P h N V η κ) (h1N : 1 ≤ N) (hV1 : 0 < V 1) :
    P.μc ≤ ∑ l ∈ (Finset.range (N + 1)).filter
      (fun l => l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)), η l := by
  have hV0 := E.cone.zero
  have hV := E.cone.incr
  have hc0 := P.c0_gt_one
  set s := ∑ l ∈ (Finset.range (N + 1)).filter
      (fun l => l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)), η l with hs
  have hbound : ∀ l ∈ Finset.range (N + 1), η l * Grid.gH P.U.u N V 1 l ≤
      η l * V 1 + (P.U.c0 - 1) * V 1 *
        (if (l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)) then η l else 0) := by
    intro l hl
    rw [Finset.mem_range] at hl
    have hpos : 0 ≤ (P.U.c0 - 1) * V 1 := mul_nonneg (by linarith) hV1.le
    have hg : Grid.gH P.U.u N V 1 l ≤ V 1 +
        (if (l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)) then (P.U.c0 - 1) * V 1 else 0) := by
      obtain ⟨j, hj, hjeq⟩ := Grid.exists_gH_eq P.U (V := V) h1N (by omega : l ≤ N)
      rw [Grid.mem_feas h1N (by omega)] at hj
      rw [← hjeq]
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · rw [Grid.gobj_zero P.U hV0]
        split_ifs <;> linarith
      · have hd0 : 0 ≤ V (l + 1) - V l := by linarith [hV.mono l (by omega)]
        have hd1 : V (l + 1) - V l ≤ V 1 := hV.gain_le hV0 (l := l) (j := 1) hj.2
        have hu := P.U.le_c0_mul hd0
        have he : Grid.gobj P.U.u V 1 l 1 = P.U.u (V (l + 1) - V l) := by
          simp [Grid.gobj, hV0]
        rw [he]
        split_ifs with hp
        · have := mul_le_mul_of_nonneg_left hd1 (by linarith : (0:ℝ) ≤ P.U.c0)
          linarith
        · have : ¬ V 1 < P.U.c0 * (V (l + 1) - V l) := fun h' => hp ⟨by omega, h'⟩
          push Not at this
          linarith
    have hη := E.law.nonneg l
    calc η l * Grid.gH P.U.u N V 1 l
        ≤ η l * (V 1 + (if (l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)) then
            (P.U.c0 - 1) * V 1 else 0)) := mul_le_mul_of_nonneg_left hg hη
      _ = _ := by split_ifs <;> ring
  have hsum : ∑ l ∈ Finset.range (N + 1), η l * Grid.gH P.U.u N V 1 l ≤
      V 1 + (P.U.c0 - 1) * V 1 * s := by
    calc ∑ l ∈ Finset.range (N + 1), η l * Grid.gH P.U.u N V 1 l
        ≤ ∑ l ∈ Finset.range (N + 1), (η l * V 1 + (P.U.c0 - 1) * V 1 *
          (if (l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)) then η l else 0)) :=
          Finset.sum_le_sum hbound
      _ = (∑ l ∈ Finset.range (N + 1), η l) * V 1 + (P.U.c0 - 1) * V 1 *
          ∑ l ∈ Finset.range (N + 1),
            (if (l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)) then η l else 0) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = V 1 + (P.U.c0 - 1) * V 1 * s := by
          rw [E.law.sum_one, hs, Finset.sum_filter]; ring
  have hb := E.bellman 1 h1N
  unfold Grid.gT at hb
  have h2 : V 1 ≤ P.β * (V 1 + (P.U.c0 - 1) * V 1 * s) := by
    calc V 1 = _ := hb
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum P.β_pos.le
  have h3 : 1 ≤ P.β * (1 + (P.U.c0 - 1) * s) := by
    have e : V 1 * (P.β * (1 + (P.U.c0 - 1) * s)) = P.β * (V 1 + (P.U.c0 - 1) * V 1 * s) := by
      ring
    have : V 1 * 1 ≤ V 1 * (P.β * (1 + (P.U.c0 - 1) * s)) := by rw [e]; linarith
    exact le_of_mul_le_mul_left this hV1
  have h4 : 1 / P.β ≤ 1 + (P.U.c0 - 1) * s := by
    rw [div_le_iff₀ P.β_pos]; linarith
  unfold Primitives.μc
  rw [div_le_iff₀ (by linarith)]
  unfold Primitives.σ
  linarith

/-- `eq:originrow` + the crossing, for a single approximant equilibrium: if the crossing index
`c ≥ 1` satisfies `V(c) ≥ a`, then `η({s : s/(h c) ≤ K_a}) ≥ μ_c`. -/
private lemma core_grid {h : ℝ} {N : ℕ} {V η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ}
    (E : Grid.IsApproxEq P h N V η κ) (hh : 0 < h) {a : ℝ} (ha : 0 < a) {c : ℕ} (hc1 : 1 ≤ c)
    (hcN : c ≤ N) (hac : a ≤ V c) :
    ENNReal.ofReal P.μc ≤ gridMeasure h N η
      {s | ENNReal.ofReal (s / (h * c)) ≤ ENNReal.ofReal (P.U.c0 * P.Cstar / a)} := by
  have hV0 := E.cone.zero
  have hV := E.cone.incr
  have hVC := E.cone.le
  have hc0 := P.c0_gt_one
  have h1N : 1 ≤ N := hc1.trans hcN
  have hcV : V c ≤ c * V 1 := core_le_nat_mul_one hV hV0 c hcN
  have hcpos : (0:ℝ) < c := by exact_mod_cast hc1
  have hV1 : 0 < V 1 := by
    by_contra hneg
    push Not at hneg
    have : (c : ℝ) * V 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcpos.le hneg
    linarith
  have hμ := core_sum E h1N hV1
  set T := (Finset.range (N + 1)).filter
      (fun l => l < N ∧ V 1 < P.U.c0 * (V (l + 1) - V l)) with hT
  set K := P.U.c0 * P.Cstar / a with hK
  set A := {s : ℝ | ENNReal.ofReal (s / (h * c)) ≤ ENNReal.ofReal K} with hA
  have hmem : ∀ l ∈ T, (l : ℝ) * h ∈ A := by
    intro l hl
    rw [hT, Finset.mem_filter, Finset.mem_range] at hl
    obtain ⟨-, hlN, hlt⟩ := hl
    show ENNReal.ofReal ((l : ℝ) * h / (h * c)) ≤ ENNReal.ofReal K
    apply ENNReal.ofReal_le_ofReal
    have hd := core_nat_mul_slope_le hV hV0 (l := l) (by omega) (l + 1) le_rfl
    have hCl := hVC (l + 1) (by omega)
    push_cast at hd
    have h1 : ((l : ℝ) + 1) * V 1 ≤ P.U.c0 * P.Cstar := by
      calc ((l : ℝ) + 1) * V 1 ≤ ((l : ℝ) + 1) * (P.U.c0 * (V (l + 1) - V l)) :=
            mul_le_mul_of_nonneg_left hlt.le (by positivity)
        _ = P.U.c0 * (((l : ℝ) + 1) * (V (l + 1) - V l)) := by ring
        _ ≤ P.U.c0 * P.Cstar :=
            mul_le_mul_of_nonneg_left (hd.trans hCl) (by linarith)
    have hh0 : h ≠ 0 := hh.ne'
    have hc0' : (c : ℝ) ≠ 0 := hcpos.ne'
    rw [show (l : ℝ) * h / (h * c) = l / c by field_simp, hK, div_le_div_iff₀ hcpos ha]
    calc (l : ℝ) * a ≤ l * (c * V 1) :=
          mul_le_mul_of_nonneg_left (hac.trans hcV) (Nat.cast_nonneg l)
      _ ≤ c * ((l + 1) * V 1) := by nlinarith
      _ ≤ c * (P.U.c0 * P.Cstar) := mul_le_mul_of_nonneg_left h1 hcpos.le
      _ = P.U.c0 * P.Cstar * c := by ring
  have hAm : MeasurableSet A :=
    measurableSet_le (ENNReal.measurable_ofReal.comp (measurable_id.div_const _))
      measurable_const
  calc ENNReal.ofReal P.μc ≤ ENNReal.ofReal (∑ l ∈ T, η l) := ENNReal.ofReal_le_ofReal hμ
    _ = ∑ l ∈ T, ENNReal.ofReal (η l) :=
        ENNReal.ofReal_sum_of_nonneg fun l _ => E.law.nonneg l
    _ ≤ gridMeasure h N η A := by
        rw [gridMeasure_apply E.law.nonneg hAm]
        refine le_trans ?_ (Finset.sum_le_sum_of_subset
          (show T ⊆ Finset.range (N + 1) from Finset.filter_subset _ _))
        refine Finset.sum_le_sum fun l hl => ?_
        rw [ite_eq_left (hmem l hl)]

/-- `prop:non-escape` (non-escaping normalized wealth mass), eq. `eq:non-escape`:
`α({0 ≤ z ≤ K_a}) ≥ μ_c` with `K_a = c₀ C_* / a`. -/
theorem NormalizedLimit.nonEscape {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) :
    ENNReal.ofReal P.μc ≤ NL.α {p | p.1 ≤ ENNReal.ofReal (P.U.c0 * P.Cstar / a)} := by
  set K := P.U.c0 * P.Cstar / a with hK
  have hC : IsClosed {p : ℝ≥0∞ × ℝ | p.1 ≤ ENNReal.ofReal K} :=
    isClosed_le continuous_fst continuous_const
  have hmeas : ∀ n, Measurable (S.ι a n) := fun n =>
    (ENNReal.measurable_ofReal.comp (measurable_id.div_const _)).prodMk
      (continuous_interp (S.h_pos n)).measurable
  have hprobη : ∀ n, IsProbabilityMeasure (S.ηn n) := fun n =>
    gridMeasure_isProb (S.isApproxEq n).law
  have hprob : ∀ n, IsProbabilityMeasure (S.αn a n) := fun n => by
    exact (Measure.isProbabilityMeasure_map_iff (hmeas n).aemeasurable).mpr (hprobη n)
  have hgrid : ∀ n, ENNReal.ofReal P.μc ≤ S.αn a n {p | p.1 ≤ ENNReal.ofReal K} := by
    intro n
    rw [SelectedSeq.αn, Measure.map_apply (hmeas n) hC.measurableSet]
    set C := {i | i ≤ S.N n ∧ a ≤ S.V n i} with hCdef
    by_cases hne : C.Nonempty
    · have hmem : S.crossIdx a n ∈ C := Nat.sInf_mem hne
      obtain ⟨hcN, hac⟩ := hmem
      have hc1 : 1 ≤ S.crossIdx a n := by
        by_contra h0
        have h0' : S.crossIdx a n = 0 := by omega
        rw [h0', (S.isApproxEq n).cone.zero] at hac
        linarith
      exact core_grid (S.isApproxEq n) (S.h_pos n) ha hc1 hcN hac
    · have hCe : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have h0 : S.crossIdx a n = 0 := by
        show sInf C = 0
        rw [hCe, Nat.sInf_empty]
      have hpre : S.ι a n ⁻¹' {p : ℝ≥0∞ × ℝ | p.1 ≤ ENNReal.ofReal K} = Set.univ := by
        ext s
        simp [SelectedSeq.ι, SelectedSeq.scale, h0]
      rw [hpre, measure_univ]
      exact ENNReal.ofReal_le_one.mpr P.μc_lt_one.le
  exact NL.α_conv.le_measure_closed (fun n => hprob (NL.φ n)) NL.α_prob hC
    (Eventually.of_forall fun n => hgrid (NL.φ n))

end Molico
