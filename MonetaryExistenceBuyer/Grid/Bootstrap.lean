import MonetaryExistenceBuyer.Grid.Gauge
import MonetaryExistenceBuyer.Grid.SlopePos
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The a priori amplitude floor

Formalizes `def:direction`, `lem:r0cap`, `prop:bootstrap` (envelope bootstrap) and
`cor:uniformfloor` (uniform amplitude floor).
-/

open Set Finset Filter Topology

noncomputable section

namespace Molico

/-- Step 2 of `prop:bootstrap` (eq. `eq:Kest`): if the increments satisfy `a_j ≥ ζ ρ^j`, then the
increments of `H_V(·, s)` satisfy `H_V(m+1, l) - H_V(m, l) ≥ u'₋(V(R)) ζ ρ^(m+1+l)`, provided
`c₀ ρ^N ≤ 1`. -/
lemma bootstrap_gH_step (U : AdmissibleUtility) {N : ℕ} {V : ℕ → ℝ} (hV : IncrSeq V N)
    (hV0 : V 0 = 0) {ρ ζ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hζ : 0 ≤ ζ)
    (hNρ : U.c0 * ρ ^ N ≤ 1) (ha : ∀ j < N, ζ * ρ ^ (j + 1) ≤ V (j + 1) - V j)
    {m l : ℕ} (hm : m < N) (hl : l ≤ N) :
    U.marg (V N) * ζ * ρ ^ (m + 1 + l) ≤ Grid.gH U.u N V (m + 1) l - Grid.gH U.u N V m l := by
  have hVN : 0 ≤ V N := hV.nonneg hV0 le_rfl
  have hmg0 : 0 ≤ U.marg (V N) := (U.marg_pos hVN).le
  obtain ⟨j, hj, hjeq⟩ := Grid.exists_gH_eq U (V := V) hm.le hl
  rw [Grid.mem_feas hm.le hl] at hj
  rw [Grid.gobj] at hjeq
  by_cases hc : l + j + 1 ≤ N
  · -- use the transfer `j + 1` at `m + 1`: the retained value is unchanged
    have hj' : j + 1 ∈ Grid.feas N (m + 1) l :=
      (Grid.mem_feas (by omega) hl).2 ⟨by omega, by omega⟩
    have h1 := Grid.gobj_le_gH U (V := V) (by omega) hl hj'
    rw [Grid.gobj, show m + 1 - (j + 1) = m - j by omega,
      show l + (j + 1) = l + j + 1 by omega] at h1
    have hA : 0 ≤ V (l + j) - V l := by
      linarith [hV.le_of_le (show l ≤ l + j by omega) (by omega)]
    have hAB := hV.mono (l + j) (by omega)
    have hB : V (l + j + 1) - V l ≤ V N := by
      have := hV.gain_le hV0 (l := l) (j := j + 1) (by omega)
      rw [show l + (j + 1) = l + j + 1 by omega] at this
      exact this.trans (hV.le_of_le (by omega) le_rfl)
    have h2 := U.marg_mul_le_sub hA (show V (l + j) - V l ≤ V (l + j + 1) - V l by linarith)
    have h3 : U.marg (V N) ≤ U.marg (V (l + j + 1) - V l) :=
      U.marg_antitoneOn (show V (l + j + 1) - V l ∈ Set.Ici (0:ℝ) by
        simp only [Set.mem_Ici]; linarith) (show V N ∈ Set.Ici (0:ℝ) from hVN) hB
    have h4 := ha (l + j) (by omega)
    have h5 : ρ ^ (m + 1 + l) ≤ ρ ^ (l + j + 1) := pow_le_pow_of_le_one hρ0.le hρ1 (by omega)
    have e : V (l + j + 1) - V l - (V (l + j) - V l) = V (l + j + 1) - V (l + j) := by ring
    rw [e] at h2
    calc U.marg (V N) * ζ * ρ ^ (m + 1 + l) ≤ U.marg (V N) * (ζ * ρ ^ (l + j + 1)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hζ) hmg0
      _ ≤ U.marg (V N) * (V (l + j + 1) - V (l + j)) := mul_le_mul_of_nonneg_left h4 hmg0
      _ ≤ U.marg (V (l + j + 1) - V l) * (V (l + j + 1) - V (l + j)) :=
          mul_le_mul_of_nonneg_right h3 (by linarith)
      _ ≤ _ := by linarith
  · -- `l + j = N`: keep the transfer `j` at `m + 1`, only the retained value changes
    have hjN : l + j = N := by omega
    have hj' : j ∈ Grid.feas N (m + 1) l := (Grid.mem_feas (by omega) hl).2 ⟨by omega, by omega⟩
    have h1 := Grid.gobj_le_gH U (V := V) (by omega) hl hj'
    rw [Grid.gobj, show m + 1 - j = m - j + 1 by omega] at h1
    have h4 := ha (m - j) (by omega)
    have hpow : ρ ^ (m + 1 + l) = ρ ^ N * ρ ^ (m - j + 1) := by
      rw [← pow_add]; congr 1; omega
    have hmc : U.marg (V N) * ρ ^ N ≤ 1 :=
      (mul_le_mul_of_nonneg_right (U.marg_le_c0 hVN) (pow_nonneg hρ0.le N)).trans hNρ
    calc U.marg (V N) * ζ * ρ ^ (m + 1 + l)
        = (U.marg (V N) * ρ ^ N) * (ζ * ρ ^ (m - j + 1)) := by rw [hpow]; ring
      _ ≤ 1 * (ζ * ρ ^ (m - j + 1)) :=
          mul_le_mul_of_nonneg_right hmc (mul_nonneg hζ (pow_nonneg hρ0.le _))
      _ ≤ _ := by linarith

/-- Step 3 of `prop:bootstrap` (Jensen): for a law of mean `M`, `∑_l η_l ρ^l ≥ ρ^{M/h} = e^{-ε}`
with `ρ = e^{-εh/M}` (via the tangent line of `exp` at `-ε`). -/
lemma law_sum_pow_ge {h M : ℝ} (hM : 0 < M) {N : ℕ} {η : ℕ → ℝ} (hη : Grid.IsLaw h M N η)
    (ε : ℝ) : Real.exp (-ε) ≤ ∑ l ∈ range (N + 1), η l * Real.exp (-ε * h / M) ^ l := by
  have key : ∀ l ∈ range (N + 1),
      Real.exp (-ε) * (-ε / M) * (η l * (l * h)) + Real.exp (-ε) * (ε + 1) * η l ≤
        η l * Real.exp (-ε * h / M) ^ l := by
    intro l _
    rw [← Real.exp_nat_mul]
    have h1 := Real.add_one_le_exp ((l : ℝ) * (-ε * h / M) + ε)
    have h2 : Real.exp ((l : ℝ) * (-ε * h / M)) =
        Real.exp (-ε) * Real.exp ((l : ℝ) * (-ε * h / M) + ε) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-ε) * ((l : ℝ) * (-ε * h / M) + ε + 1) ≤
        Real.exp ((l : ℝ) * (-ε * h / M)) := by
      rw [h2]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_left h3 (hη.nonneg l)
    calc _ = η l * (Real.exp (-ε) * ((l : ℝ) * (-ε * h / M) + ε + 1)) := by ring
      _ ≤ _ := h4
  calc Real.exp (-ε) = ∑ l ∈ range (N + 1), (Real.exp (-ε) * (-ε / M) * (η l * (l * h)) +
        Real.exp (-ε) * (ε + 1) * η l) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hη.mean, hη.sum_one]
        field_simp
        ring
    _ ≤ _ := Finset.sum_le_sum key

namespace Primitives

variable (P : Primitives)

/-- `def:direction`: the geometric direction `u₀(x) = 1 - exp(-ε x / M)`. -/
def u0 (ε x : ℝ) : ℝ := 1 - Real.exp (-ε * x / P.M)

/-- `eq:r0`: the floor `r₀(ε) = sup{r > 0 : u'₋(r) > e^ε / β}`. -/
def r0 (ε : ℝ) : ℝ := sSup {r | 0 < r ∧ Real.exp ε / P.β < P.U.marg r}

/-- The truncation window `eq:epswindow`: `(M/R) log c₀ < ε < log(β c₀)` with `R = N h`. -/
def InWindow (h : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  P.M / (N * h) * Real.log P.U.c0 < ε ∧ ε < Real.log (P.β * P.U.c0)

/-- The set defining `r₀(ε)` is nonempty when `ε < log(β c₀)`: since `u'₋(0+) = c₀ > e^ε/β`. -/
lemma r0_set_nonempty {ε : ℝ} (hε1 : ε < Real.log (P.β * P.U.c0)) :
    {r | 0 < r ∧ Real.exp ε / P.β < P.U.marg r}.Nonempty := by
  have hβc : 0 < P.β * P.U.c0 := by linarith [P.active]
  have hc : Real.exp ε / P.β < P.U.c0 := by
    rw [div_lt_iff₀ P.β_pos]
    have := Real.exp_lt_exp.2 hε1
    rw [Real.exp_log hβc] at this
    linarith
  obtain ⟨r, hr1, hr2⟩ :=
    ((P.U.tendsto_marg_zero.eventually (lt_mem_nhds hc)).and self_mem_nhdsWithin).exists
  exact ⟨r, hr2, hr1⟩

/-- For `ε > 0` the set defining `r₀(ε)` is bounded above by some `z < L_*`: `u'₋(L_*) ≤ σ < e^ε/β`
and `u'₋` is upper semicontinuous and nonincreasing. -/
lemma r0_set_bound {ε : ℝ} (hε0 : 0 < ε) :
    ∃ z, z < P.Lstar ∧ ∀ r ∈ {r | 0 < r ∧ Real.exp ε / P.β < P.U.marg r}, r ≤ z := by
  have hc : P.σ < Real.exp ε / P.β := by
    have h1 : 1 < Real.exp ε := Real.one_lt_exp_iff.2 hε0
    have h2 : 1 / P.β < Real.exp ε / P.β := (div_lt_div_iff_of_pos_right P.β_pos).2 h1
    unfold σ; linarith
  have hmL : P.U.marg P.Lstar < Real.exp ε / P.β := by
    have := P.U.marg_le_slope le_rfl P.Lstar_pos
    rw [P.U.u_zero, sub_zero, sub_zero, P.u_Lstar, mul_div_assoc, div_self P.Lstar_pos.ne',
      mul_one] at this
    linarith
  have h1 := P.U.marg_upperSemicontinuousOn P.Lstar
    (show P.Lstar ∈ Ici (0:ℝ) from P.Lstar_pos.le) _ hmL
  rw [eventually_nhdsWithin_iff] at h1
  have h2 : ∀ᶠ z in 𝓝[<] P.Lstar, z ∈ Ici (0:ℝ) → P.U.marg z < Real.exp ε / P.β :=
    h1.filter_mono nhdsWithin_le_nhds
  obtain ⟨z, hz1, hz2⟩ := (h2.and (Ioo_mem_nhdsLT P.Lstar_pos)).exists
  refine ⟨z, hz2.2, fun r hr => ?_⟩
  obtain ⟨hr0, hr⟩ := hr
  by_contra hrz
  push Not at hrz
  have h3 := P.U.marg_antitoneOn (show z ∈ Ici (0:ℝ) from hz2.1.le)
    (show r ∈ Ici (0:ℝ) from hr0.le) hrz.le
  have h4 := hz1 hz2.1.le
  linarith

/-- `lem:r0cap`: for `0 < ε < log(β c₀)` (in particular for every `ε` in the window
`eq:epswindow`), `0 < r₀(ε) < L_* < C_*`. -/
theorem r0cap {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < Real.log (P.β * P.U.c0)) :
    0 < P.r0 ε ∧ P.r0 ε < P.Lstar ∧ P.Lstar < P.Cstar := by
  obtain ⟨z, hzL, hz⟩ := P.r0_set_bound hε0
  obtain ⟨r, hr⟩ := P.r0_set_nonempty hε1
  have hbdd : BddAbove {r | 0 < r ∧ Real.exp ε / P.β < P.U.marg r} := ⟨z, hz⟩
  unfold r0
  exact ⟨hr.1.trans_le (le_csSup hbdd hr), (csSup_le ⟨r, hr⟩ hz).trans_lt hzL,
    P.Lstar_lt_Cstar⟩

/-- `def:direction`: increments of `u₀` on the grid are geometric,
`u₀(jh) - u₀((j-1)h) = c_ρ ρ^j` with `ρ = e^{-εh/M}`, `c_ρ = (1-ρ)/ρ`. -/
lemma u0_incr (ε h : ℝ) (j : ℕ) :
    P.u0 ε ((j + 1 : ℕ) * h) - P.u0 ε (j * h) =
      (1 - Real.exp (-ε * h / P.M)) / Real.exp (-ε * h / P.M) *
        Real.exp (-ε * h / P.M) ^ (j + 1) := by
  have hρ : Real.exp (-ε * h / P.M) ≠ 0 := (Real.exp_pos _).ne'
  rw [pow_succ, ← Real.exp_nat_mul]
  unfold u0
  have e1 : -ε * (((j + 1 : ℕ) : ℝ) * h) / P.M = (j : ℝ) * (-ε * h / P.M) + (-ε * h / P.M) := by
    push_cast; ring
  have e2 : -ε * ((j : ℝ) * h) / P.M = (j : ℝ) * (-ε * h / P.M) := by ring
  rw [e1, e2, Real.exp_add]
  field_simp
  ring

/-- `prop:bootstrap` (envelope bootstrap). Let `ε` lie in the window `eq:epswindow`, `η ∈ 𝒫_M(𝒳)`,
`τ ≥ 0`, and `V ∈ 𝒦_{h,R}` solve `V - T_η V = τ u₀` on the grid (`eq:krasno`). Then either
`V ≡ 0` and `τ = 0`, or `V(R) ≥ r₀(ε)`. -/
theorem bootstrap {h : ℝ} (hh : 0 < h) {N : ℕ} {ε : ℝ} (hε : P.InWindow h N ε)
    {η : ℕ → ℝ} (hη : Grid.IsLaw h P.M N η) {τ : ℝ} (hτ : 0 ≤ τ) {V : ℕ → ℝ}
    (hV : Grid.InCone P.Cstar N V)
    (hfix : ∀ m ≤ N, V m - Grid.gT P.U.u P.β N η V m = τ * P.u0 ε (m * h)) :
    ((∀ i ≤ N, V i = 0) ∧ τ = 0) ∨ P.r0 ε ≤ V N := by
  by_contra hcon
  rw [not_or, not_le] at hcon
  obtain ⟨hnot, hlt⟩ := hcon
  have hM := P.M_pos
  -- the grid is nontrivial: `N ≥ 1` since the law has mean `M > 0`
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · have := hη.mean
      subst h0
      simp at this
      linarith
    · exact h0
  have hR : 0 < (N : ℝ) * h := mul_pos (Nat.cast_pos.2 hN) hh
  have hlogc0 : 0 < Real.log P.U.c0 := Real.log_pos P.c0_gt_one
  have hε0 : 0 < ε := lt_trans (mul_pos (div_pos hM hR) hlogc0) hε.1
  -- the geometric ratio `ρ = e^{-εh/M} ∈ (0,1)`
  set ρ := Real.exp (-ε * h / P.M) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by have := mul_pos hε0 hh; linarith) hM
  -- the window lower bound gives `c₀ ρ^N < 1`
  have hNρ : P.U.c0 * ρ ^ N ≤ 1 := by
    have h1 : Real.log P.U.c0 < ε * (N * h) / P.M := by
      have := hε.1
      rw [div_mul_eq_mul_div, div_lt_iff₀ hR] at this
      rw [lt_div_iff₀ hM]; linarith
    have h2 : ρ ^ N = Real.exp (-(ε * (N * h) / P.M)) := by
      rw [hρ, ← Real.exp_nat_mul]; congr 1; ring
    have h3 : P.U.c0 < Real.exp (ε * (N * h) / P.M) := by
      calc P.U.c0 = Real.exp (Real.log P.U.c0) := (Real.exp_log P.U.c0_pos).symm
        _ < _ := Real.exp_lt_exp.2 h1
    rw [h2, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    exact h3.le
  -- `V(R) < r₀(ε)` forces `u'₋(V(R)) > e^ε/β`
  have hVN : 0 ≤ V N := hV.incr.nonneg hV.zero le_rfl
  have hmarg : Real.exp ε / P.β < P.U.marg (V N) := by
    obtain ⟨r, ⟨hr0, hr⟩, hVr⟩ := exists_lt_of_lt_csSup (P.r0_set_nonempty hε.2) hlt
    exact hr.trans_le (P.U.marg_antitoneOn hVN hr0.le hVr.le)
  set lam := P.β * P.U.marg (V N) * Real.exp (-ε) with hlam_def
  have hlam : 1 < lam := by
    have h1 : Real.exp ε < P.U.marg (V N) * P.β := (div_lt_iff₀ P.β_pos).1 hmarg
    have h2 : Real.exp ε * Real.exp (-ε) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (-ε))
    rw [hlam_def]; linarith
  set cρ := (1 - ρ) / ρ with hcρ_def
  have hcρ : 0 < cρ := div_pos (by linarith) hρ0
  -- Steps 1-3: the envelope `a_j ≥ ζ ρ^j` self-improves to `a_j ≥ (λ ζ + τ c_ρ) ρ^j`
  have step3 : ∀ ζ : ℝ, 0 ≤ ζ → (∀ j < N, ζ * ρ ^ (j + 1) ≤ V (j + 1) - V j) →
      ∀ j < N, (lam * ζ + τ * cρ) * ρ ^ (j + 1) ≤ V (j + 1) - V j := by
    intro ζ hζ ha j hj
    have e1 := hfix (j + 1) (by omega)
    have e2 := hfix j hj.le
    have hu : P.u0 ε (((j + 1 : ℕ) : ℝ) * h) - P.u0 ε ((j : ℝ) * h) = cρ * ρ ^ (j + 1) :=
      P.u0_incr ε h j
    have hdiff : Grid.gT P.U.u P.β N η V (j + 1) - Grid.gT P.U.u P.β N η V j =
        P.β * ∑ l ∈ range (N + 1),
          η l * (Grid.gH P.U.u N V (j + 1) l - Grid.gH P.U.u N V j l) := by
      simp only [Grid.gT, mul_sub, Finset.sum_sub_distrib]
    have hlow : ∑ l ∈ range (N + 1), η l * (P.U.marg (V N) * ζ * ρ ^ (j + 1 + l)) ≤
        ∑ l ∈ range (N + 1), η l * (Grid.gH P.U.u N V (j + 1) l - Grid.gH P.U.u N V j l) :=
      Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left
        (bootstrap_gH_step P.U hV.incr hV.zero hρ0 hρ1.le hζ hNρ ha hj
          (by rw [Finset.mem_range] at hl; omega)) (hη.nonneg l)
    have hjen : Real.exp (-ε) ≤ ∑ l ∈ range (N + 1), η l * ρ ^ l := law_sum_pow_ge hM hη ε
    have hsum_eq : ∑ l ∈ range (N + 1), η l * (P.U.marg (V N) * ζ * ρ ^ (j + 1 + l)) =
        P.U.marg (V N) * ζ * ρ ^ (j + 1) * ∑ l ∈ range (N + 1), η l * ρ ^ l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [pow_add]; ring
    have hmg0 : 0 ≤ P.U.marg (V N) * ζ * ρ ^ (j + 1) :=
      mul_nonneg (mul_nonneg (P.U.marg_pos hVN).le hζ) (pow_nonneg hρ0.le _)
    have h1 := mul_le_mul_of_nonneg_left hjen hmg0
    rw [← hsum_eq] at h1
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hlow) P.β_pos.le
    rw [← hdiff] at h2
    have e3 : (lam * ζ + τ * cρ) * ρ ^ (j + 1) =
        P.β * (P.U.marg (V N) * ζ * ρ ^ (j + 1) * Real.exp (-ε)) + τ * (cρ * ρ ^ (j + 1)) := by
      rw [hlam_def]; ring
    rw [e3, ← hu]
    linarith
  rcases hτ.eq_or_lt with hτ0 | hτpos
  · -- `τ = 0`: a nonzero fixed point; compare with the minimal envelope ratio
    have hne : ∃ i ≤ N, V i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hnot ⟨hall, hτ0.symm⟩
    have hbell : ∀ m ≤ N, V m = Grid.gT P.U.u P.β N η V m := fun m hm => by
      have := hfix m hm
      rw [← hτ0, zero_mul] at this
      linarith
    have hpos := slopepos P.U P.β_pos P.β_lt_one hV.incr hV.zero hη.nonneg hη.sum_one hbell hne
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (range N)
      (fun j => (V (j + 1) - V j) / ρ ^ (j + 1)) ⟨0, Finset.mem_range.2 hN⟩
    have hj0N : j0 < N := Finset.mem_range.1 hj0
    have hζ : 0 < (V (j0 + 1) - V j0) / ρ ^ (j0 + 1) :=
      div_pos (sub_pos.2 (hpos j0 hj0N)) (pow_pos hρ0 _)
    have hall : ∀ j < N, (V (j0 + 1) - V j0) / ρ ^ (j0 + 1) * ρ ^ (j + 1) ≤ V (j + 1) - V j := by
      intro j hj
      exact (le_div_iff₀ (pow_pos hρ0 _)).1 (hmin j (Finset.mem_range.2 hj))
    have h3 := step3 _ hζ.le hall j0 hj0N
    have hζdef : (V (j0 + 1) - V j0) / ρ ^ (j0 + 1) * ρ ^ (j0 + 1) = V (j0 + 1) - V j0 :=
      div_mul_cancel₀ _ (pow_pos hρ0 _).ne'
    rw [← hτ0, zero_mul, add_zero, mul_assoc, hζdef] at h3
    have hp : 0 < V (j0 + 1) - V j0 := sub_pos.2 (hpos j0 hj0N)
    nlinarith
  · -- `τ > 0`: iterating gives `a_1 ≥ (k+1) τ c_ρ ρ` for every `k`, contradicting `a_1 ≤ V(R)`
    have hiter : ∀ k : ℕ, ∀ j < N, ((k : ℝ) + 1) * (τ * cρ) * ρ ^ (j + 1) ≤ V (j + 1) - V j := by
      intro k
      induction k with
      | zero =>
        intro j hj
        have := step3 0 le_rfl (fun j hj => by rw [zero_mul]; linarith [hV.incr.mono j hj]) j hj
        have e : (((0 : ℕ) : ℝ) + 1) * (τ * cρ) * ρ ^ (j + 1) = (lam * 0 + τ * cρ) * ρ ^ (j + 1) := by
          push_cast; ring
        rw [e]; exact this
      | succ k ih =>
        intro j hj
        have hz : 0 ≤ ((k : ℝ) + 1) * (τ * cρ) :=
          mul_nonneg (by positivity) (mul_nonneg hτ hcρ.le)
        have := step3 _ hz ih j hj
        have hle : (((k + 1 : ℕ) : ℝ) + 1) * (τ * cρ) ≤ lam * (((k : ℝ) + 1) * (τ * cρ)) + τ * cρ := by
          push_cast; nlinarith
        exact (mul_le_mul_of_nonneg_right hle (pow_nonneg hρ0.le _)).trans this
    have hpos : 0 < τ * cρ * ρ := mul_pos (mul_pos hτpos hcρ) hρ0
    obtain ⟨k, hk⟩ := exists_nat_gt (V N / (τ * cρ * ρ))
    rw [div_lt_iff₀ hpos] at hk
    have h1 := hiter k 0 hN
    rw [hV.zero, sub_zero, zero_add, pow_one] at h1
    have h2 : V 1 ≤ V N := hV.incr.le_of_le hN le_rfl
    nlinarith

/-- `prop:bootstrap`, "in particular": every nonzero grid fixed point satisfies `V(R) ≥ r₀(ε)`
for every `ε` in the window, hence `V(R) ≥ r₀^*(R)`. -/
theorem bootstrap_fixed {h : ℝ} (hh : 0 < h) {N : ℕ} {ε : ℝ} (hε : P.InWindow h N ε)
    {η : ℕ → ℝ} (hη : Grid.IsLaw h P.M N η) {V : ℕ → ℝ} (hV : Grid.InCone P.Cstar N V)
    (hbell : ∀ m ≤ N, V m = Grid.gT P.U.u P.β N η V m) (hne : ∃ i ≤ N, V i ≠ 0) :
    P.r0 ε ≤ V N := by
  rcases P.bootstrap hh hε hη le_rfl hV (fun m hm => by rw [← hbell m hm]; simp) with h | h
  · obtain ⟨i, hi, hne⟩ := hne; exact absurd (h.1 i hi) hne
  · exact h

/-! ### The uniform amplitude floor (`cor:uniformfloor`) -/

/-- `ε_amp = log(β c₀)/2 ∈ (0, log(β c₀))`. -/
def εamp : ℝ := Real.log (P.β * P.U.c0) / 2

/-- The direction `u₀` of `cor:uniformfloor`, independent of `h` and `R`. -/
def u0amp (x : ℝ) : ℝ := P.u0 P.εamp x

/-- The uniform amplitude floor `ℓ₀`. -/
def ℓ0 : ℝ := P.r0 P.εamp / 2

/-- The truncation threshold `R_amp > M log c₀ / ε_amp`, `R_amp > M`. -/
def Ramp : ℝ := 2 * P.M * Real.log P.U.c0 / P.εamp + P.M

/-- `cor:uniformfloor`: `0 < ℓ₀ < L_*`, `R_amp > M`, `u₀` is strictly increasing and concave
with values in `[0,1)` and `u₀(0) = 0`; for every grid with `R ≥ R_amp`, every solution of
`eq:krasno` with direction `u₀` satisfies either `V ≡ 0, τ = 0` or `V(R) ≥ ℓ₀`. -/
theorem uniformfloor :
    0 < P.ℓ0 ∧ P.ℓ0 < P.Lstar ∧ P.M < P.Ramp ∧
    P.u0amp 0 = 0 ∧ StrictMonoOn P.u0amp (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) P.u0amp ∧
    (∀ x, 0 ≤ x → P.u0amp x ∈ Set.Ico 0 1) ∧
    ∀ {h : ℝ}, 0 < h → ∀ {N : ℕ}, P.Ramp ≤ N * h →
      ∀ {η : ℕ → ℝ}, Grid.IsLaw h P.M N η → ∀ {τ : ℝ}, 0 ≤ τ →
      ∀ {V : ℕ → ℝ}, Grid.InCone P.Cstar N V →
      (∀ m ≤ N, V m - Grid.gT P.U.u P.β N η V m = τ * P.u0amp (m * h)) →
      ((∀ i ≤ N, V i = 0) ∧ τ = 0) ∨ P.ℓ0 ≤ V N := by
  have hlogβc : 0 < Real.log (P.β * P.U.c0) := Real.log_pos P.active
  have hεa0 : 0 < P.εamp := by unfold εamp; positivity
  have hεa1 : P.εamp < Real.log (P.β * P.U.c0) := by unfold εamp; linarith
  obtain ⟨hr0, hrL, -⟩ := P.r0cap hεa0 hεa1
  have hM := P.M_pos
  have hlogc0 : 0 < Real.log P.U.c0 := Real.log_pos P.c0_gt_one
  have hRamp : P.M < P.Ramp := by
    unfold Ramp
    have : 0 < 2 * P.M * Real.log P.U.c0 / P.εamp := by positivity
    linarith
  refine ⟨by unfold ℓ0; linarith, by unfold ℓ0; linarith, hRamp, ?_, ?_, ?_, ?_, ?_⟩
  · simp [u0amp, u0]
  · intro x _ y _ hxy
    simp only [u0amp, u0]
    have h1 : -P.εamp * y / P.M < -P.εamp * x / P.M :=
      (div_lt_div_iff_of_pos_right hM).2 (by nlinarith)
    have h2 := Real.exp_lt_exp.2 h1
    linarith
  · refine ⟨convex_Ici 0, fun x _ y _ a b ha hb hab => ?_⟩
    have hc := convexOn_exp.2 (Set.mem_univ (-P.εamp * x / P.M))
      (Set.mem_univ (-P.εamp * y / P.M)) ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    simp only [u0amp, u0]
    have e : -P.εamp * (a * x + b * y) / P.M =
        a * (-P.εamp * x / P.M) + b * (-P.εamp * y / P.M) := by ring
    rw [e]
    linarith
  · intro x hx
    simp only [u0amp, u0, Set.mem_Ico]
    have h1 : -P.εamp * x / P.M ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) hM.le
    exact ⟨by linarith [Real.exp_le_one_iff.2 h1], by linarith [Real.exp_pos (-P.εamp * x / P.M)]⟩
  · intro h hh N hR η hη τ hτ V hV hfix
    have hR0 : 0 < (N : ℝ) * h := by linarith
    have hwin : P.InWindow h N P.εamp := by
      refine ⟨?_, hεa1⟩
      rw [div_mul_eq_mul_div, div_lt_iff₀ hR0]
      have h1 : P.εamp * P.Ramp ≤ P.εamp * (N * h) := mul_le_mul_of_nonneg_left hR hεa0.le
      have h2 : P.εamp * P.Ramp = 2 * P.M * Real.log P.U.c0 + P.εamp * P.M := by
        unfold Ramp; field_simp
      have h3 := mul_pos hM hlogc0
      have h4 := mul_pos hεa0 hM
      linarith
    rcases P.bootstrap hh hwin hη hτ hV hfix with h0 | h1
    · exact Or.inl h0
    · right; unfold ℓ0; linarith

/-- `cor:uniformfloor`, eq. `eq:uniformfloor`: every nonzero grid Bellman fixed point in
`𝒦_{h,R}` with seller law of mean `M` satisfies `ℓ₀ ≤ V(R) ≤ L_*`. -/
theorem uniformfloor_fixed {h : ℝ} (hh : 0 < h) {N : ℕ} (hR : P.Ramp ≤ N * h)
    {η : ℕ → ℝ} (hη : Grid.IsLaw h P.M N η) {V : ℕ → ℝ} (hV : Grid.InCone P.Cstar N V)
    (hbell : ∀ m ≤ N, V m = Grid.gT P.U.u P.β N η V m) (hne : ∃ i ≤ N, V i ≠ 0) :
    P.ℓ0 ≤ V N ∧ V N ≤ P.Lstar := by
  refine ⟨?_, (gauge_grid P hV.incr hV.zero hη.nonneg hη.sum_one hbell le_rfl).2⟩
  rcases (P.uniformfloor).2.2.2.2.2.2.2 hh hR hη le_rfl hV (fun m hm => by
    rw [← hbell m hm]; simp) with h | h
  · obtain ⟨i, hi, hne⟩ := hne; exact absurd (h.1 i hi) hne
  · exact h

end Primitives

end Molico
