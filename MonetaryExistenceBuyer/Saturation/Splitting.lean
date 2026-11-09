import MonetaryExistenceBuyer.Saturation.Inversion

/-!
# Uniform wealth splitting at large buyer wealth (`thm:splitting`)

Proof outline (`c = 1/2`, `ω = 1/(4R)`):
* `thick_tight`: by tightness of `α` at `z = ∞`, the sellers with `lδ_n < K_E` eventually carry
  `η̃_n`-mass `> 3/4` (Portmanteau for the open set `{z < K_E}`).
* `thick_markov`: by `eq:adjnorm` and Markov's inequality, the sellers with
  `H_V(i,l) - H_V(i-1,l) > (4/β) (V(i) - V(i-1))` carry mass `≤ 1/4`.
* `thick_landing`: a uniform form of `lem:inversion`, obtained from the sequential one by
  extracting a violating subsequence and filling the remaining indices with `i = r = N_n`
  (`N_n δ_n → ∞`, `thick_Nδ_tendsto`).
* `neighbour` at every optimiser of a good seller gives slope bounds at both landing indices,
  hence both landing shares are at least `ω` (`thick_share`).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### Elementary facts about the normalized grid -/

private lemma thick_δ'_nonneg {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a) (n : ℕ) :
    0 ≤ NL.δ' n :=
  div_nonneg (S.h_pos _).le (mul_nonneg (S.h_pos _).le (Nat.cast_nonneg _))

private lemma thick_Nn_pos {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a) (n : ℕ) :
    1 ≤ NL.Nn n := by
  by_contra hcon
  have h0 : S.N (NL.φ n) = 0 := by
    have : NL.Nn n = S.N (NL.φ n) := rfl
    omega
  have hm := (S.isApproxEq (NL.φ n)).law.mean
  rw [h0] at hm
  simp at hm
  linarith [P.M_pos]

private lemma thick_slope_nonneg {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a) (n : ℕ)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ NL.Nn n) : 0 ≤ NL.slope n i := by
  unfold NormalizedLimit.slope
  apply div_nonneg _ (thick_δ'_nonneg NL n)
  have hi' : i ≤ S.N (NL.φ n) := hi
  have := (S.isApproxEq (NL.φ n)).cone.incr.mono (i - 1) (by omega)
  rw [Nat.sub_add_cancel hi1] at this
  linarith

private lemma thick_slope_le {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a) {n x i : ℕ}
    {D : ℝ} (h : S.V (NL.φ n) x - S.V (NL.φ n) (x - 1) ≤
      D * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1))) :
    NL.slope n x ≤ D * NL.slope n i := by
  unfold NormalizedLimit.slope
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right h (thick_δ'_nonneg NL n)

/-- The normalized mesh is eventually bounded. -/
private lemma thick_δ'_bdd {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a) :
    ∃ Δ > (0 : ℝ), ∀ᶠ n in atTop, NL.δ' n ≤ Δ := by
  rcases NL.lattice with ⟨-, ht⟩ | ⟨hδ, heq⟩
  · exact ⟨1, one_pos, ht.eventually (ge_mem_nhds one_pos)⟩
  · exact ⟨NL.δ, hδ, Eventually.of_forall fun n => (heq n).le⟩

/-- `N_n δ_n = R_n / e_n → ∞`, since `R_n → ∞` and `e_n → 0` with `e_n > 0` eventually
(because `W_n(1) → W(1) ≥ a > 0`, while `W_n ≡ 0` if `e_n = 0`). -/
private lemma thick_Nδ_tendsto {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) :
    Tendsto (fun n => (NL.Nn n : ℝ) * NL.δ' n) atTop atTop := by
  obtain ⟨hsc, hW1, -⟩ := NL.props ha haJ
  have hWt : Tendsto (fun n => S.Wn a (NL.φ n) 1) atTop (𝓝 (NL.W 1)) :=
    NL.W_conv.tendsto_at (mem_Ioi.2 one_pos)
  have hpos : ∀ᶠ n in atTop, 0 < S.Wn a (NL.φ n) 1 :=
    hWt.eventually (lt_mem_nhds (by linarith))
  have hR : Tendsto (fun n => (S.N (NL.φ n) : ℝ) * S.h (NL.φ n)) atTop atTop :=
    S.R_tendsto.comp NL.φ_mono.tendsto_atTop
  refine tendsto_atTop_mono' atTop ?_ hR
  filter_upwards [hpos, hsc.eventually (ge_mem_nhds one_pos)] with n hn hle
  have he0 : 0 ≤ S.scale a (NL.φ n) := mul_nonneg (S.h_pos _).le (Nat.cast_nonneg _)
  have he : 0 < S.scale a (NL.φ n) := by
    rcases he0.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : S.Wn a (NL.φ n) 1 = 0 := by
        simp only [SelectedSeq.Wn, SelectedSeq.Vn, ← h, zero_mul]
        rw [interp_of_nonpos (S.h_pos _) le_rfl, (S.isApproxEq _).cone.zero]
      linarith
  show (S.N (NL.φ n) : ℝ) * S.h (NL.φ n) ≤
    (S.N (NL.φ n) : ℝ) * (S.h (NL.φ n) / S.scale a (NL.φ n))
  rw [← mul_div_assoc]
  exact le_div_self (mul_nonneg (Nat.cast_nonneg _) (S.h_pos _).le) he hle

/-! ### Uniform inversion -/

/-- A uniform form of `lem:inversion`: if `v_{n,x} ≤ D v_{n,i}` and `iδ_n` is large, then
`x/i ≥ c` for every `c < 1/R_D`. Proved from the sequential `lem:inversion` by extracting a
violating subsequence and completing it to a full sequence with `i_n = x_n = N_n`. -/
private lemma thick_landing {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation)
    (htight : NL.α {p | p.1 = ⊤} = 0) (hC : NL.Cbar ≤ P.σ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ R ≥ (1 : ℝ), ∀ c < 1 / R, ∃ K1 : ℝ, ∃ n1 : ℕ, ∀ n ≥ n1, ∀ i x : ℕ, 1 ≤ i →
      i ≤ NL.Nn n → 1 ≤ x → x ≤ NL.Nn n → K1 ≤ i * NL.δ' n →
      NL.slope n x ≤ D * NL.slope n i → c ≤ (x : ℝ) / i := by
  obtain ⟨R, hR, hinv⟩ := NL.inversion ha haJ hnp htight hC (D := D) (by linarith)
  refine ⟨R, hR, fun c hc => ?_⟩
  by_contra hneg
  push Not at hneg
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, ∃ i x : ℕ, (1 ≤ i ∧ i ≤ NL.Nn n) ∧
      (1 ≤ x ∧ x ≤ NL.Nn n) ∧ (k : ℝ) ≤ i * NL.δ' n ∧ NL.slope n x ≤ D * NL.slope n i ∧
      (x : ℝ) / i < c := by
    intro k
    rw [frequently_atTop]
    intro n1
    obtain ⟨n, hn, i, x, h1, h2, h3, h4, h5, h6, h7⟩ := hneg k n1
    exact ⟨n, hn, i, x, ⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7⟩
  obtain ⟨ψ, hψ, hQ⟩ := extraction_forall_of_frequently hfreq
  choose ii xx hii hxx hk hsl hlt using hQ
  let I : ℕ → ℕ := fun n => if h : ∃ k, ψ k = n then ii (Classical.choose h) else NL.Nn n
  let X : ℕ → ℕ := fun n => if h : ∃ k, ψ k = n then xx (Classical.choose h) else NL.Nn n
  have hIψ : ∀ k, I (ψ k) = ii k := by
    intro k
    have hex : ∃ k', ψ k' = ψ k := ⟨k, rfl⟩
    simp only [I, dite_eq_left hex]
    rw [hψ.injective (Classical.choose_spec hex)]
  have hXψ : ∀ k, X (ψ k) = xx k := by
    intro k
    have hex : ∃ k', ψ k' = ψ k := ⟨k, rfl⟩
    simp only [X, dite_eq_left hex]
    rw [hψ.injective (Classical.choose_spec hex)]
  have hI : ∀ n, 1 ≤ I n ∧ I n ≤ NL.Nn n := by
    intro n
    by_cases h : ∃ k, ψ k = n
    · obtain ⟨k, rfl⟩ := h
      rw [hIψ]
      exact hii k
    · simp only [I, dite_eq_right h]
      exact ⟨thick_Nn_pos NL n, le_rfl⟩
  have hX : ∀ n, 1 ≤ X n ∧ X n ≤ NL.Nn n := by
    intro n
    by_cases h : ∃ k, ψ k = n
    · obtain ⟨k, rfl⟩ := h
      rw [hXψ]
      exact hxx k
    · simp only [X, dite_eq_right h]
      exact ⟨thick_Nn_pos NL n, le_rfl⟩
  have hItend : Tendsto (fun n => (I n : ℝ) * NL.δ' n) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [tendsto_atTop.1 (thick_Nδ_tendsto NL ha haJ) b,
      eventually_ge_atTop (ψ ⌈b⌉₊)] with n h1 h2
    by_cases h : ∃ k, ψ k = n
    · obtain ⟨k, rfl⟩ := h
      rw [hIψ]
      have hk' : ⌈b⌉₊ ≤ k := hψ.le_iff_le.1 h2
      calc b ≤ ⌈b⌉₊ := Nat.le_ceil b
        _ ≤ k := by exact_mod_cast hk'
        _ ≤ _ := hk k
    · simp only [I, dite_eq_right h]
      exact h1
  have hsl' : ∀ n, NL.slope n (X n) ≤ D * NL.slope n (I n) := by
    intro n
    by_cases h : ∃ k, ψ k = n
    · obtain ⟨k, rfl⟩ := h
      rw [hIψ, hXψ]
      exact hsl k
    · simp only [I, X, dite_eq_right h]
      have := thick_slope_nonneg NL n (thick_Nn_pos NL n) le_rfl
      nlinarith
  have hev := hinv I X hI hX hItend hsl' c hc
  obtain ⟨k, hk'⟩ := (hψ.tendsto_atTop.eventually hev).exists
  simp only [hXψ, hIψ] at hk'
  exact absurd (hlt k) (not_lt.2 hk')

/-! ### Tightness -/

/-- Tightness (`htight`) and Portmanteau: there is `K_E ≥ 0` such that eventually the sellers
with `l δ_n < K_E` carry `η̃_n`-mass `> 3/4`. -/
private lemma thick_tight {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (htight : NL.α {p | p.1 = ⊤} = 0) :
    ∃ KE : ℝ, 0 ≤ KE ∧ ∀ᶠ n in atTop, (3 / 4 : ℝ) <
      NL.lawMass n ((Finset.range (NL.Nn n + 1)).filter fun l => (l : ℝ) * NL.δ' n < KE) := by
  have hαp := NL.α_prob
  have hmeas : ∀ m, Measurable (S.ι a m) := fun m => by
    show Measurable fun s => (ENNReal.ofReal (s / S.scale a m), S.Vn m s)
    exact (ENNReal.measurable_ofReal.comp (measurable_id.div_const _)).prodMk
      (interp_monotone (S.h_pos m) (S.isApproxEq m).cone.incr).measurable
  have hαn : ∀ n, IsProbabilityMeasure (S.αn a (NL.φ n)) := fun n => by
    have : IsProbabilityMeasure (S.ηn (NL.φ n)) := gridMeasure_isProb (S.isApproxEq (NL.φ n)).law
    exact (Measure.isProbabilityMeasure_map_iff (hmeas _).aemeasurable).2 this
  let U : ℕ → Set (ℝ≥0∞ × ℝ) := fun k => {p | p.1 < k}
  have hUo : ∀ k, IsOpen (U k) := fun k => isOpen_lt continuous_fst continuous_const
  have hUm : Monotone U := fun k k' hk p (hp : p.1 < k) =>
    show p.1 < k' from lt_of_lt_of_le hp (by exact_mod_cast hk)
  have hUnion : ⋃ k, U k = {p : ℝ≥0∞ × ℝ | p.1 = ⊤}ᶜ := by
    ext p
    simp only [mem_iUnion, mem_compl_iff, mem_ofPred_eq, U]
    constructor
    · rintro ⟨k, hk⟩ h
      rw [h] at hk
      exact not_top_lt hk
    · intro h
      exact ENNReal.exists_nat_gt h
  have hfull : NL.α (⋃ k, U k) = 1 := by
    rw [hUnion, prob_compl_eq_one_iff (show MeasurableSet {p : ℝ≥0∞ × ℝ | p.1 = ⊤} from
      (measurableSet_singleton (⊤ : ℝ≥0∞)).preimage measurable_fst)]
    exact htight
  have hlim := tendsto_measure_iUnion_atTop (μ := NL.α) hUm
  rw [hfull] at hlim
  have h34 : ENNReal.ofReal (3 / 4) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
  obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds h34)).exists
  simp only [Function.comp_apply] at hk
  have ht := (weakConv_iff_tendsto hαn hαp).1 NL.α_conv
  have hl := ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht (hUo k)
  simp only [toPM_toMeasure] at hl
  have hev := eventually_lt_of_lt_liminf (hk.trans_le hl)
  refine ⟨k, Nat.cast_nonneg k, ?_⟩
  filter_upwards [hev] with n hn
  have hcalc : S.αn a (NL.φ n) (U k) = ENNReal.ofReal (NL.lawMass n
      ((Finset.range (NL.Nn n + 1)).filter fun l => (l : ℝ) * NL.δ' n < k)) := by
    rw [SelectedSeq.αn, Measure.map_apply (hmeas _) (hUo k).measurableSet, SelectedSeq.ηn,
      gridMeasure_apply' (S.isApproxEq _).law.nonneg ((hmeas _) (hUo k).measurableSet)]
    congr 1
    rw [NormalizedLimit.lawMass, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hiff : (l : ℝ) * S.h (NL.φ n) ∈ S.ι a (NL.φ n) ⁻¹' U k ↔
        (l : ℝ) * NL.δ' n < k := by
      have hnn : 0 ≤ (l : ℝ) * NL.δ' n := mul_nonneg (Nat.cast_nonneg l) (thick_δ'_nonneg NL n)
      have he : (l : ℝ) * S.h (NL.φ n) / S.scale a (NL.φ n) = (l : ℝ) * NL.δ' n :=
        mul_div_assoc _ _ _
      simp only [mem_preimage, SelectedSeq.ι, U, mem_ofPred_eq]
      rw [he, ← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff']
      exact ⟨fun h => h.1, fun h => ⟨h, lt_of_le_of_lt hnn h⟩⟩
    by_cases h : (l : ℝ) * NL.δ' n < k
    · rw [ite_eq_left h, ite_eq_left (hiff.2 h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.1 h'))]
  rw [hcalc, ENNReal.ofReal_lt_ofReal_iff'] at hn
  exact hn.1

/-! ### Markov's inequality on `eq:adjnorm` -/

/-- Markov: if `v = β ∑_l η_l p_l` with `η, p ≥ 0`, the `η`-mass of `{p > (4/β) v}` is `≤ 1/4`. -/
private lemma thick_markov {s : Finset ℕ} {η p : ℕ → ℝ} {v β : ℝ} (hβ : 0 < β) (hv : 0 ≤ v)
    (hη : ∀ l, 0 ≤ η l) (hp : ∀ l ∈ s, 0 ≤ p l) (hsum : v = β * ∑ l ∈ s, η l * p l) :
    ∑ l ∈ s.filter (fun l => 4 / β * v < p l), η l ≤ 1 / 4 := by
  set E := s.filter (fun l => 4 / β * v < p l) with hE
  have h1 : ∑ l ∈ E, η l * (4 / β * v) ≤ ∑ l ∈ E, η l * p l :=
    Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hl).2.le (hη l)
  have h2 : ∑ l ∈ E, η l * p l ≤ ∑ l ∈ s, η l * p l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun l hl _ => mul_nonneg (hη l) (hp l hl)
  rw [← Finset.sum_mul] at h1
  rcases hv.lt_or_eq with hvpos | hvz
  · have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) hβ.le
    have e1 : (∑ l ∈ E, η l) * (4 / β * v) * β = 4 * (∑ l ∈ E, η l) * v := by
      field_simp
    rw [e1, mul_comm _ β, ← hsum] at h3
    nlinarith
  · have hz : ∑ l ∈ s, η l * p l = 0 := by
      have : β * ∑ l ∈ s, η l * p l = 0 := by rw [← hsum, ← hvz]
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hβ.ne'
      · exact h
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun l hl => mul_nonneg (hη l) (hp l hl))] at hz
    have : ∑ l ∈ E, η l = 0 := Finset.sum_eq_zero fun l hl => by
      obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
      rw [← hvz, mul_zero] at hl2
      rcases mul_eq_zero.1 (hz l hl1) with h | h
      · exact h
      · linarith
    rw [this]
    norm_num

/-! ### Landing shares -/

/-- If both landing indices `B, S` (with `B + S = x + y`) satisfy `x ≤ 2R (X + 1)` and
`x ≥ 4R + y`, then the buyer's share `B/(x+y)` lies in `[1/(4R), 1 - 1/(4R)]`. -/
private lemma thick_share {R x y B S : ℝ} (hR : 1 ≤ R) (hsum : B + S = x + y) (hy : 0 ≤ y)
    (hxy : 4 * R + y ≤ x) (hB : x ≤ 2 * R * (B + 1)) (hS : x ≤ 2 * R * (S + 1)) :
    B / (x + y) ∈ Icc (1 / (4 * R)) (1 - 1 / (4 * R)) := by
  have hR0 : 0 < R := by linarith
  have hpos : 0 < x + y := by linarith
  have hB' : x + y ≤ 4 * R * B := by linarith
  have hS' : x + y ≤ 4 * R * S := by linarith
  have h4R : 0 < 4 * R := by linarith
  have hB'' : (x + y) / (4 * R) ≤ B := by rw [div_le_iff₀ h4R]; linarith
  have hS'' : (x + y) / (4 * R) ≤ S := by rw [div_le_iff₀ h4R]; linarith
  constructor
  · rw [le_div_iff₀ hpos]
    calc 1 / (4 * R) * (x + y) = (x + y) / (4 * R) := by ring
      _ ≤ B := hB''
  · rw [div_le_iff₀ hpos]
    calc B = x + y - S := by linarith
      _ ≤ x + y - (x + y) / (4 * R) := by linarith
      _ = (1 - 1 / (4 * R)) * (x + y) := by ring

/-- `thm:splitting` (uniform wealth splitting at large buyer wealth), eq. `eq:splitting`. -/
theorem NormalizedLimit.splitting {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) (hnp : ¬ NL.HasFiniteSaturation)
    (htight : NL.α {p | p.1 = ⊤} = 0) (hC : NL.Cbar ≤ P.σ) :
    ∃ ω ∈ Ioc (0 : ℝ) (1 / 2), ∃ c > (0 : ℝ), ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ici 0 ∧
      ∀ ς > (0 : ℝ), ∃ K' : ℝ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ i : ℕ, 1 ≤ i → i ≤ NL.Nn n →
        K' ≤ i * NL.δ' n → c - ς ≤ NL.lawMass n (NL.splitSet ω K n i) := by
  obtain ⟨KE, hKE0, hKE⟩ := thick_tight NL htight
  have hβ := P.β_pos
  have hcm := P.cmin_pos
  set D : ℝ := 4 / P.β / P.cmin with hD
  have h4β : 1 ≤ 4 / P.β := by rw [le_div_iff₀ hβ]; linarith [P.β_lt_one]
  have hDge : 4 / P.β ≤ D := le_div_self (by positivity) hcm P.cmin_le_one
  obtain ⟨R, hR1, hland⟩ := thick_landing NL ha haJ hnp htight hC (D := D) (by linarith)
  obtain ⟨Δ, hΔ0, hΔ⟩ := thick_δ'_bdd NL
  have hR0 : 0 < R := by linarith
  refine ⟨1 / (4 * R), ⟨by positivity, ?_⟩, 1 / 2, by norm_num, Icc 0 KE, isCompact_Icc,
    Icc_subset_Ici_self, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  intro ς hς
  obtain ⟨K1, n1, hK1⟩ := hland (1 / (2 * R))
    (by rw [div_lt_div_iff₀ (by positivity) hR0]; linarith)
  obtain ⟨n2, hn2⟩ := eventually_atTop.1 (hKE.and hΔ)
  refine ⟨max K1 (4 * R * Δ + KE), max n1 n2, ?_⟩
  intro n hn i hi1 hi hK'
  have hn1 : n1 ≤ n := le_of_max_le_left hn
  obtain ⟨hmass, hδΔ⟩ := hn2 n (le_of_max_le_right hn)
  have hK1' : K1 ≤ i * NL.δ' n := (le_max_left _ _).trans hK'
  have hK2 : 4 * R * Δ + KE ≤ i * NL.δ' n := (le_max_right _ _).trans hK'
  have hδ0 := thick_δ'_nonneg NL n
  have hδpos : 0 < NL.δ' n := by
    rcases hδ0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hK2
      nlinarith
  have hE := S.isApproxEq (NL.φ n)
  have hi' : i ≤ S.N (NL.φ n) := hi
  have hv0 : 0 ≤ S.V (NL.φ n) i - S.V (NL.φ n) (i - 1) := by
    have := hE.cone.incr.mono (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at this
    linarith
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
  -- the good sellers: `l δ_n < K_E` and `ρ_{l,i} ≤ 4/β`
  set G := (Finset.range (NL.Nn n + 1)).filter fun l : ℕ => (l : ℝ) * NL.δ' n < KE ∧
      Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l ≤
        4 / P.β * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) with hG
  -- Markov
  have hp0 : ∀ l ∈ Finset.range (NL.Nn n + 1), 0 ≤
      Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l := by
    intro l hl
    have hl' : l ≤ S.N (NL.φ n) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have : Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l ≤
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l :=
      Grid.gH_mono' P.U hE.cone.incr (show i - 1 ≤ i by omega) hi' hl'
    linarith
  have hM : ∑ l ∈ (Finset.range (NL.Nn n + 1)).filter (fun l =>
      4 / P.β * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) <
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
          Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l), S.η (NL.φ n) l ≤ 1 / 4 :=
    thick_markov (p := fun l => Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l) hβ hv0 hE.law.nonneg hp0
      (adjnorm hE hi1 hi')
  have hGmass : 1 / 2 ≤ NL.lawMass n G := by
    set Kset := (Finset.range (NL.Nn n + 1)).filter fun l : ℕ => (l : ℝ) * NL.δ' n < KE
    set E := (Finset.range (NL.Nn n + 1)).filter (fun l : ℕ =>
      4 / P.β * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) <
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
          Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l)
    have hsub : Kset ⊆ G ∪ E := by
      intro l hl
      obtain ⟨hlr, hlK⟩ := Finset.mem_filter.1 hl
      rw [Finset.mem_union]
      by_cases hc : Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
          Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l ≤
          4 / P.β * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1))
      · exact Or.inl (Finset.mem_filter.2 ⟨hlr, hlK, hc⟩)
      · exact Or.inr (Finset.mem_filter.2 ⟨hlr, lt_of_not_ge hc⟩)
    have hη0 := hE.law.nonneg
    have h1 : NL.lawMass n Kset ≤ ∑ l ∈ G ∪ E, S.η (NL.φ n) l :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun l _ _ => hη0 l
    have h2 := Finset.sum_union_inter (s₁ := G) (s₂ := E) (f := S.η (NL.φ n))
    have h3 : 0 ≤ ∑ l ∈ G ∩ E, S.η (NL.φ n) l := Finset.sum_nonneg fun l _ => hη0 l
    unfold NormalizedLimit.lawMass at h1 hmass ⊢
    linarith
  -- every good seller is thick
  have hGsub : G ⊆ NL.splitSet (1 / (4 * R)) (Icc 0 KE) n i := by
    intro l hl
    obtain ⟨hlr, hlK, hlp⟩ := Finset.mem_filter.1 hl
    have hlN : l ≤ S.N (NL.φ n) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hlr)
    suffices key : ∀ j ∈ NL.argmaxSet n i l,
        ((i - j : ℕ) : ℝ) / ((i : ℝ) + l) ∈ Icc (1 / (4 * R)) (1 - 1 / (4 * R)) by
      simp only [NormalizedLimit.splitSet, Finset.mem_filter]
      exact ⟨hlr, ⟨mul_nonneg (Nat.cast_nonneg l) hδ0, hlK.le⟩, key⟩
    intro j hj
    obtain ⟨hjf, hjmax⟩ := Finset.mem_filter.1 hj
    obtain ⟨-, -, m3, m4⟩ := neighbour P.U hE.cone hi1 hi' hlN hjf hjmax
    have m3' : i - j < NL.Nn n → S.V (NL.φ n) (i - j + 1) - S.V (NL.φ n) (i - j) ≤
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
          Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l := m3
    have m4' : l + j < NL.Nn n →
        P.U.marg P.Cstar * (S.V (NL.φ n) (l + j + 1) - S.V (NL.φ n) (l + j)) ≤
        Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l -
          Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) (i - 1) l := m4
    have hjf' := (Grid.mem_feas hi' hlN).1 hjf
    -- buyer landing index `B = i - j`
    have hB : (i : ℝ) ≤ 2 * R * (((i - j : ℕ) : ℝ) + 1) := by
      by_cases hBN : i - j < NL.Nn n
      · have hsl : NL.slope n (i - j + 1) ≤ D * NL.slope n i := by
          apply thick_slope_le NL
          rw [Nat.add_sub_cancel]
          have := m3' hBN
          nlinarith [mul_le_mul_of_nonneg_right hDge hv0]
        have := hK1 n hn1 i (i - j + 1) hi1 hi (by omega) (by omega) hK1' hsl
        rw [div_le_div_iff₀ (by positivity) hi0] at this
        push_cast at this
        linarith
      · have hle : i ≤ i - j := by omega
        have hle' : (i : ℝ) ≤ ((i - j : ℕ) : ℝ) := by exact_mod_cast hle
        nlinarith [mul_nonneg (sub_nonneg.2 hR1) (Nat.cast_nonneg (α := ℝ) (i - j))]
    -- seller landing index `S = l + j`
    have hS : (i : ℝ) ≤ 2 * R * (((l + j : ℕ) : ℝ) + 1) := by
      by_cases hSN : l + j < NL.Nn n
      · have hΔS : 0 ≤ S.V (NL.φ n) (l + j + 1) - S.V (NL.φ n) (l + j) := by
          linarith [hE.cone.incr.mono (l + j) hSN]
        have hmarg : P.cmin ≤ P.U.marg P.Cstar := min_le_right _ _
        have h4 := m4' hSN
        have hsl : NL.slope n (l + j + 1) ≤ D * NL.slope n i := by
          apply thick_slope_le NL
          rw [Nat.add_sub_cancel]
          have h5 : P.cmin * (S.V (NL.φ n) (l + j + 1) - S.V (NL.φ n) (l + j)) ≤
              4 / P.β * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) := by
            nlinarith [mul_le_mul_of_nonneg_right hmarg hΔS]
          have h6 : D * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) =
              4 / P.β * (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) / P.cmin := by
            rw [hD]; field_simp
          rw [h6, le_div_iff₀ hcm]
          linarith
        have := hK1 n hn1 i (l + j + 1) hi1 hi (by omega) (by omega) hK1' hsl
        rw [div_le_div_iff₀ (by positivity) hi0] at this
        push_cast at this ⊢
        linarith
      · have hle : i ≤ l + j := by omega
        have hle' : (i : ℝ) ≤ ((l + j : ℕ) : ℝ) := by exact_mod_cast hle
        nlinarith [mul_nonneg (sub_nonneg.2 hR1) (Nat.cast_nonneg (α := ℝ) (l + j))]
    -- `i ≥ 4R + l`
    have hxy : 4 * R + l ≤ (i : ℝ) := by
      have h1 : (4 * R + l) * NL.δ' n ≤ i * NL.δ' n := by
        have e : (4 * R + l) * NL.δ' n = 4 * R * NL.δ' n + l * NL.δ' n := by ring
        rw [e]
        linarith [mul_le_mul_of_nonneg_left hδΔ (show 0 ≤ 4 * R by linarith)]
      exact le_of_mul_le_mul_right h1 hδpos
    have hsum : ((i - j : ℕ) : ℝ) + ((l + j : ℕ) : ℝ) = (i : ℝ) + l := by
      rw [Nat.cast_sub hjf'.1]; push_cast; ring
    exact thick_share hR1 hsum (Nat.cast_nonneg l) hxy hB hS
  calc 1 / 2 - ς ≤ 1 / 2 := by linarith
    _ ≤ NL.lawMass n G := hGmass
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hGsub fun l _ _ => hE.law.nonneg l

end Molico
