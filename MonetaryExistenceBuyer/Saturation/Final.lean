import MonetaryExistenceBuyer.Saturation.Splitting
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Every normalized limit exhibits finite-wealth saturation (`thm:noplateau`)

The proof is the size-biased entropy budget of the manuscript. In index form, for the
approximant along the subsequence, `lem:entropy` reads
`∑_{m,l,j} η_m η_l κ_{mlj} (m + l) G(m,l,j) = 0` with `G = χ(r̂) - χ(r)`,
`r = m/(m+l)`, `r̂ = (m-j)/(m+l)`. Writing `χ = -binEntropy`, we bound
`(m + l) G ≤ (m + l) H(r) + [thick] m χ(ω)` with `H = binEntropy`, split the size-biased weight
`m + l` into a buyer and a seller part (equal by the symmetry `H(r) = H(1 - r)`), and control
`H(r)` by `binEntropy t₀` away from the low-wealth buyers (mass `≤ T e_n / M`) and the
high-wealth sellers (mass `≤ ε` by tightness). Here the threshold `T` can be kept fixed.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### Facts about `χ = -binEntropy` -/

private lemma χ_eq_neg_binEntropy (x : ℝ) : χ x = -Real.binEntropy x := by
  unfold χ Real.binEntropy
  rw [Real.log_inv, Real.log_inv]; ring

private lemma binEntropy_le_of_le_half {x t : ℝ} (hx0 : 0 ≤ x) (hxt : x ≤ t) (ht : t ≤ 1 / 2) :
    Real.binEntropy x ≤ Real.binEntropy t :=
  Real.binEntropy_strictMonoOn.monotoneOn ⟨hx0, by norm_num; linarith⟩
    ⟨hx0.trans hxt, by norm_num; linarith⟩ hxt

private lemma binEntropy_le_of_near_one {x t : ℝ} (hx1 : x ≤ 1) (hxt : 1 - x ≤ t)
    (ht : t ≤ 1 / 2) : Real.binEntropy x ≤ Real.binEntropy t := by
  rw [← Real.binEntropy_one_sub x]
  exact binEntropy_le_of_le_half (by linarith) hxt ht

private lemma binEntropy_ge_mid {ω x : ℝ} (hω0 : 0 ≤ ω) (hx : x ∈ Icc ω (1 - ω)) :
    Real.binEntropy ω ≤ Real.binEntropy x := by
  rcases le_total x (1 / 2) with h | h
  · exact binEntropy_le_of_le_half hω0 hx.1 h
  · rw [← Real.binEntropy_one_sub x]
    exact binEntropy_le_of_le_half hω0 (by linarith [hx.2]) (by linarith)

/-- `χ(ω) < 0` for `ω ∈ (0, 1/2]`. -/
private lemma χ_neg {ω : ℝ} (hω : ω ∈ Ioc (0 : ℝ) (1 / 2)) : χ ω < 0 := by
  rw [χ_eq_neg_binEntropy]
  linarith [Real.binEntropy_pos hω.1 (by linarith [hω.2])]

/-- `binEntropy` is small near `0`. -/
private lemma exists_binEntropy_small {B : ℝ} (hB : 0 < B) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ 1 / 2 ∧ Real.binEntropy t₀ ≤ B := by
  have hc : Tendsto Real.binEntropy (𝓝 0) (𝓝 0) := by
    simpa using Real.binEntropy_continuous.tendsto 0
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually (gt_mem_nhds hB))
  refine ⟨min (ρ / 2) (1 / 2), by positivity, min_le_right _ _, (hball ?_).le⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  exact (min_le_left _ _).trans_lt (by linarith)

/-! ### The share functions in index form -/

/-- `H(m, l) = binEntropy(m/(m+l)) = -χ(r)`. -/
private def shareH (m l : ℕ) : ℝ := Real.binEntropy ((m : ℝ) / ((m : ℝ) + l))

/-- `G(m, l, j) = χ(r̂) - χ(r)`. -/
private def shareG (m l j : ℕ) : ℝ :=
  χ (((m - j : ℕ) : ℝ) / ((m : ℝ) + l)) - χ ((m : ℝ) / ((m : ℝ) + l))

private lemma entropyIntegrand_eq_mul {h : ℝ} (hh : 0 < h) (m l j : ℕ) :
    entropyIntegrand h m l j = h * (((m : ℝ) + l) * shareG m l j) := by
  unfold entropyIntegrand shareG
  simp only
  have e : (m : ℝ) * h + (l : ℝ) * h = ((m : ℝ) + l) * h := by ring
  rw [e, mul_div_mul_right _ _ hh.ne', mul_div_mul_right _ _ hh.ne']
  ring

private lemma shareG_le (m l j : ℕ) : shareG m l j ≤ shareH m l := by
  unfold shareG shareH
  have h0 : 0 ≤ ((m - j : ℕ) : ℝ) / ((m : ℝ) + l) := by positivity
  have h1 : ((m - j : ℕ) : ℝ) / ((m : ℝ) + l) ≤ 1 := by
    apply div_le_one_of_le₀ _ (by positivity)
    have : ((m - j : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m j
    linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  rw [χ_eq_neg_binEntropy, χ_eq_neg_binEntropy]
  linarith [Real.binEntropy_nonneg h0 h1]

private lemma shareG_le_thick {m l j : ℕ} {ω : ℝ} (hω0 : 0 ≤ ω)
    (hr : ((m - j : ℕ) : ℝ) / ((m : ℝ) + l) ∈ Icc ω (1 - ω)) :
    shareG m l j ≤ χ ω + shareH m l := by
  unfold shareG shareH
  rw [χ_eq_neg_binEntropy, χ_eq_neg_binEntropy, χ_eq_neg_binEntropy]
  linarith [binEntropy_ge_mid hω0 hr]

private lemma shareH_symm (m l : ℕ) : shareH m l = shareH l m := by
  unfold shareH
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  by_cases h : (m : ℝ) + l = 0
  · have hm : (m : ℝ) = 0 := by linarith
    have hl : (l : ℝ) = 0 := by linarith
    simp [hm, hl]
  · have h' : (l : ℝ) + m ≠ 0 := by rwa [add_comm]
    rw [← Real.binEntropy_one_sub ((m : ℝ) / ((m : ℝ) + l))]
    congr 1
    field_simp
    ring

/-- Away from low buyers and high sellers, the buyer share is close to `1`. -/
private lemma shareH_le {m l : ℕ} {δ T K₂ t₀ : ℝ} (hT : 0 < T) (hK₂ : 0 < K₂)
    (hKt : K₂ / T ≤ t₀) (ht₀ : t₀ ≤ 1 / 2) :
    shareH m l ≤ Real.binEntropy t₀ +
      Real.log 2 * ((if (m : ℝ) * δ ≤ T then 1 else 0) + (if K₂ ≤ (l : ℝ) * δ then 1 else 0)) := by
  unfold shareH
  have hb0 : 0 ≤ Real.binEntropy t₀ :=
    Real.binEntropy_nonneg ((div_pos hK₂ hT).le.trans hKt) (by linarith)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH := Real.binEntropy_le_log_two (p := (m : ℝ) / ((m : ℝ) + l))
  have hi1 : 0 ≤ (if (m : ℝ) * δ ≤ T then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hi2 : 0 ≤ (if K₂ ≤ (l : ℝ) * δ then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  by_cases h1 : (m : ℝ) * δ ≤ T
  · rw [ite_eq_left h1]
    nlinarith
  · by_cases h2 : K₂ ≤ (l : ℝ) * δ
    · rw [ite_eq_left h2]
      nlinarith
    · rw [ite_eq_right h1, ite_eq_right h2]
      rw [not_le] at h1 h2
      have hm : (0 : ℝ) < m * δ := hT.trans h1
      have hmpos : (0 : ℝ) < m := by
        by_contra hc
        have : (m : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg m)
        rw [this, zero_mul] at hm
        exact lt_irrefl 0 hm
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have hml : (0 : ℝ) < (m : ℝ) + l := by positivity
      have hr1 : (m : ℝ) / ((m : ℝ) + l) ≤ 1 := div_le_one_of_le₀ (by linarith) hml.le
      have hr2 : 1 - (m : ℝ) / ((m : ℝ) + l) ≤ t₀ := by
        refine le_trans ?_ hKt
        rw [one_sub_div hml.ne', add_sub_cancel_left, div_le_div_iff₀ hml hT]
        nlinarith [mul_le_mul_of_nonneg_left h1.le hl0, mul_le_mul_of_nonneg_left h2.le hmpos.le]
      simp only [add_zero, mul_zero]
      exact binEntropy_le_of_near_one hr1 hr2 ht₀

/-! ### The abstract entropy budget for one approximant -/

private lemma core_bound {N : ℕ} {η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ} {h M δ e : ℝ}
    (hh : 0 < h) (hM : 0 < M) (hδ : 0 < δ) (hδe : δ * e = h)
    (hη : Grid.IsLaw h M N η) (hκ : Grid.IsKernel N κ)
    {ω c ε T K₂ t₀ : ℝ} (hω0 : 0 ≤ ω) (hc : 0 ≤ c) (hT : 0 < T)
    (hK₂ : 0 < K₂) (hKt : K₂ / T ≤ t₀) (ht₀ : t₀ ≤ 1 / 2) (hχω : χ ω ≤ 0)
    (E : ℕ → Finset ℕ) (hEsub : ∀ m, E m ⊆ Finset.range (N + 1))
    (hEthick : ∀ m ≤ N, ∀ l ∈ E m, ∀ j ∈ Grid.feas N m l, κ m l j ≠ 0 →
      ((m - j : ℕ) : ℝ) / ((m : ℝ) + l) ∈ Icc ω (1 - ω))
    (hEmass : ∀ m ≤ N, T < m * δ → c ≤ ∑ l ∈ E m, η l)
    (htight : ∑ l ∈ Finset.range (N + 1), η l * (if K₂ ≤ (l : ℝ) * δ then 1 else 0) ≤ ε)
    (hent : ∑ m ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1), ∑ j ∈ Grid.feas N m l,
      η m * η l * κ m l j * entropyIntegrand h m l j = 0) :
    0 ≤ 2 * Real.binEntropy t₀ + 2 * Real.log 2 * (T * e / M + ε) +
      c * χ ω * (1 - T * e / M) := by
  set R := Finset.range (N + 1) with hR
  have hη0 := hη.nonneg
  have hκ0 := hκ.nonneg
  set b := Real.binEntropy t₀ with hb
  set L := Real.log 2 with hL
  have hlog : 0 ≤ L := Real.log_nonneg (by norm_num)
  set q := M / h with hq
  set p := T / δ with hp
  -- the sum of the weights and the mean
  have hsum1 : ∑ l ∈ R, η l = 1 := hη.sum_one
  have hmean : ∑ l ∈ R, η l * l = q := by
    rw [hq, eq_div_iff hh.ne', Finset.sum_mul]
    rw [← hη.mean]
    exact Finset.sum_congr rfl fun l _ => by ring
  -- Step 1: the entropy identity without the mesh
  have hZ : ∑ m ∈ R, ∑ l ∈ R, ∑ j ∈ Grid.feas N m l,
      η m * η l * κ m l j * (((m : ℝ) + l) * shareG m l j) = 0 := by
    have : h * ∑ m ∈ R, ∑ l ∈ R, ∑ j ∈ Grid.feas N m l,
        η m * η l * κ m l j * (((m : ℝ) + l) * shareG m l j) = 0 := by
      rw [← hent, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [entropyIntegrand_eq_mul hh]; ring
    exact (mul_eq_zero.1 this).resolve_left hh.ne'
  -- Step 2: pointwise bound, summed over the transfers
  have hstep : ∀ m ∈ R, ∀ l ∈ R, ∑ j ∈ Grid.feas N m l,
      η m * η l * κ m l j * (((m : ℝ) + l) * shareG m l j) ≤
      η m * η l * (((m : ℝ) + l) * shareH m l +
        (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0)) := by
    intro m hm l hl
    have hm' : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    calc _ ≤ ∑ j ∈ Grid.feas N m l, (η m * η l * (((m : ℝ) + l) * shareH m l +
            (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0))) * κ m l j := by
          refine Finset.sum_le_sum fun j hj => ?_
          by_cases hκj : κ m l j = 0
          · simp [hκj]
          have hw : 0 ≤ η m * η l * κ m l j := mul_nonneg (mul_nonneg (hη0 m) (hη0 l)) (hκ0 m l j)
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
          have hG1 := shareG_le m l j
          have key : ((m : ℝ) + l) * shareG m l j ≤ ((m : ℝ) + l) * shareH m l +
              (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0) := by
            split_ifs with hD
            · have hG2 := shareG_le_thick hω0 (hEthick m hm' l hD.2 j hj hκj)
              nlinarith [mul_le_mul_of_nonneg_left hG2 hm0, mul_le_mul_of_nonneg_left hG1 hl0]
            · nlinarith [mul_le_mul_of_nonneg_left hG1 (add_nonneg hm0 hl0)]
          calc η m * η l * κ m l j * (((m : ℝ) + l) * shareG m l j)
              ≤ η m * η l * κ m l j * (((m : ℝ) + l) * shareH m l +
                (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0)) :=
                mul_le_mul_of_nonneg_left key hw
            _ = _ := by ring
      _ = _ := sum_feas_mul_kernel hκ hm hl _
  -- the two sums
  set S1 := ∑ m ∈ R, ∑ l ∈ R, η m * η l * ((m : ℝ) * shareH m l) with hS1
  set S2 := ∑ m ∈ R, ∑ l ∈ R, η m * η l * (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0)
    with hS2
  have hsplit : 0 ≤ 2 * S1 + S2 := by
    have h1 : 0 ≤ ∑ m ∈ R, ∑ l ∈ R, η m * η l * (((m : ℝ) + l) * shareH m l +
        (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0)) := by
      exact hZ.symm.le.trans
        (Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun l hl => hstep m hm l hl)
    have h2 : ∑ m ∈ R, ∑ l ∈ R, η m * η l * (((m : ℝ) + l) * shareH m l +
        (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0)) =
        S1 + ∑ m ∈ R, ∑ l ∈ R, η m * η l * ((l : ℝ) * shareH m l) + S2 := by
      rw [hS1, hS2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have h3 : ∑ m ∈ R, ∑ l ∈ R, η m * η l * ((l : ℝ) * shareH m l) = S1 := by
      rw [hS1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
      rw [shareH_symm l m]; ring
    rw [h2, h3] at h1
    linarith
  -- low buyers: `∑_{mδ ≤ T} η_m m ≤ T/δ`
  have hlow : ∑ m ∈ R, η m * m * (if (m : ℝ) * δ ≤ T then 1 else 0) ≤ p := by
    calc _ ≤ ∑ m ∈ R, p * η m := by
          refine Finset.sum_le_sum fun m _ => ?_
          split_ifs with h1
          · rw [mul_one, mul_comm p]
            exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hδ).2 h1) (hη0 m)
          · rw [mul_zero]; exact mul_nonneg (div_pos hT hδ).le (hη0 m)
      _ = p := by rw [← Finset.mul_sum, hsum1, mul_one]
  -- Step 3: the buyer-biased bound
  have hS1b : S1 ≤ b * q + L * (p + q * ε) := by
    set τ := ∑ l ∈ R, η l * (if K₂ ≤ (l : ℝ) * δ then 1 else 0) with hτ
    calc S1 ≤ ∑ m ∈ R, ∑ l ∈ R, ((η m * m * b) * η l +
          (L * (η m * m * (if (m : ℝ) * δ ≤ T then 1 else 0))) * η l +
          (L * (η m * m)) * (η l * (if K₂ ≤ (l : ℝ) * δ then 1 else 0))) := by
          refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun l _ => ?_
          have hH := shareH_le (m := m) (l := l) (δ := δ) hT hK₂ hKt ht₀
          have hw : 0 ≤ η m * η l * m := mul_nonneg (mul_nonneg (hη0 m) (hη0 l)) (Nat.cast_nonneg m)
          calc η m * η l * ((m : ℝ) * shareH m l) = (η m * η l * m) * shareH m l := by ring
            _ ≤ (η m * η l * m) * (b + L * ((if (m : ℝ) * δ ≤ T then 1 else 0) +
                (if K₂ ≤ (l : ℝ) * δ then 1 else 0))) := mul_le_mul_of_nonneg_left hH hw
            _ = _ := by ring
      _ = ∑ m ∈ R, (η m * m * b + L * (η m * m * (if (m : ℝ) * δ ≤ T then 1 else 0)) +
          L * (η m * m) * τ) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum, hsum1]
          ring
      _ = b * ∑ m ∈ R, η m * m + L * ∑ m ∈ R, η m * m * (if (m : ℝ) * δ ≤ T then 1 else 0) +
          L * τ * ∑ m ∈ R, η m * m := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
            Finset.mul_sum]
          congr 1; congr 1
          · exact Finset.sum_congr rfl fun m _ => by ring
          · exact Finset.sum_congr rfl fun m _ => by ring
      _ ≤ b * q + L * p + L * ε * q := by
          rw [hmean]
          have hq0 : 0 ≤ q := div_nonneg hM.le hh.le
          have := mul_le_mul_of_nonneg_left hlow hlog
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htight hlog) hq0
          linarith
      _ = _ := by ring
  -- Step 4: the thick bound
  have hS2b : S2 ≤ χ ω * c * (q - p) := by
    have hpm : ∀ m ∈ R, ∑ l ∈ R, η m * η l *
        (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0) ≤
        χ ω * c * (η m * m * (1 - (if (m : ℝ) * δ ≤ T then 1 else 0))) := by
      intro m hm
      have hm' : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      by_cases hTm : T < m * δ
      · have hE : ∑ l ∈ R, η m * η l * (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0) =
            (η m * m * χ ω) * ∑ l ∈ E m, η l := by
          have : ∀ l ∈ R, η m * η l * (if T < m * δ ∧ l ∈ E m then (m : ℝ) * χ ω else 0) =
              if l ∈ E m then (η m * m * χ ω) * η l else 0 := by
            intro l _
            by_cases hl : l ∈ E m
            · rw [ite_eq_left ⟨hTm, hl⟩, ite_eq_left hl]; ring
            · rw [ite_eq_right (fun h => hl h.2), ite_eq_right hl, mul_zero]
          rw [Finset.sum_congr rfl this, Finset.sum_ite_mem, Finset.inter_eq_right.2 (hEsub m),
            ← Finset.mul_sum]
        rw [hE, ite_eq_right (not_le.2 hTm), sub_zero, mul_one]
        have hcoef : η m * m * χ ω ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hη0 m) (Nat.cast_nonneg m)) hχω
        have := mul_le_mul_of_nonpos_left (hEmass m hm' hTm) hcoef
        linarith
      · have hle : (m : ℝ) * δ ≤ T := not_lt.1 hTm
        rw [ite_eq_left hle, sub_self, mul_zero, mul_zero]
        refine le_of_eq (Finset.sum_eq_zero fun l _ => ?_)
        rw [ite_eq_right (fun h => hTm h.1), mul_zero]
    calc S2 ≤ ∑ m ∈ R, χ ω * c * (η m * m * (1 - (if (m : ℝ) * δ ≤ T then 1 else 0))) :=
          Finset.sum_le_sum hpm
      _ = χ ω * c * (q - ∑ m ∈ R, η m * m * (if (m : ℝ) * δ ≤ T then 1 else 0)) := by
          rw [← Finset.mul_sum, ← hmean, ← Finset.sum_sub_distrib]
          congr 1
          exact Finset.sum_congr rfl fun m _ => by ring
      _ ≤ χ ω * c * (q - p) :=
          mul_le_mul_of_nonpos_left (by linarith) (mul_nonpos_of_nonpos_of_nonneg hχω hc)
  -- Step 5: rescale by `h / M`
  have hX : 0 ≤ 2 * (b * q + L * (p + q * ε)) + χ ω * c * (q - p) := by
    have := mul_le_mul_of_nonneg_left hS1b (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  have he : e = h / δ := by rw [← hδe]; field_simp
  have hfin : 2 * b + 2 * L * (T * e / M + ε) + c * χ ω * (1 - T * e / M) =
      (h / M) * (2 * (b * q + L * (p + q * ε)) + χ ω * c * (q - p)) := by
    rw [hq, hp, he]
    field_simp
  rw [hfin]
  exact mul_nonneg (div_nonneg hh.le hM.le) hX

/-! ### Limit inputs along the subsequence -/

/-- Tightness at `∞` gives a finite radius `K₂` beyond which `α` has mass `< ε`. -/
private lemma exists_tight_radius {μ : Measure (ℝ≥0∞ × ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ {p | p.1 = ⊤} = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₂ : ℝ, 0 < K₂ ∧ μ {p | ENNReal.ofReal K₂ ≤ p.1} < ENNReal.ofReal ε := by
  set s : ℕ → Set (ℝ≥0∞ × ℝ) := fun k => {p | (k : ℝ≥0∞) ≤ p.1} with hs
  have hmeas : ∀ k, MeasurableSet (s k) := fun k =>
    (isClosed_le continuous_const continuous_fst).measurableSet
  have hanti : Antitone s := fun k k' hkk' p hp =>
    le_trans (by exact_mod_cast hkk') (show (k' : ℝ≥0∞) ≤ p.1 from hp)
  have hinter : ⋂ k, s k = {p | p.1 = ⊤} := by
    ext p
    simp only [hs, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_contra hne
      obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hne
      exact absurd (h k) (not_le.2 hk)
    · intro h k; rw [h]; exact le_top
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hmeas k).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter, hμ] at hlim
  have hev := (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 hε)
  obtain ⟨k, hk, hk1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  refine ⟨k, by exact_mod_cast hk1, ?_⟩
  simpa [hs, ENNReal.ofReal_natCast] using hk

/-- `e_n > 0` eventually, since `W_n(1) → W(1) ≥ a > 0` while `W_n ≡ 0` when `e_n = 0`. -/
private lemma eventually_scale_pos {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) : ∀ᶠ n in atTop, 0 < S.scale a (NL.φ n) := by
  obtain ⟨-, hW1, -⟩ := NL.props ha haJ
  have hWt := NL.W_conv.tendsto_at (show (1 : ℝ) ∈ Ioi 0 from Set.mem_Ioi.2 one_pos)
  filter_upwards [hWt.eventually (lt_mem_nhds (show (0 : ℝ) < NL.W 1 by linarith))] with n hn
  rcases (show 0 ≤ S.scale a (NL.φ n) from
    mul_nonneg (S.h_pos _).le (Nat.cast_nonneg _)).lt_or_eq with h | h
  · exact h
  · exfalso
    unfold SelectedSeq.Wn SelectedSeq.Vn at hn
    rw [← h, zero_mul, interp_of_nonpos (S.h_pos _) le_rfl, (S.isApproxEq _).cone.zero] at hn
    exact lt_irrefl 0 hn

private lemma measurable_ι (S : SelectedSeq P) (a : ℝ) (n : ℕ) : Measurable (S.ι a n) :=
  (ENNReal.measurable_ofReal.comp (measurable_id.div_const _)).prodMk
    (continuous_interp (S.h_pos n)).measurable

/-- The mass of `{z ≥ K₂}` under `α_n` in index form. -/
private lemma tight_index {S : SelectedSeq P} {a : ℝ} {n : ℕ} (he : 0 < S.scale a n)
    {K₂ ε : ℝ} (hε : 0 < ε)
    (hα : S.αn a n {p | ENNReal.ofReal K₂ ≤ p.1} < ENNReal.ofReal ε) :
    ∑ l ∈ Finset.range (S.N n + 1), S.η n l * (if K₂ ≤ (l : ℝ) * S.δn a n then 1 else 0) ≤ ε := by
  have hC : MeasurableSet {p : ℝ≥0∞ × ℝ | ENNReal.ofReal K₂ ≤ p.1} :=
    (isClosed_le continuous_const continuous_fst).measurableSet
  rw [SelectedSeq.αn, Measure.map_apply (measurable_ι S a n) hC, SelectedSeq.ηn,
    gridMeasure_apply' (S.isApproxEq n).law.nonneg (measurable_ι S a n hC),
    ENNReal.ofReal_lt_ofReal_iff hε] at hα
  refine le_of_lt (lt_of_eq_of_lt (Finset.sum_congr rfl fun l _ => ?_) hα)
  have hiff : ENNReal.ofReal K₂ ≤ ENNReal.ofReal ((l : ℝ) * S.h n / S.scale a n) ↔
      K₂ ≤ (l : ℝ) * S.δn a n := by
    rw [ENNReal.ofReal_le_ofReal_iff
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (S.h_pos n).le) he.le)]
    unfold SelectedSeq.δn
    rw [mul_div_assoc]
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, SelectedSeq.ι]
  by_cases hcond : K₂ ≤ (l : ℝ) * S.δn a n
  · rw [ite_eq_left hcond, ite_eq_left (hiff.2 hcond), mul_one]
  · rw [ite_eq_right hcond, ite_eq_right (mt hiff.1 hcond), mul_zero]

/-- `thm:noplateau`: every normalized limit exhibits finite-wealth saturation. -/
theorem NormalizedLimit.noplateau {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) : NL.HasFiniteSaturation := by
  by_contra hnp
  have htight := NL.count ha haJ hnp
  have hC := NL.coeff ha haJ hnp htight
  obtain ⟨ω, hω, c, hc, K, hK, hK0, hthick⟩ := NL.splitting ha haJ hnp htight hC
  have hent := fun n => entropy (S.isApproxEq (NL.φ n))
  -- The size-biased entropy budget: on `Λ_n^B` the thick sellers force
  -- `∫ F dΛ_n^B ≤ (c/2) χ(ω) + ε log 2 + o(1)`, on `Λ_n^S` `∫ F dΛ_n^S ≤ ε log 2 + o(1)`, so
  -- `∫ F dΛ_n < 0` for large `n`, contradicting `eq:entropy`.
  obtain ⟨K', n0, hK'⟩ := hthick (c / 2) (by linarith)
  have hχω := χ_neg hω
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := P.M_pos
  -- the budget `A = (c/2)|χ(ω)|` and the tolerance `ε` with `2 ε log 2 = A/4`
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = -(c / 2 * χ ω) := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; nlinarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = A / (8 * Real.log 2) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  have h2Lε : 2 * Real.log 2 * ε = A / 4 := by rw [hε]; field_simp; ring
  -- tightness radius, entropy threshold, buyer threshold
  have := NL.α_prob
  obtain ⟨K₂, hK₂, hαK₂⟩ := exists_tight_radius htight hεpos
  obtain ⟨t₀, ht₀pos, ht₀half, hbt₀⟩ := exists_binEntropy_small (show 0 < A / 8 by positivity)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max K' (K₂ / t₀) := ⟨_, rfl⟩
  have hTpos : 0 < T := hT ▸ lt_of_lt_of_le (div_pos hK₂ ht₀pos) (le_max_right _ _)
  have hKt : K₂ / T ≤ t₀ := by
    rw [div_le_iff₀ hTpos]
    have h1 : K₂ / t₀ ≤ T := hT ▸ le_max_right _ _
    rw [div_le_iff₀ ht₀pos] at h1
    linarith
  -- tightness holds frequently (Portmanteau for the closed set `{z ≥ K₂}`)
  have hCcl : IsClosed {p : ℝ≥0∞ × ℝ | ENNReal.ofReal K₂ ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hαprob : ∀ n, IsProbabilityMeasure (S.αn a (NL.φ n)) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (measurable_ι S a _).aemeasurable).mpr
      (gridMeasure_isProb (S.isApproxEq _).law)
  have hfreq : ∃ᶠ n in atTop,
      S.αn a (NL.φ n) {p | ENNReal.ofReal K₂ ≤ p.1} < ENNReal.ofReal ε := by
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    have := NL.α_conv.le_measure_closed hαprob NL.α_prob hCcl
      (hcon.mono fun n hn => not_lt.1 hn)
    exact absurd hαK₂ (not_lt.2 this)
  -- eventually: thickness applies, `e_n > 0` and `e_n` is small
  obtain ⟨he0, -⟩ := NL.props ha haJ
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = A * P.M / (4 * T * (2 * Real.log 2 + A)) := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hB]; positivity
  have hev : ∀ᶠ n in atTop, n0 ≤ n ∧ 0 < S.scale a (NL.φ n) ∧ S.scale a (NL.φ n) < B :=
    (eventually_ge_atTop n0).and
      ((eventually_scale_pos NL ha haJ).and ((tendsto_order.1 he0).2 B hBpos))
  obtain ⟨n, hαn, hn0, hepos, heB⟩ := (hfreq.and_eventually hev).exists
  -- the entropy budget at the approximant `φ n`
  have hh := S.h_pos (NL.φ n)
  have hδ : 0 < NL.δ' n := div_pos hh hepos
  have hδe : NL.δ' n * S.scale a (NL.φ n) = S.h (NL.φ n) := div_mul_cancel₀ _ hepos.ne'
  have hentn := (mul_eq_zero.1 (hent n)).resolve_left (inv_ne_zero (by positivity))
  have key := core_bound hh hM hδ hδe (S.isApproxEq (NL.φ n)).law
    (S.isApproxEq (NL.φ n)).kernel hω.1.le (by linarith : (0 : ℝ) ≤ c / 2) hTpos hK₂
    hKt ht₀half hχω.le (fun m => NL.splitSet ω K n m) (fun m => Finset.filter_subset _ _)
    (fun m hm l hl j hj hκ => by
      have hl' := Finset.mem_filter.1 hl
      have hlN : l ≤ S.N (NL.φ n) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl'.1)
      exact hl'.2.2 j (Finset.mem_filter.2
        ⟨hj, (S.isApproxEq (NL.φ n)).argmax m hm l hlN j hj hκ⟩))
    (fun m hm hTm => by
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, Nat.cast_zero, zero_mul] at hTm; linarith
        · exact h0
      have := hK' n hn0 m hm1 hm (le_trans (hT ▸ le_max_left _ _) hTm.le)
      unfold NormalizedLimit.lawMass at this
      linarith)
    (tight_index hepos hεpos hαn) hentn
  -- contradiction: the budget is `≤ -A/4 < 0`
  have hx : T * S.scale a (NL.φ n) / P.M * (2 * Real.log 2 + A) < A / 4 := by
    rw [hB, lt_div_iff₀ (by positivity)] at heB
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM]
    nlinarith
  have hcA : c / 2 * χ ω = -A := by rw [hA]; ring
  rw [hcA] at key
  nlinarith

end Molico
