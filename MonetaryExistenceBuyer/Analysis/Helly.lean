import MonetaryExistenceBuyer.Analysis.Concave
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Convex.Continuous

/-!
# Helly / Arzelà–Ascoli for concave nondecreasing functions

Uniformly bounded, nondecreasing, concave functions on `[0, ∞)` are uniformly Lipschitz on every
`[a, ∞)`, `a > 0` (`concave_lipschitz`). A diagonal argument over the positive rationals (Helly)
plus equicontinuity (Arzelà–Ascoli) yields a subsequence converging locally uniformly on
`(0, ∞)` (used in `def:selected`, `thm:halflevel`, `def:normalization`).
-/

open Set Filter Topology

noncomputable section

namespace Molico

/-- Symmetric form of the uniform Lipschitz bound `concave_lipschitz`. -/
lemma abs_sub_le_of_concave {f : ℝ → ℝ} {B a : ℝ} (hconc : ConcaveOn ℝ (Ici 0) f)
    (hmono : MonotoneOn f (Ici 0)) (hbd : ∀ x, 0 ≤ x → 0 ≤ f x ∧ f x ≤ B) (ha : 0 < a)
    {x y : ℝ} (hx : a ≤ x) (hy : a ≤ y) : |f x - f y| ≤ B / a * |x - y| := by
  rcases le_total x y with h | h
  · have := concave_lipschitz hconc hmono hbd ha hx h
    rw [abs_sub_comm, abs_of_nonneg this.1, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact this.2
  · have := concave_lipschitz hconc hmono hbd ha hy h
    rw [abs_of_nonneg this.1, abs_of_nonneg (sub_nonneg.2 h)]
    exact this.2

/-- Equicontinuity plus convergence at the positive rationals gives pointwise Cauchy sequences
on `(0, ∞)`. -/
lemma cauchySeq_of_rat_of_concave {F : ℕ → ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n, MonotoneOn (F n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (F n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ F n x ∧ F n x ≤ B)
    (hq : ∀ r : ℚ, 0 < r → CauchySeq (fun n => F n r)) {x : ℝ} (hx : 0 < x) :
    CauchySeq (fun n => F n x) := by
  have hB : 0 ≤ B := (hbd 0 0 le_rfl).1.trans (hbd 0 0 le_rfl).2
  have hL : 0 ≤ B / x := div_nonneg hB hx.le
  have hL1 : 0 < B / x + 1 := by linarith
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hδ : 0 < ε / (3 * (B / x + 1)) := div_pos hε (mul_pos (by norm_num) hL1)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_add_of_pos_right x hδ)
  have hr0 : (0 : ℚ) < r := by exact_mod_cast hx.trans hr1
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hq r hr0) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have key : ∀ k, |F k x - F k r| ≤ B / x * (r - x) := by
    intro k
    have := concave_lipschitz (hconc k) (hmono k) (hbd k) hx le_rfl hr1.le
    rw [abs_sub_comm, abs_of_nonneg this.1]
    exact this.2
  have hLr : B / x * (r - x) < ε / 3 := by
    calc B / x * (r - x) ≤ B / x * (ε / (3 * (B / x + 1))) :=
          mul_le_mul_of_nonneg_left (by linarith) hL
      _ < (B / x + 1) * (ε / (3 * (B / x + 1))) := mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε / 3 := by field_simp
  have k1 := abs_le.1 (key m)
  have k2 := abs_le.1 (key n)
  have h1 : |F m r - F n r| < ε / 3 := by rw [← Real.dist_eq]; exact hN m hm n hn
  have k3 := abs_lt.1 h1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [k1.1, k1.2, k2.1, k2.2, k3.1, k3.2]

/-- Pointwise Cauchy plus equicontinuity gives uniformly Cauchy sequences on compact intervals
`[a, b] ⊆ (0, ∞)`. -/
lemma uniformCauchySeqOn_Icc_of_concave {F : ℕ → ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n, MonotoneOn (F n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (F n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ F n x ∧ F n x ≤ B)
    (hc : ∀ x, 0 < x → CauchySeq (fun n => F n x)) {a b : ℝ} (ha : 0 < a) :
    UniformCauchySeqOn F atTop (Icc a b) := by
  have hB : 0 ≤ B := (hbd 0 0 le_rfl).1.trans (hbd 0 0 le_rfl).2
  have hL : 0 ≤ B / a := div_nonneg hB ha.le
  have hL1 : 0 < B / a + 1 := by linarith
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hδ : 0 < ε / (3 * (B / a + 1)) := div_pos hε (mul_pos (by norm_num) hL1)
  obtain ⟨T, hTs, hTfin, hcov⟩ := (isCompact_Icc (a := a) (b := b)).finite_cover_balls hδ
  have hev : ∀ᶠ N in atTop, ∀ y ∈ T, ∀ m ≥ N, ∀ n ≥ N, dist (F m y) (F n y) < ε / 3 := by
    rw [eventually_all_finite hTfin]
    intro y hy
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.1 (hc y (ha.trans_le (hTs hy).1)) (ε / 3) (by positivity)
    exact eventually_atTop.2 ⟨N, fun N' hN' m hm n hn => hN m (hN'.trans hm) n (hN'.trans hn)⟩
  obtain ⟨N, hN⟩ := hev.exists
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.1 (hcov hx)
  have hyI := hTs hyT
  have hxy' : |x - y| < ε / (3 * (B / a + 1)) := by
    rwa [Metric.mem_ball, Real.dist_eq] at hxy
  have hLxy : B / a * |x - y| < ε / 3 := by
    calc B / a * |x - y| ≤ B / a * (ε / (3 * (B / a + 1))) :=
          mul_le_mul_of_nonneg_left hxy'.le hL
      _ < (B / a + 1) * (ε / (3 * (B / a + 1))) := mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε / 3 := by field_simp
  have k1 := abs_le.1 (abs_sub_le_of_concave (hconc m) (hmono m) (hbd m) ha hx.1 hyI.1)
  have k2 := abs_le.1 (abs_sub_le_of_concave (hconc n) (hmono n) (hbd n) ha hx.1 hyI.1)
  have h1 : |F m y - F n y| < ε / 3 := by rw [← Real.dist_eq]; exact hN y hyT m hm n hn
  have k3 := abs_lt.1 h1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [k1.1, k1.2, k2.1, k2.2, k3.1, k3.2]

/-- Helly / Arzelà–Ascoli extraction for concave nondecreasing uniformly bounded functions. -/
theorem helly_concave {f : ℕ → ℝ → ℝ} {B : ℝ} (hmono : ∀ n, MonotoneOn (f n) (Ici 0))
    (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (f n)) (hbd : ∀ n x, 0 ≤ x → 0 ≤ f n x ∧ f n x ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℝ → ℝ,
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop (Ioi 0) := by
  -- Step 1: diagonal extraction at the positive rationals (compactness of a countable product).
  have hK : IsCompact (Set.pi univ (fun _ : ℚ => Icc (0 : ℝ) B)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨L, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun n (r : ℚ) => f n |(r : ℝ)|)
    (fun n => mem_univ_pi.2 fun r => ⟨(hbd n _ (abs_nonneg _)).1, (hbd n _ (abs_nonneg _)).2⟩)
  have hq : ∀ r : ℚ, 0 < r → CauchySeq (fun n => f (φ n) r) := by
    intro r hr
    have h := tendsto_pi_nhds.1 hlim r
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    simp only [Function.comp_apply, abs_of_pos hr'] at h
    exact h.cauchySeq
  -- Step 2: pointwise Cauchy on `(0, ∞)`.
  have hc : ∀ x, 0 < x → CauchySeq (fun n => f (φ n) x) := fun x hx =>
    cauchySeq_of_rat_of_concave (fun n => hmono (φ n)) (fun n => hconc (φ n))
      (fun n => hbd (φ n)) hq hx
  refine ⟨φ, hφ, fun x => limUnder atTop (fun n => f (φ n) x), ?_⟩
  have hpt : ∀ x, 0 < x → Tendsto (fun n => f (φ n) x) atTop
      (𝓝 (limUnder atTop (fun n => f (φ n) x))) :=
    fun x hx => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hc x hx))
  -- Step 3: uniform convergence on `[x/2, 2x]`.
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  have hx' : (0 : ℝ) < x := hx
  refine ⟨Icc (x / 2) (2 * x),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  exact (uniformCauchySeqOn_Icc_of_concave (fun n => hmono (φ n)) (fun n => hconc (φ n))
    (fun n => hbd (φ n)) hc (by linarith : (0 : ℝ) < x / 2)).tendstoUniformlyOn_of_tendsto
    (fun y hy => hpt y (by linarith [hy.1]))

/-- Properties of a locally uniform limit on `(0, ∞)` of such functions. -/
theorem concave_limit_props {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n, MonotoneOn (f n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (f n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ f n x ∧ f n x ≤ B)
    (hlim : TendstoLocallyUniformlyOn f g atTop (Ioi 0)) :
    MonotoneOn g (Ioi 0) ∧ ConcaveOn ℝ (Ioi 0) g ∧ ContinuousOn g (Ioi 0) ∧
      (∀ x, 0 < x → 0 ≤ g x ∧ g x ≤ B) ∧
      (∀ x, 0 < x → ∀ t, 0 < t → t ≤ 1 → t * g x ≤ g (t * x)) := by
  have hT : ∀ x, 0 < x → Tendsto (fun n => f n x) atTop (𝓝 (g x)) :=
    fun x hx => hlim.tendsto_at hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact le_of_tendsto_of_tendsto' (hT x hx) (hT y hy)
      (fun n => hmono n (mem_Ici.2 (mem_Ioi.1 hx).le) (mem_Ici.2 (mem_Ioi.1 hy).le) hxy)
  · refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hxy : 0 < a • x + b • y := (convex_Ioi (0 : ℝ)) hx hy ha hb hab
    have h1 := ((hT x hx).const_smul a).add ((hT y hy).const_smul b)
    exact le_of_tendsto_of_tendsto' h1 (hT _ hxy)
      (fun n => (hconc n).2 (mem_Ici.2 (mem_Ioi.1 hx).le) (mem_Ici.2 (mem_Ioi.1 hy).le) ha hb hab)
  · refine hlim.continuousOn (Eventually.of_forall fun n => ?_).frequently
    simpa [interior_Ici] using (hconc n).continuousOn_interior
  · intro x hx
    exact ⟨ge_of_tendsto' (hT x hx) (fun n => (hbd n x hx.le).1),
      le_of_tendsto' (hT x hx) (fun n => (hbd n x hx.le).2)⟩
  · intro x hx t ht0 ht1
    exact le_of_tendsto_of_tendsto' ((hT x hx).const_mul t) (hT _ (mul_pos ht0 hx))
      (fun n => concave_mul_le (hconc n) (hbd n 0 le_rfl).1 ht0.le ht1 hx.le)

/-- Convergence along converging arguments: if `x_n → x > 0` then `f_n(x_n) → g(x)`. -/
theorem tendsto_comp_of_concave {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n, MonotoneOn (f n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (f n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ f n x ∧ f n x ≤ B)
    (hlim : TendstoLocallyUniformlyOn f g atTop (Ioi 0)) {x : ℝ} (hx : 0 < x) {xs : ℕ → ℝ}
    (hxs : Tendsto xs atTop (𝓝 x)) : Tendsto (fun n => f n (xs n)) atTop (𝓝 (g x)) := by
  have hcont := (concave_limit_props hmono hconc hbd hlim).2.2.1
  refine hlim.tendsto_comp (hcont.continuousWithinAt hx) hx ?_
  exact tendsto_nhdsWithin_iff.2 ⟨hxs, hxs.eventually (Ioi_mem_nhds hx)⟩

/-- Upper bound near the origin: if `x_n → 0` with `x_n ≥ 0`, then
`limsup f_n(x_n) ≤ g(0+) = inf_{x > 0} g(x)`; precisely, for every `x > 0`, eventually
`f_n(x_n) ≤ g(x) + ε`. -/
theorem eventually_le_of_tendsto_zero {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n, MonotoneOn (f n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (f n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ f n x ∧ f n x ≤ B)
    (hlim : TendstoLocallyUniformlyOn f g atTop (Ioi 0)) {xs : ℕ → ℝ} (hxs0 : ∀ n, 0 ≤ xs n)
    (hxs : Tendsto xs atTop (𝓝 0)) {x : ℝ} (hx : 0 < x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, f n (xs n) ≤ g x + ε := by
  filter_upwards [hxs.eventually (Iio_mem_nhds hx),
    (hlim.tendsto_at hx).eventually_lt_const (lt_add_of_pos_right (g x) hε)] with n hn1 hn2
  exact (hmono n (hxs0 n) hx.le (mem_Iio.1 hn1).le).trans hn2.le

/-- Lower bound at infinity: if `x_n → ∞`, then for every `x > 0`, eventually
`f_n(x_n) ≥ g(x) - ε`. -/
theorem eventually_ge_of_tendsto_atTop {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n, MonotoneOn (f n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (f n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ f n x ∧ f n x ≤ B)
    (hlim : TendstoLocallyUniformlyOn f g atTop (Ioi 0)) {xs : ℕ → ℝ}
    (hxs : Tendsto xs atTop atTop) {x : ℝ} (hx : 0 < x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, g x - ε ≤ f n (xs n) := by
  filter_upwards [hxs.eventually_ge_atTop x,
    (hlim.tendsto_at hx).eventually_const_lt (sub_lt_self (g x) hε)] with n hn1 hn2
  exact hn2.le.trans (hmono n hx.le (hx.le.trans hn1) hn1)

/-- No jump at the origin upgrades the convergence to locally uniform convergence on `[0, ∞)`
(first line of the proof of `thm:zerojump`). -/
theorem tendstoLocallyUniformlyOn_Ici_of_noJump {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {B : ℝ}
    (hmono : ∀ n, MonotoneOn (f n) (Ici 0)) (hconc : ∀ n, ConcaveOn ℝ (Ici 0) (f n))
    (hbd : ∀ n x, 0 ≤ x → 0 ≤ f n x ∧ f n x ≤ B) (hf0 : ∀ n, f n 0 = 0)
    (hlim : TendstoLocallyUniformlyOn f g atTop (Ioi 0)) (hg0 : g 0 = 0)
    (hjump : Tendsto g (𝓝[>] 0) (𝓝 0)) :
    TendstoLocallyUniformlyOn f g atTop (Ici 0) := by
  have hlim' := Metric.tendstoLocallyUniformlyOn_iff.1 hlim
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  rcases (mem_Ici.1 hx).eq_or_lt with h0 | hpos
  · subst h0
    have hball : g ⁻¹' Metric.ball 0 (ε / 3) ∈ 𝓝[>] (0 : ℝ) :=
      hjump (Metric.ball_mem_nhds 0 (by positivity))
    obtain ⟨δ, hδ, hδs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hball
    have hδ' : (0 : ℝ) < δ := hδ
    have hsmall : ∀ y, 0 ≤ y → y < δ → |g y| < ε / 3 := by
      intro y hy0 hyδ
      rcases hy0.eq_or_lt with h | h
      · rw [← h, hg0, abs_zero]; positivity
      · have := hδs ⟨h, hyδ⟩
        simpa [Real.dist_eq] using this
    have hgd := abs_lt.1 (hsmall (δ / 2) (by linarith) (by linarith))
    have hfd : ∀ᶠ n in atTop, f n (δ / 2) < ε / 2 :=
      (hlim.tendsto_at (show (0 : ℝ) < δ / 2 by linarith)).eventually_lt_const
        (by linarith [hgd.2])
    refine ⟨Icc 0 (δ / 2), Icc_mem_nhdsGE (by linarith), ?_⟩
    filter_upwards [hfd] with n hn y hy
    have hgy := abs_lt.1 (hsmall y hy.1 (by linarith [hy.2]))
    have hfy0 := (hbd n y hy.1).1
    have hfy1 : f n y ≤ f n (δ / 2) := hmono n hy.1 (by linarith [hy.2] : (0 : ℝ) ≤ δ / 2) hy.2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hgy.1, hgy.2]
  · obtain ⟨t, ht, hev⟩ := hlim' ε hε x hpos
    rw [isOpen_Ioi.nhdsWithin_eq hpos] at ht
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, hev⟩

end Molico
