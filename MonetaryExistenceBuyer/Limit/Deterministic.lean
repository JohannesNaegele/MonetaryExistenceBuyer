import MonetaryExistenceBuyer.Model
import MonetaryExistenceBuyer.Necessity

/-!
# Purification (`prop:deterministic`)
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

section Helpers

variable (U : AdmissibleUtility) {V : ℝ → ℝ}

/-- Positive monetary trade forces `V ≢ 0` on `[0,∞)`. -/
private lemma exists_pos_of_monetary {β M : ℝ} {η : Measure ℝ} {Γ : Measure (ℝ × ℝ × ℝ)}
    (h : IsEquilibrium U.u β M V η Γ) : ∃ y, 0 ≤ y ∧ 0 < V y := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  apply h.monetary
  have hV := h.value
  have hae : ∀ᵐ p ∂Γ, ¬ (0 < gain V p.2.1 p.2.2) := by
    filter_upwards [h.ae_good] with p hp hmon
    have h1 := hcon _ (show 0 ≤ p.2.1 + p.2.2 by linarith [hp.2.1, hp.2.2.1])
    have h2 := hV.nonneg hp.2.1
    have h3 := hmon
    simp only [gain] at h3
    linarith
  rw [ae_iff] at hae
  simpa using hae

/-- A concave nondecreasing function which is not strictly increasing has a plateau. -/
private lemma plateau_of_not_strictMono (hV : IsValueFn V) (hns : ¬ StrictMonoOn V (Ici 0)) :
    ∃ x₀, 0 ≤ x₀ ∧ ∀ z, x₀ ≤ z → V z = V x₀ := by
  simp only [StrictMonoOn, not_forall, not_lt] at hns
  obtain ⟨x, hx, y, hy, hxy, hle⟩ := hns
  have hx' : 0 ≤ x := hx
  refine ⟨x, hx', fun z hz => ?_⟩
  have hVxy : V y = V x := le_antisymm hle (hV.le_of_le hx' hxy.le)
  rcases le_or_gt z y with hzy | hyz
  · exact le_antisymm (by have := hV.le_of_le (hx'.trans hz) hzy; linarith)
      (hV.le_of_le hx' hz)
  · have hsl := hV.concaveOn.slope_anti_adjacent hx
      (show z ∈ Ici (0:ℝ) from hx'.trans (hxy.le.trans hyz.le)) hxy hyz
    rw [hVxy, sub_self, zero_div, div_nonpos_iff] at hsl
    have h1 : V z - V x ≤ 0 := by
      rcases hsl with ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · exact h1
    exact le_antisymm (by linarith) (hV.le_of_le hx' hz)

/-- The first plateau point. -/
private lemma first_plateau (hV : IsValueFn V) {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hpl : ∀ z, x₀ ≤ z → V z = V x₀) :
    ∃ p, 0 ≤ p ∧ (∀ z, p ≤ z → V z = V x₀) ∧ ∀ x, 0 ≤ x → x < p → V x < V x₀ := by
  set L := V x₀ with hL
  set S : Set ℝ := {x | 0 ≤ x ∧ ∀ z, x ≤ z → V z = L} with hS_def
  have hS : S.Nonempty := ⟨x₀, hx₀, hpl⟩
  have hSb : BddBelow S := ⟨0, fun x hx => hx.1⟩
  set p := sInf S with hp_def
  have hp0 : 0 ≤ p := le_csInf hS (fun x hx => hx.1)
  have hle : ∀ z, 0 ≤ z → V z ≤ L := fun z hz => by
    rcases le_total z x₀ with h | h
    · exact hV.le_of_le hz h
    · exact (hpl z h).le
  have hgt : ∀ z, p < z → V z = L := by
    intro z hz
    obtain ⟨x, hxS, hxz⟩ := exists_lt_of_csInf_lt hS hz
    exact hxS.2 z hxz.le
  have hpL : V p = L := by
    have hc : ContinuousWithinAt V (Ioi p) p :=
      (hV.continuousOn p hp0).mono (fun z hz => hp0.trans (le_of_lt hz))
    have h2 : Tendsto V (𝓝[>] p) (𝓝 L) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => (hgt z hz).symm)
    exact tendsto_nhds_unique hc h2
  refine ⟨p, hp0, fun z hz => ?_, fun x hx hxp => ?_⟩
  · rcases hz.eq_or_lt with rfl | hz
    · exact hpL
    · exact hgt z hz
  · refine lt_of_le_of_ne (hle x hx) (fun hxL => ?_)
    have hxS : x ∈ S := ⟨hx, fun z hz => le_antisymm (hle z (hx.trans hz))
      (by rw [← hxL]; exact hV.le_of_le hx hz)⟩
    exact absurd (csInf_le hSb hxS) (not_le.2 hxp)

/-- Step 1 of `prop:deterministic`: the value function is strictly increasing. -/
private lemma strictMonoOn_value {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {η : Measure ℝ}
    {Γ : Measure (ℝ × ℝ × ℝ)} (h : IsEquilibrium U.u β M V η Γ) :
    StrictMonoOn V (Ici 0) := by
  have hV := h.value
  have := h.isProb_η
  by_contra hns
  obtain ⟨x₀, hx₀, hpl⟩ := plateau_of_not_strictMono hV hns
  obtain ⟨p, hp0, hpge, hplt⟩ := first_plateau hV hx₀ hpl
  set L := V x₀ with hL
  obtain ⟨y, hy, hVy⟩ := exists_pos_of_monetary U h
  have hLpos : 0 < L := by
    have : V y ≤ L := by
      rcases le_total y x₀ with h' | h'
      · exact hV.le_of_le hy h'
      · exact (hpl y h').le
    linarith
  have hpL : V p = L := hpge _ le_rfl
  have hp : 0 < p := by
    rcases hp0.eq_or_lt with h' | h'
    · exfalso
      rw [← h', hV.zero] at hpL
      linarith
    · exact h'
  obtain ⟨G, hG, hGb, hGeq⟩ := exists_continuous_bellH U hV
  have hint : ∀ m, Integrable (fun s => G (m, s)) η := fun m =>
    Integrable.of_bound (hG.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      (U.ubar + hV.sup) (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGb _).1]; exact (hGb _).2)
  have hbell : ∀ m, 0 ≤ m → V m = β * ∫ s, G (m, s) ∂η := by
    intro m hm
    rw [h.bellman m hm, bellT]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h.ae_η_nonneg] with s hs
    exact (hGeq m s hm hs).symm
  have h2p : V (2 * p) = L := hpge _ (by linarith)
  have hzero : ∫ s, (G (2 * p, s) - G (p, s)) ∂η = 0 := by
    rw [integral_sub (hint _) (hint _)]
    have e1 := hbell (2 * p) (by linarith)
    have e2 := hbell p hp0
    rw [h2p] at e1
    rw [hpL] at e2
    have : β * (∫ s, G (2 * p, s) ∂η - ∫ s, G (p, s) ∂η) = 0 := by rw [mul_sub]; linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  have hnn : 0 ≤ᵐ[η] fun s => G (2 * p, s) - G (p, s) := by
    filter_upwards [h.ae_η_nonneg] with s hs
    rw [hGeq _ _ (by linarith) hs, hGeq _ _ hp0 hs]
    simp only [Pi.zero_apply, sub_nonneg]
    exact bellH_mono U hV hp0 (by linarith) hs
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn ((hint _).sub (hint _))).1 hzero
  have hHL : ∀ᵐ s ∂η, G (p, s) = L := by
    filter_upwards [hae, h.ae_η_nonneg] with s hs hs0
    simp only [Pi.zero_apply, sub_eq_zero] at hs
    rw [hGeq _ _ (by linarith) hs0, hGeq _ _ hp0 hs0] at hs
    rw [hGeq _ _ hp0 hs0]
    obtain ⟨d, hd, hdeq⟩ := exists_bellH_eq U hV hp0 hs0
    rcases hd.1.eq_or_lt with hd0 | hd0
    · rw [← hdeq, ← hd0, obj_zero U hV, hpL]
    · exfalso
      have h1 := obj_le_bellH U hV (show 0 ≤ 2 * p by linarith) hs0
        (show d ∈ Icc 0 (2 * p) from ⟨hd.1, by linarith [hd.2]⟩)
      have h2 : V (2 * p - d) = L := hpge _ (by linarith [hd.2])
      have h3 : V (p - d) < L := hplt _ (by linarith [hd.2]) (by linarith)
      unfold obj at h1 hdeq
      rw [h2] at h1
      linarith
  have hfin : V p = β * L := by
    rw [hbell p hp0, integral_congr_ae hHL, integral_const]
    simp
  rw [hpL] at hfin
  nlinarith [mul_pos hLpos (sub_pos.2 hβ1)]

/-- Step 2 of `prop:deterministic`: uniqueness of the optimiser (strict concavity). -/
private lemma argmax_unique (hV : IsValueFn V) (hsm : StrictMonoOn V (Ici 0)) {b s d₁ d₂ : ℝ}
    (hb : 0 ≤ b) (hs : 0 ≤ s) (hd₁ : d₁ ∈ Icc 0 b) (hd₂ : d₂ ∈ Icc 0 b)
    (h₁ : obj U.u V b s d₁ = bellH U.u V b s) (h₂ : obj U.u V b s d₂ = bellH U.u V b s) :
    d₁ = d₂ := by
  by_contra hne
  set m := (d₁ + d₂) / 2 with hm_def
  have hm : m ∈ Icc 0 b := ⟨by linarith [hd₁.1, hd₂.1], by linarith [hd₁.2, hd₂.2]⟩
  have hmax := obj_le_bellH U hV hb hs hm
  have hc1 : (1/2 : ℝ) * V (s + d₁) + (1/2) * V (s + d₂) ≤ V (s + m) := by
    have := hV.concaveOn.2 (show s + d₁ ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hd₁.1])
      (show s + d₂ ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hd₂.1])
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm_def]; ring
  have hc2 : (1/2 : ℝ) * V (b - d₁) + (1/2) * V (b - d₂) ≤ V (b - m) := by
    have := hV.concaveOn.2 (show b - d₁ ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hd₁.2])
      (show b - d₂ ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hd₂.2])
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    convert this using 2
    rw [hm_def]; ring
  set g₁ := gain V s d₁ with hg₁_def
  set g₂ := gain V s d₂ with hg₂_def
  have hg₁ : 0 ≤ g₁ := hV.gain_nonneg hs hd₁.1
  have hg₂ : 0 ≤ g₂ := hV.gain_nonneg hs hd₂.1
  have hgne : g₁ ≠ g₂ := by
    intro heq
    apply hne
    simp only [hg₁_def, hg₂_def, gain] at heq
    have h' : V (s + d₁) = V (s + d₂) := by linarith
    have := hsm.injOn (show s + d₁ ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hd₁.1])
      (show s + d₂ ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hd₂.1]) h'
    linarith
  have hu1 : (1/2 : ℝ) * U.u g₁ + (1/2) * U.u g₂ < U.u ((1/2) * g₁ + (1/2) * g₂) := by
    have := U.strictConcaveOn.2 (show g₁ ∈ Ici (0:ℝ) from hg₁) (show g₂ ∈ Ici (0:ℝ) from hg₂)
      hgne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simpa only [smul_eq_mul] using this
  have hu2 : U.u ((1/2) * g₁ + (1/2) * g₂) ≤ U.u (gain V s m) := by
    apply U.monotoneOn (show (1/2) * g₁ + (1/2) * g₂ ∈ Ici (0:ℝ) by
        simp only [mem_Ici]; positivity)
      (show gain V s m ∈ Ici (0:ℝ) from hV.gain_nonneg hs hm.1)
    simp only [hg₁_def, hg₂_def, gain]
    linarith
  unfold obj at h₁ h₂ hmax
  linarith

/-- The (chosen) optimiser on the quadrant, `0` outside. -/
private def argmaxFn (hV : IsValueFn V) (q : ℝ × ℝ) : ℝ :=
  if hq : 0 ≤ q.1 ∧ 0 ≤ q.2 then Classical.choose (exists_bellH_eq U hV hq.1 hq.2) else 0

private lemma argmaxFn_spec (hV : IsValueFn V) {q : ℝ × ℝ} (hq : 0 ≤ q.1 ∧ 0 ≤ q.2) :
    argmaxFn U hV q ∈ Icc 0 q.1 ∧
      obj U.u V q.1 q.2 (argmaxFn U hV q) = bellH U.u V q.1 q.2 := by
  unfold argmaxFn
  rw [dite_eq_left hq]
  exact Classical.choose_spec (exists_bellH_eq U hV hq.1 hq.2)

private lemma argmaxFn_of_not (hV : IsValueFn V) {q : ℝ × ℝ} (hq : ¬ (0 ≤ q.1 ∧ 0 ≤ q.2)) :
    argmaxFn U hV q = 0 := by
  unfold argmaxFn
  rw [dite_eq_right hq]

/-- Jointly continuous extension of the Bellman objective. -/
private def objExt (V : ℝ → ℝ) (q : ℝ × ℝ) (t : ℝ) : ℝ :=
  posPart U.u (posPart V (q.2 + t) - posPart V q.2) + posPart V (q.1 - t)

private lemma objExt_eq (hV : IsValueFn V) {q : ℝ × ℝ} {t : ℝ} (hs : 0 ≤ q.2)
    (ht : t ∈ Icc 0 q.1) : objExt U V q t = obj U.u V q.1 q.2 t := by
  have hg := hV.gain_nonneg hs ht.1
  unfold gain at hg
  simp only [objExt, obj, gain]
  rw [posPart_eq (by linarith [ht.1] : 0 ≤ q.2 + t), posPart_eq hs,
    posPart_eq (by linarith [ht.2] : 0 ≤ q.1 - t), posPart_eq hg]

private lemma continuous_objExt (hV : IsValueFn V) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => objExt U V p.1 p.2) := by
  have hVt : Continuous (posPart V) := continuous_posPart hV.continuousOn
  have hut : Continuous (posPart U.u) := continuous_posPart U.continuousOn
  unfold objExt
  fun_prop

/-- Step 3 of `prop:deterministic`: joint continuity of the optimiser on the quadrant. -/
private lemma argmaxFn_continuousOn (hV : IsValueFn V) (hsm : StrictMonoOn V (Ici 0)) :
    ContinuousOn (argmaxFn U hV) (Ici 0 ×ˢ Ici 0) := by
  set Q : Set (ℝ × ℝ) := Ici 0 ×ˢ Ici 0 with hQ_def
  have hF := continuous_objExt U hV
  rintro ⟨b, s⟩ ⟨hb, hs⟩
  have hb : 0 ≤ b := hb
  have hs : 0 ≤ s := hs
  have hspec : argmaxFn U hV (b, s) ∈ Icc 0 b ∧
      obj U.u V b s (argmaxFn U hV (b, s)) = bellH U.u V b s := argmaxFn_spec U hV ⟨hb, hs⟩
  show Tendsto (argmaxFn U hV) (𝓝[Q] (b, s)) (𝓝 (argmaxFn U hV (b, s)))
  refine (isCompact_Icc (a := (0:ℝ)) (b := b + 1)).tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · have h1 : ∀ᶠ q in 𝓝[Q] (b, s), q ∈ Q := self_mem_nhdsWithin
    have h2 : ∀ᶠ q in 𝓝[Q] (b, s), q.1 < b + 1 := nhdsWithin_le_nhds
      ((continuous_fst.tendsto (b, s)).eventually (gt_mem_nhds (by linarith : b < b + 1)))
    filter_upwards [h1, h2] with q hq hq'
    have := (argmaxFn_spec U hV (q := q) ⟨hq.1, hq.2⟩).1
    exact ⟨this.1, this.2.trans hq'.le⟩
  · intro d _ hcl
    have hne : NeBot (comap (argmaxFn U hV) (𝓝 d) ⊓ 𝓝[Q] (b, s)) :=
      neBot_inf_comap_iff_map'.2 (ClusterPt.neBot hcl)
    set 𝓕 := comap (argmaxFn U hV) (𝓝 d) ⊓ 𝓝[Q] (b, s) with h𝓕
    have hq : Tendsto (fun q : ℝ × ℝ => q) 𝓕 (𝓝 (b, s)) :=
      tendsto_id.mono_left (inf_le_right.trans nhdsWithin_le_nhds)
    have hd' : Tendsto (argmaxFn U hV) 𝓕 (𝓝 d) := tendsto_comap.mono_left inf_le_left
    have hQ : ∀ᶠ q in 𝓕, q ∈ Q := mem_inf_of_right self_mem_nhdsWithin
    have hdb : d ∈ Icc 0 b := by
      constructor
      · exact ge_of_tendsto hd' (hQ.mono fun q hq =>
          (argmaxFn_spec U hV (q := q) ⟨hq.1, hq.2⟩).1.1)
      · exact le_of_tendsto_of_tendsto hd' ((continuous_fst.tendsto _).comp hq)
          (hQ.mono fun q hq => (argmaxFn_spec U hV (q := q) ⟨hq.1, hq.2⟩).1.2)
    have hopt : ∀ a ∈ Icc 0 b, obj U.u V b s a ≤ obj U.u V b s d := by
      intro a ha
      have p1 : Tendsto (fun q => (q, argmaxFn U hV q)) 𝓕 (𝓝 ((b, s), d)) :=
        hq.prodMk_nhds hd'
      have t1 : Tendsto (fun q => objExt U V q (argmaxFn U hV q)) 𝓕
          (𝓝 (objExt U V (b, s) d)) := by
        have := (hF.tendsto ((b, s), d)).comp p1
        exact this
      have m2 : Tendsto (fun q : ℝ × ℝ => min a q.1) 𝓕 (𝓝 (min a b)) :=
        ((continuous_const.min continuous_fst).tendsto (b, s)).comp hq
      have p2 : Tendsto (fun q : ℝ × ℝ => (q, min a q.1)) 𝓕 (𝓝 ((b, s), min a b)) :=
        hq.prodMk_nhds m2
      have t2 : Tendsto (fun q : ℝ × ℝ => objExt U V q (min a q.1)) 𝓕
          (𝓝 (objExt U V (b, s) (min a b))) := by
        have := (hF.tendsto ((b, s), min a b)).comp p2
        exact this
      rw [min_eq_left ha.2] at t2
      have key := le_of_tendsto_of_tendsto t2 t1 (hQ.mono fun q hq => by
        have hq' : 0 ≤ q.1 ∧ 0 ≤ q.2 := ⟨hq.1, hq.2⟩
        obtain ⟨hmem, hoptq⟩ := argmaxFn_spec U hV hq'
        have hmin : min a q.1 ∈ Icc 0 q.1 := ⟨le_min ha.1 hq'.1, min_le_right _ _⟩
        show objExt U V q (min a q.1) ≤ objExt U V q (argmaxFn U hV q)
        rw [objExt_eq U hV hq'.2 hmin, objExt_eq U hV hq'.2 hmem, hoptq]
        exact obj_le_bellH U hV hq'.1 hq'.2 hmin)
      rw [objExt_eq U hV (q := (b, s)) hs ha, objExt_eq U hV (q := (b, s)) hs hdb] at key
      exact key
    have hdopt : obj U.u V b s d = bellH U.u V b s := by
      refine le_antisymm (obj_le_bellH U hV hb hs hdb) ?_
      obtain ⟨a, ha, hae⟩ := exists_bellH_eq U hV hb hs
      rw [← hae]
      exact hopt a ha
    exact argmax_unique U hV hsm hb hs hdb hspec.1 hdopt hspec.2

private lemma argmaxFn_measurable (hV : IsValueFn V) (hsm : StrictMonoOn V (Ici 0)) :
    Measurable (argmaxFn U hV) := by
  classical
  set Q : Set (ℝ × ℝ) := Ici 0 ×ˢ Ici 0 with hQ_def
  have hQm : MeasurableSet Q := measurableSet_Ici.prod measurableSet_Ici
  have e : argmaxFn U hV = Q.piecewise (argmaxFn U hV) (fun _ => 0) := by
    funext q
    by_cases hq : q ∈ Q
    · rw [Set.piecewise_eq_of_mem _ _ _ hq]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hq]
      exact argmaxFn_of_not U hV (fun h' => hq ⟨h'.1, h'.2⟩)
  rw [e]
  exact (argmaxFn_continuousOn U hV hsm).measurable_piecewise continuousOn_const hQm

end Helpers

/-- `prop:deterministic`: every equilibrium in the sense of `def:eq` has a strictly increasing
value function; for every `(b, s) ∈ ℝ₊²` the maximum in `eq:HT` has a unique optimiser
`d_V(b,s)`, jointly continuous; and `Γ` is the pushforward of `η ⊗ η` under
`(b,s) ↦ (b, s, d_V(b,s))`. -/
theorem deterministic (U : AdmissibleUtility) {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {V : ℝ → ℝ} {η : Measure ℝ} {Γ : Measure (ℝ × ℝ × ℝ)} (h : IsEquilibrium U.u β M V η Γ) :
    StrictMonoOn V (Ici 0) ∧
    ∃ dV : ℝ × ℝ → ℝ, Measurable dV ∧ ContinuousOn dV (Ici 0 ×ˢ Ici 0) ∧
      (∀ b s, 0 ≤ b → 0 ≤ s → dV (b, s) ∈ Icc 0 b ∧
        ∀ d ∈ Icc 0 b, obj U.u V b s d = bellH U.u V b s ↔ d = dV (b, s)) ∧
      Γ = (η.prod η).map (fun q => (q.1, q.2, dV q)) := by
  have hV := h.value
  have hsm := strictMonoOn_value U hβ0 hβ1 h
  set dV := argmaxFn U hV with hdV
  have hdm : Measurable dV := argmaxFn_measurable U hV hsm
  have hφ : Measurable (fun q : ℝ × ℝ => (q.1, q.2, dV q)) :=
    measurable_fst.prodMk (measurable_snd.prodMk hdm)
  have hpair : Measurable pairBS := by unfold pairBS; fun_prop
  have hae : (id : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) =ᵐ[Γ]
      (fun q : ℝ × ℝ => (q.1, q.2, dV q)) ∘ pairBS := by
    filter_upwards [h.ae_good, h.argmax] with p hp hpa
    have hspec := argmaxFn_spec U hV (q := pairBS p) ⟨hp.1, hp.2.1⟩
    have heq : p.2.2 = dV (pairBS p) :=
      argmax_unique U hV hsm hp.1 hp.2.1 ⟨hp.2.2.1, hp.2.2.2⟩ hspec.1 hpa hspec.2
    exact Prod.ext rfl (Prod.ext rfl heq)
  refine ⟨hsm, dV, hdm, argmaxFn_continuousOn U hV hsm, fun b s hb hs => ?_, ?_⟩
  · have hspec : dV (b, s) ∈ Icc 0 b ∧ obj U.u V b s (dV (b, s)) = bellH U.u V b s :=
      argmaxFn_spec U hV (q := (b, s)) ⟨hb, hs⟩
    refine ⟨hspec.1, fun d hd => ⟨fun hopt => ?_, fun hdeq => ?_⟩⟩
    · exact argmax_unique U hV hsm hb hs hd hspec.1 hopt hspec.2
    · rw [hdeq]; exact hspec.2
  · calc Γ = Γ.map id := Measure.map_id.symm
      _ = Γ.map ((fun q : ℝ × ℝ => (q.1, q.2, dV q)) ∘ pairBS) := Measure.map_congr hae
      _ = (Γ.map pairBS).map (fun q : ℝ × ℝ => (q.1, q.2, dV q)) :=
        (Measure.map_map hφ hpair).symm
      _ = (η.prod η).map (fun q => (q.1, q.2, dV q)) := by rw [h.marginal]

/-- `prop:deterministic`, consequence: every equilibrium is deterministic. -/
theorem IsEquilibrium.isDeterministic (U : AdmissibleUtility) {β M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {V : ℝ → ℝ} {η : Measure ℝ} {Γ : Measure (ℝ × ℝ × ℝ)}
    (h : IsEquilibrium U.u β M V η Γ) : IsDeterministic Γ := by
  obtain ⟨-, dV, hdm, -, -, hΓ⟩ := deterministic U hβ0 hβ1 h
  refine ⟨dV, hdm, ?_⟩
  rw [hΓ, ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) (by fun_prop))]
  exact Eventually.of_forall fun q => rfl

end Molico
