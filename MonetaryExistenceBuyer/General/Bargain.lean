import MonetaryExistenceBuyer.General.Composite

/-!
# Buyer-takes-all bargaining (`lem:buyerreduction`)

For `θ = 1`, the bargaining maximisers at `(b, s)` are exactly the trades
`(K⁻¹(Δ_V(s,d)), d)` with `d` a maximiser of the buyer problem `H_V(b,s)` of `def:bellman`
(for the composite utility `u = U ∘ K⁻¹`): the buyer receives `H_V(b,s)`, the seller `V(s)`.
Hence the general Bellman equation `eq:generalbellman` reduces to `V = T_η V` (`eq:buyerflow`).
-/

open Set Filter Topology MeasureTheory ProbabilityTheory

noncomputable section

namespace Molico.Environment

variable (E : Environment)

/-- The buyer's objective is bounded by `u(V(m)) + V(m)`. -/
private lemma obj_u_le {V : ℝ → ℝ} (hV : IsValueFn V) {m s d : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hd : d ∈ Icc 0 m) : obj E.u V m s d ≤ E.u (V m) + V m := by
  unfold obj
  have h1 : gain V s d ≤ V m := (hV.gain_le hs hd.1).trans (hV.le_of_le hd.1 hd.2)
  have h2 := E.u_monotoneOn (show gain V s d ∈ Ici (0:ℝ) from hV.gain_nonneg hs hd.1)
    (show V m ∈ Ici (0:ℝ) from hV.nonneg hm) h1
  have h3 : V (m - d) ≤ V m := hV.le_of_le (by linarith [hd.2]) (by linarith [hd.1])
  linarith

theorem bddAbove_obj_u {V : ℝ → ℝ} (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    BddAbove (obj E.u V m s '' Icc 0 m) :=
  ⟨E.u (V m) + V m, by rintro _ ⟨d, hd, rfl⟩; exact E.obj_u_le hV hm hs hd⟩

theorem obj_le_bellH_u {V : ℝ → ℝ} (hV : IsValueFn V) {m s d : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s)
    (hd : d ∈ Icc 0 m) : obj E.u V m s d ≤ bellH E.u V m s :=
  le_csSup (E.bddAbove_obj_u hV hm hs) ⟨d, hd, rfl⟩

theorem le_bellH_u {V : ℝ → ℝ} (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    V m ≤ bellH E.u V m s := by
  have := E.obj_le_bellH_u hV hm hs (show (0:ℝ) ∈ Icc 0 m from ⟨le_rfl, hm⟩)
  simpa [obj, gain, E.u_zero] using this

private lemma bellH_u_le {V : ℝ → ℝ} (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    bellH E.u V m s ≤ E.u (V m) + V m :=
  csSup_le (Set.Nonempty.image _ ⟨0, le_rfl, hm⟩)
    (by rintro _ ⟨d, hd, rfl⟩; exact E.obj_u_le hV hm hs hd)

/-- `H_V(m, ·)` is antitone on `[0, ∞)` (concavity of `V`, monotonicity of `u`). -/
private lemma bellH_u_anti {V : ℝ → ℝ} (hV : IsValueFn V) {m s s' : ℝ} (hm : 0 ≤ m)
    (hs : 0 ≤ s) (hss' : s ≤ s') : bellH E.u V m s' ≤ bellH E.u V m s := by
  refine csSup_le (Set.Nonempty.image _ ⟨0, le_rfl, hm⟩) ?_
  rintro _ ⟨d, hd, rfl⟩
  refine le_trans ?_ (E.obj_le_bellH_u hV hm hs hd)
  unfold obj
  have h1 : gain V s' d ≤ gain V s d := concave_incr_anti hV.concaveOn hs hss' hd.1
  have h2 := E.u_monotoneOn
    (show gain V s' d ∈ Ici (0:ℝ) from hV.gain_nonneg (hs.trans hss') hd.1)
    (show gain V s d ∈ Ici (0:ℝ) from hV.gain_nonneg hs hd.1) h1
  linarith

/-- For `θ = 1` the Nash product is the buyer's surplus. -/
private lemma nash_one (T : ThreatRule) (V : ℝ → ℝ) (b s : ℝ) (y : ℝ × ℝ) :
    E.nash 1 T V b s y = E.Jb V b s y.1 y.2 - T.Tb b s := by
  simp [nash]

/-- The trade `(K⁻¹(Δ_V(s,d)), d)` is feasible as soon as the buyer is not worse off. -/
private lemma mk_mem_feasibleSet {V : ℝ → ℝ} (hV : IsValueFn V) {b s d : ℝ} (hs : 0 ≤ s)
    (hd : d ∈ Icc 0 b) (hobj : V b ≤ obj E.u V b s d) :
    (E.Kinv (gain V s d), d) ∈ E.feasibleSet V b s := by
  have hg0 : 0 ≤ gain V s d := hV.gain_nonneg hs hd.1
  refine ⟨E.Kinv_mem hg0, hd.1, hd.2, hobj, ?_⟩
  show V s ≤ -E.K (E.Kinv (gain V s d)) + V (s + d)
  rw [E.K_Kinv hg0]
  unfold gain
  linarith

/-- For `θ = 1` the buyer's payoff at every bargaining maximiser is `H_V(b,s)`. -/
theorem Jb_eq_bellH (T : ThreatRule) {V : ℝ → ℝ} (hV : IsValueFn V) {b s : ℝ} (hb : 0 ≤ b)
    (hs : 0 ≤ s) {x : ℝ × ℝ} (hx : x ∈ E.bargainSet 1 T V b s) :
    E.Jb V b s x.1 x.2 = bellH E.u V b s := by
  have hbind := E.buyerreduction_binding T hx
  obtain ⟨⟨hQ, hd0, hdb, hB, -⟩, hmax⟩ := hx
  have hq : E.Kinv (gain V s x.2) = x.1 := by
    rw [gain, ← hbind, E.Kinv_K hQ]
  have hJ : E.Jb V b s x.1 x.2 = obj E.u V b s x.2 := by
    rw [obj, Environment.u, hq]; rfl
  refine le_antisymm (hJ ▸ E.obj_le_bellH_u hV hb hs ⟨hd0, hdb⟩) ?_
  refine csSup_le (Set.Nonempty.image _ ⟨0, le_rfl, hb⟩) ?_
  rintro _ ⟨d, hd, rfl⟩
  by_cases h : V b ≤ obj E.u V b s d
  · have := hmax _ (E.mk_mem_feasibleSet hV hs hd h)
    rw [E.nash_one, E.nash_one] at this
    have e : E.Jb V b s (E.Kinv (gain V s d), d).1 (E.Kinv (gain V s d), d).2 =
        obj E.u V b s d := rfl
    linarith
  · rw [not_le] at h
    linarith

/-- For `θ = 1` the seller's payoff at every bargaining maximiser is `V(s)` (zero surplus). -/
theorem Js_eq (T : ThreatRule) {V : ℝ → ℝ} {b s : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ E.bargainSet 1 T V b s) : E.Js V b s x.1 x.2 = V s := by
  rw [Js, E.buyerreduction_binding T hx]
  ring

/-- Every maximiser `d` of the buyer problem yields the bargaining maximiser
`(K⁻¹(Δ_V(s,d)), d)`. -/
theorem mem_bargainSet_of_argmax (T : ThreatRule) {V : ℝ → ℝ} (hV : IsValueFn V) {b s d : ℝ}
    (hb : 0 ≤ b) (hs : 0 ≤ s) (hd : d ∈ Icc 0 b) (hmax : obj E.u V b s d = bellH E.u V b s) :
    (E.Kinv (gain V s d), d) ∈ E.bargainSet 1 T V b s := by
  refine ⟨E.mk_mem_feasibleSet hV hs hd ((E.le_bellH_u hV hb hs).trans_eq hmax.symm),
    fun y hy => ?_⟩
  rw [E.nash_one, E.nash_one]
  obtain ⟨hQ, hd0, hdb, -, hS⟩ := hy
  have hK : E.K y.1 ≤ gain V s y.2 := by
    simp only [Js] at hS; unfold gain; linarith
  have hU := E.U_le_u hQ (hV.gain_nonneg hs hd0) hK
  have h1 := E.obj_le_bellH_u hV hb hs ⟨hd0, hdb⟩
  have e : E.Jb V b s (E.Kinv (gain V s d), d).1 (E.Kinv (gain V s d), d).2 =
      obj E.u V b s d := rfl
  rw [e, hmax]
  simp only [Jb]
  simp only [obj] at h1
  linarith

private lemma ae_nonneg {η : Measure ℝ} (hη : η (Iio 0) = 0) : ∀ᵐ s ∂η, 0 ≤ s := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hη] with s hs
  simpa using hs

/-- `s ↦ H_V(m,s)` is integrable against a probability law on `[0, ∞)`. -/
private lemma integrable_bellH_u {V : ℝ → ℝ} (hV : IsValueFn V) {η : Measure ℝ}
    [IsProbabilityMeasure η] (hη : η (Iio 0) = 0) {m : ℝ} (hm : 0 ≤ m) :
    Integrable (fun s => bellH E.u V m s) η := by
  have hae := ae_nonneg hη
  have hanti : Antitone fun s : ℝ => bellH E.u V m (max s 0) := fun s s' hss' =>
    E.bellH_u_anti hV hm (le_max_right s 0) (max_le_max hss' le_rfl)
  refine Integrable.of_bound ?_ (E.u (V m) + V m) ?_
  · refine hanti.measurable.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with s hs
    rw [max_eq_left hs]
  · filter_upwards [hae] with s hs
    have h0 := (hV.nonneg hm).trans (E.le_bellH_u hV hm hs)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact E.bellH_u_le hV hm hs

/-- The buyer-side integral in `eq:generalbellman` exists for `θ = 1`: its integrand is `η`-a.e.
equal to `H_V(m,s) - V(m)` (`Jb_eq_bellH`), which is bounded. -/
theorem buyerreduction_integrable_b (T : ThreatRule) {V : ℝ → ℝ} (hV : IsValueFn V)
    {η : Measure ℝ} [IsProbabilityMeasure η] (hη : η (Iio 0) = 0) {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    [IsMarkovKernel κ] (hsupp : ∀ b s, 0 ≤ b → 0 ≤ s → κ (b, s) (E.bargainSet 1 T V b s)ᶜ = 0)
    {m : ℝ} (hm : 0 ≤ m) :
    Integrable (fun s => ∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) η := by
  refine ((E.integrable_bellH_u hV hη hm).sub (integrable_const (V m))).congr ?_
  filter_upwards [ae_nonneg hη] with s hs
  have hmem : ∀ᵐ x ∂κ (m, s), x ∈ E.bargainSet 1 T V m s := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hsupp m s hm hs)] with x hx
    simpa using hx
  show bellH E.u V m s - V m = ∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)
  calc bellH E.u V m s - V m = ∫ _x, (bellH E.u V m s - V m) ∂κ (m, s) := by simp
    _ = ∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s) := by
        refine integral_congr_ae ?_
        filter_upwards [hmem] with x hx
        rw [E.Jb_eq_bellH T hV hm hs hx]

/-- The seller-side integral in `eq:generalbellman` exists for `θ = 1`: its integrand vanishes
on the bargaining set (`Js_eq`). -/
theorem buyerreduction_integrable_s (T : ThreatRule) {V : ℝ → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] (hη : η (Iio 0) = 0) {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    [IsMarkovKernel κ] (hsupp : ∀ b s, 0 ≤ b → 0 ≤ s → κ (b, s) (E.bargainSet 1 T V b s)ᶜ = 0)
    {m : ℝ} (hm : 0 ≤ m) :
    Integrable (fun b => ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) η := by
  refine (integrable_const (0 : ℝ)).congr ?_
  filter_upwards [ae_nonneg hη] with b hb
  have hmem : ∀ᵐ x ∂κ (b, m), x ∈ E.bargainSet 1 T V b m := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hsupp b m hb hm)] with x hx
    simpa using hx
  show (0 : ℝ) = ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)
  calc (0 : ℝ) = ∫ _x, (0 : ℝ) ∂κ (b, m) := (integral_zero _ _).symm
    _ = ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m) := by
        refine integral_congr_ae ?_
        filter_upwards [hmem] with x hx
        rw [E.Js_eq T hx, sub_self]

/-- `lem:buyerreduction`, eq. `eq:buyerflow`: for `θ = 1` and increasing `V` (here: an
admissible value function, `IsValueFn`) the general Bellman equation is equivalent to the
buyer's Bellman equation `r V(m) = π [∫ H_V(m,s) dη(s) - V(m)]` with the composite utility, i.e.
to `V = T_η V` with `β = π/(r+π)` (`rem:buyertakesall`). -/
theorem buyerreduction_bellman (T : ThreatRule) {V : ℝ → ℝ} (hV : IsValueFn V)
    {η : Measure ℝ} [IsProbabilityMeasure η] (hη : η (Iio 0) = 0) {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    [IsMarkovKernel κ] (hsupp : ∀ b s, 0 ≤ b → 0 ≤ s → κ (b, s) (E.bargainSet 1 T V b s)ᶜ = 0)
    {m : ℝ} (hm : 0 ≤ m) :
    (E.r * V m = E.π * ∫ s, (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η +
      E.π * ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η) ↔
    V m = bellT E.u E.β η V m := by
  have hae := ae_nonneg hη
  have hmem : ∀ b s, 0 ≤ b → 0 ≤ s → ∀ᵐ x ∂κ (b, s), x ∈ E.bargainSet 1 T V b s := by
    intro b s hb hs
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hsupp b s hb hs)] with x hx
    simpa using hx
  have h1 : ∫ s, (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η =
      ∫ s, (bellH E.u V m s - V m) ∂η := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with s hs
    calc ∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)
        = ∫ _x, (bellH E.u V m s - V m) ∂κ (m, s) := by
          refine integral_congr_ae ?_
          filter_upwards [hmem m s hm hs] with x hx
          rw [E.Jb_eq_bellH T hV hm hs hx]
      _ = bellH E.u V m s - V m := by simp
  have h2 : ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η = 0 := by
    calc ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η
        = ∫ _b, (0:ℝ) ∂η := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with b hb
          calc ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)
              = ∫ _x, (0:ℝ) ∂κ (b, m) := by
                refine integral_congr_ae ?_
                filter_upwards [hmem b m hb hm] with x hx
                rw [E.Js_eq T hx, sub_self]
            _ = 0 := integral_zero _ _
      _ = 0 := integral_zero _ _
  rw [h1, h2, integral_sub (E.integrable_bellH_u hV hη hm) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero]
  unfold bellT Environment.β
  have hpos : 0 < E.r + E.π := by linarith [E.r_pos, E.π_pos]
  rw [div_mul_eq_mul_div, eq_div_iff hpos.ne']
  constructor <;> intro h <;> linear_combination h

end Molico.Environment
