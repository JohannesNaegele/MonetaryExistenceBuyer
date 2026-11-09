import MonetaryExistenceBuyer.Utility
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The buyer-takes-all model: Bellman operator and stationary monetary equilibrium

Formalizes, from `existence-theorem.tex`:

* `def:bellman` — the Bellman operator `H_V`, `T_η V` (`bellH`, `bellT`);
* `def:eq` — stationary monetary equilibrium of mean `M` in relaxed strategies (`IsEquilibrium`),
  and determinism (`IsDeterministic`);
* `rem:norm` — neutrality of money (`IsEquilibrium.rescale`).

A meeting triple `(b, s, d)` is encoded as `p : ℝ × ℝ × ℝ` with `p.1 = b`, `p.2.1 = s`,
`p.2.2 = d`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

/-- The seller's continuation gain `Δ_V(s,d) = V(s+d) - V(s)`. -/
def gain (V : ℝ → ℝ) (s d : ℝ) : ℝ := V (s + d) - V s

/-- The buyer's objective `u(Δ_V(s,d)) + V(m - d)` at buyer wealth `m`, seller wealth `s`,
payment `d`. -/
def obj (u V : ℝ → ℝ) (m s d : ℝ) : ℝ := u (gain V s d) + V (m - d)

/-- `def:bellman`: `H_V(m,s) = sup_{0 ≤ d ≤ m} {u(Δ_V(s,d)) + V(m-d)}`. -/
def bellH (u V : ℝ → ℝ) (m s : ℝ) : ℝ := sSup (obj u V m s '' Icc 0 m)

/-- `def:bellman`: `(T_η V)(m) = β ∫ H_V(m,s) dη(s)`. -/
def bellT (u : ℝ → ℝ) (β : ℝ) (η : Measure ℝ) (V : ℝ → ℝ) (m : ℝ) : ℝ :=
  β * ∫ s, bellH u V m s ∂η

/-- Value functions admitted in `def:eq`: bounded, continuous, increasing and concave on `[0,∞)`,
with `V(0) = 0`. -/
structure IsValueFn (V : ℝ → ℝ) : Prop where
  zero : V 0 = 0
  continuousOn : ContinuousOn V (Ici 0)
  monotoneOn : MonotoneOn V (Ici 0)
  concaveOn : ConcaveOn ℝ (Ici 0) V
  bddAbove : BddAbove (V '' Ici 0)

/-- The set `A = {(b,s,d) : 0 ≤ d ≤ b}` of meeting triples. -/
def meetingSet : Set (ℝ × ℝ × ℝ) := {p | 0 ≤ p.2.2 ∧ p.2.2 ≤ p.1}

/-- Post-trade wealth of the buyer, `B(b,s,d) = b - d`. -/
def postB (p : ℝ × ℝ × ℝ) : ℝ := p.1 - p.2.2

/-- Post-trade wealth of the seller, `S(b,s,d) = s + d`. -/
def postS (p : ℝ × ℝ × ℝ) : ℝ := p.2.1 + p.2.2

/-- The `(b,s)`-projection of a meeting triple. -/
def pairBS (p : ℝ × ℝ × ℝ) : ℝ × ℝ := (p.1, p.2.1)

/-- `def:eq`: a stationary monetary equilibrium of mean `M` in relaxed strategies for the
buyer-takes-all specialization with composite utility `u` and effective discount factor `β`. -/
structure IsEquilibrium (u : ℝ → ℝ) (β M : ℝ) (V : ℝ → ℝ) (η : Measure ℝ)
    (Γ : Measure (ℝ × ℝ × ℝ)) : Prop where
  value : IsValueFn V
  isProb_η : IsProbabilityMeasure η
  /-- `η ∈ 𝒫(ℝ₊)`. -/
  η_nonneg : η (Iio 0) = 0
  isProb_Γ : IsProbabilityMeasure Γ
  /-- `Γ` is a probability measure on `A = {(b,s,d) : 0 ≤ d ≤ b}`. -/
  Γ_meeting : Γ meetingSetᶜ = 0
  /-- (i) `V = T_η V`. -/
  bellman : ∀ m, 0 ≤ m → V m = bellT u β η V m
  /-- (ii) the `(b,s)`-marginal of `Γ` is `η ⊗ η` ... -/
  marginal : Γ.map pairBS = η.prod η
  /-- (ii) ... and `Γ` is concentrated on the argmax set. -/
  argmax : ∀ᵐ p ∂Γ, obj u V p.1 p.2.1 p.2.2 = bellH u V p.1 p.2.1
  /-- (iii) stationarity `η = ½ B_# Γ + ½ S_# Γ`. -/
  stationary : η = (2⁻¹ : ℝ≥0∞) • Γ.map postB + (2⁻¹ : ℝ≥0∞) • Γ.map postS
  /-- (iv) `∫ x dη = M > 0`. -/
  integrable_id : Integrable id η
  mean : ∫ x, x ∂η = M
  mean_pos : 0 < M
  /-- (v) positive monetary trade: `Γ{Δ_V(s,d) > 0} > 0`. -/
  monetary : Γ {p | 0 < gain V p.2.1 p.2.2} ≠ 0

/-- `def:eq`: the equilibrium is deterministic if `Γ` is concentrated on the graph of a
measurable payment rule `d = d_V(b,s)`. -/
def IsDeterministic (Γ : Measure (ℝ × ℝ × ℝ)) : Prop :=
  ∃ dV : ℝ × ℝ → ℝ, Measurable dV ∧ ∀ᵐ p ∂Γ, p.2.2 = dV (p.1, p.2.1)

/-! ### Elementary properties of the Bellman objective -/

section Objective

variable {u V : ℝ → ℝ}

lemma IsValueFn.nonneg (hV : IsValueFn V) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ V x := by
  have := hV.monotoneOn (self_mem_Ici : (0:ℝ) ∈ Ici 0) hx hx
  rwa [hV.zero] at this

lemma IsValueFn.gain_nonneg (hV : IsValueFn V) {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) :
    0 ≤ gain V s d := by
  unfold gain
  have := hV.monotoneOn (show s ∈ Ici (0:ℝ) from hs) (show s + d ∈ Ici (0:ℝ) by
    simp only [mem_Ici]; linarith) (by linarith)
  linarith

/-- Concavity through the origin: `Δ_V(s,d) ≤ V(d)`. -/
lemma IsValueFn.gain_le (hV : IsValueFn V) {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) :
    gain V s d ≤ V d := by
  have := concave_incr_anti hV.concaveOn (le_refl 0) hs hd
  simp only [zero_add, hV.zero, sub_zero] at this
  unfold gain
  rw [add_comm] at this ⊢
  linarith

lemma IsValueFn.le_of_le (hV : IsValueFn V) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    V x ≤ V y := hV.monotoneOn hx (show y ∈ Ici (0:ℝ) from hx.trans hxy) hxy

/-- A uniform upper bound for `V` on `[0,∞)`. -/
def IsValueFn.sup (_hV : IsValueFn V) : ℝ := sSup (V '' Ici 0)

lemma IsValueFn.le_sup (hV : IsValueFn V) {x : ℝ} (hx : 0 ≤ x) : V x ≤ hV.sup :=
  le_csSup hV.bddAbove ⟨x, hx, rfl⟩

lemma IsValueFn.sup_nonneg (hV : IsValueFn V) : 0 ≤ hV.sup :=
  (hV.nonneg le_rfl).trans (hV.le_sup le_rfl)

end Objective

section Bellman

variable (U : AdmissibleUtility) {V : ℝ → ℝ}

lemma obj_le (hV : IsValueFn V) {m s d : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) (hd : d ∈ Icc 0 m) :
    obj U.u V m s d ≤ U.u (V m) + V m := by
  unfold obj
  have h1 : gain V s d ≤ V m := (hV.gain_le hs hd.1).trans (hV.le_of_le hd.1 hd.2)
  have h2 := U.monotoneOn (show gain V s d ∈ Ici (0:ℝ) from hV.gain_nonneg hs hd.1)
    (show V m ∈ Ici (0:ℝ) from hV.nonneg hm) h1
  have h3 : V (m - d) ≤ V m := hV.le_of_le (by linarith [hd.2]) (by linarith [hd.1])
  linarith

lemma bddAbove_obj (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    BddAbove (obj U.u V m s '' Icc 0 m) :=
  ⟨U.u (V m) + V m, by rintro _ ⟨d, hd, rfl⟩; exact obj_le U hV hm hs hd⟩

lemma obj_le_bellH (hV : IsValueFn V) {m s d : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) (hd : d ∈ Icc 0 m) :
    obj U.u V m s d ≤ bellH U.u V m s :=
  le_csSup (bddAbove_obj U hV hm hs) ⟨d, hd, rfl⟩

lemma obj_zero (hV : IsValueFn V) (m s : ℝ) : obj U.u V m s 0 = V m := by
  simp [obj, gain, U.u_zero]

/-- `H_V(m,s) ≥ V(m)` (the transfer `d = 0`). -/
lemma le_bellH (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    V m ≤ bellH U.u V m s := by
  have := obj_le_bellH U hV hm hs (show (0:ℝ) ∈ Icc 0 m from ⟨le_rfl, hm⟩)
  rwa [obj_zero U hV] at this

/-- `H_V(m,s) ≤ u(V(m)) + V(m)` (proof of `lem:gauge`). -/
lemma bellH_le (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    bellH U.u V m s ≤ U.u (V m) + V m :=
  csSup_le (Set.Nonempty.image _ ⟨0, le_rfl, hm⟩) (by rintro _ ⟨d, hd, rfl⟩; exact obj_le U hV hm hs hd)

lemma bellH_nonneg (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    0 ≤ bellH U.u V m s := (hV.nonneg hm).trans (le_bellH U hV hm hs)

lemma bellH_le_const (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    bellH U.u V m s ≤ U.ubar + hV.sup :=
  (bellH_le U hV hm hs).trans (add_le_add (U.le_ubar (hV.nonneg hm)) (hV.le_sup hm))

/-- The maximum in `H_V(m,s)` is attained. -/
lemma exists_bellH_eq (hV : IsValueFn V) {m s : ℝ} (hm : 0 ≤ m) (hs : 0 ≤ s) :
    ∃ d ∈ Icc 0 m, obj U.u V m s d = bellH U.u V m s := by
  have hcont : ContinuousOn (obj U.u V m s) (Icc 0 m) := by
    unfold obj gain
    have h1 : ContinuousOn (fun d => V (s + d)) (Icc 0 m) :=
      hV.continuousOn.comp (continuousOn_const.add continuousOn_id) (fun d hd => by
        simp only [mem_Ici]; linarith [hd.1])
    have h2 : ContinuousOn (fun d => U.u (V (s + d) - V s)) (Icc 0 m) :=
      U.continuousOn.comp (h1.sub continuousOn_const) (fun d hd => by
        have := hV.gain_nonneg hs hd.1; simpa [gain] using this)
    have h3 : ContinuousOn (fun d => V (m - d)) (Icc 0 m) :=
      hV.continuousOn.comp (continuousOn_const.sub continuousOn_id) (fun d hd => by
        simp only [mem_Ici]; linarith [hd.2])
    exact h2.add h3
  obtain ⟨d, hd, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hm⟩ hcont
  refine ⟨d, hd, le_antisymm (obj_le_bellH U hV hm hs hd) ?_⟩
  exact csSup_le (Set.Nonempty.image _ ⟨0, le_rfl, hm⟩) (by
    rintro _ ⟨d', hd', rfl⟩; exact hmax hd')

/-- `H_V(m, ·)` and `T_η V` are monotone in buyer wealth. -/
lemma bellH_mono (hV : IsValueFn V) {m m' s : ℝ} (hm : 0 ≤ m) (hmm' : m ≤ m') (hs : 0 ≤ s) :
    bellH U.u V m s ≤ bellH U.u V m' s := by
  obtain ⟨d, hd, hdeq⟩ := exists_bellH_eq U hV hm hs
  rw [← hdeq]
  refine le_trans ?_ (obj_le_bellH U hV (hm.trans hmm') hs ⟨hd.1, hd.2.trans hmm'⟩)
  unfold obj
  have := hV.le_of_le (show 0 ≤ m - d by linarith [hd.2]) (show m - d ≤ m' - d by linarith)
  linarith

end Bellman

/-! ### Measurability of the Bellman objective on the quadrant -/

section Measurability

variable (U : AdmissibleUtility) {V : ℝ → ℝ}

/-- Extension of a function on `[0,∞)` that is constant on `(-∞,0]`. -/
def posPart (f : ℝ → ℝ) (x : ℝ) : ℝ := f (max x 0)

lemma continuous_posPart {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) : Continuous (posPart f) :=
  hf.comp_continuous (continuous_id.max continuous_const) (fun x => le_max_right x 0)

/-- On the closed quadrant, `H_V` agrees with a jointly continuous function. -/
lemma posPart_eq {f : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x) : posPart f x = f x := by
  simp [posPart, max_eq_left hx]

lemma IsValueFn.posPart_nonneg (hV : IsValueFn V) (x : ℝ) : 0 ≤ posPart V x :=
  hV.nonneg (le_max_right x 0)

lemma IsValueFn.posPart_le (hV : IsValueFn V) (x : ℝ) : posPart V x ≤ hV.sup :=
  hV.le_sup (le_max_right x 0)

lemma posPart_u_nonneg (x : ℝ) : 0 ≤ posPart U.u x := U.nonneg (le_max_right x 0)

lemma posPart_u_le (x : ℝ) : posPart U.u x ≤ U.ubar := U.le_ubar (le_max_right x 0)

lemma exists_continuous_bellH (hV : IsValueFn V) :
    ∃ G : ℝ × ℝ → ℝ, Continuous G ∧ (∀ q, 0 ≤ G q ∧ G q ≤ U.ubar + hV.sup) ∧
      ∀ m s, 0 ≤ m → 0 ≤ s → G (m, s) = bellH U.u V m s := by
  set Vt := posPart V
  set ut := posPart U.u
  have hVt : Continuous Vt := continuous_posPart hV.continuousOn
  have hut : Continuous ut := continuous_posPart U.continuousOn
  let F : ℝ × ℝ → ℝ → ℝ := fun q t =>
    ut (Vt (q.2 + t * max q.1 0) - Vt q.2) + Vt (max q.1 0 - t * max q.1 0)
  have hF : Continuous ↿F := by
    simp only [F]
    fun_prop
  have hFb : ∀ q t, 0 ≤ F q t ∧ F q t ≤ U.ubar + hV.sup := fun q t =>
    ⟨add_nonneg (posPart_u_nonneg U _) (hV.posPart_nonneg _),
      add_le_add (posPart_u_le U _) (hV.posPart_le _)⟩
  have hne : ∀ q, (F q '' Icc 0 1).Nonempty := fun q => Set.Nonempty.image _ ⟨0, le_rfl, zero_le_one⟩
  refine ⟨fun q => sSup (F q '' Icc 0 1), isCompact_Icc.continuous_sSup hF, fun q => ⟨?_, ?_⟩, ?_⟩
  · exact le_csSup_of_le ⟨U.ubar + hV.sup, by rintro _ ⟨t, -, rfl⟩; exact (hFb q t).2⟩
      ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ (hFb q 0).1
  · exact csSup_le (hne q) (by rintro _ ⟨t, -, rfl⟩; exact (hFb q t).2)
  intro m s hm hs
  simp only
  congr 1
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * m, ⟨mul_nonneg ht.1 hm, by nlinarith [ht.2]⟩, ?_⟩
    simp only [F, obj, gain, Vt, ut, posPart, max_eq_left hm]
    have h1 : 0 ≤ s + t * m := by nlinarith [ht.1]
    have h2 : 0 ≤ m - t * m := by nlinarith [ht.2]
    have h3 : 0 ≤ V (s + t * m) - V s :=
      hV.gain_nonneg hs (mul_nonneg ht.1 hm)
    rw [max_eq_left h1, max_eq_left hs, max_eq_left h2, max_eq_left h3]
  · rintro ⟨d, hd, rfl⟩
    rcases hm.eq_or_lt with rfl | hm'
    · have hd0 : d = 0 := le_antisymm hd.2 hd.1
      subst hd0
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      simp [F, obj, gain, Vt, ut, posPart, max_eq_left hs]
    · refine ⟨d / m, ⟨div_nonneg hd.1 hm, (div_le_one hm').mpr hd.2⟩, ?_⟩
      have hdm : d / m * m = d := by field_simp
      simp only [F, obj, gain, Vt, ut, posPart, max_eq_left hm, hdm]
      have h1 : 0 ≤ s + d := by linarith [hd.1]
      have h2 : 0 ≤ m - d := by linarith [hd.2]
      have h3 : 0 ≤ V (s + d) - V s := hV.gain_nonneg hs hd.1
      rw [max_eq_left h1, max_eq_left hs, max_eq_left h2, max_eq_left h3]

end Measurability

/-! ### Neutrality of money (`rem:norm`) -/

/-- Rescaling of the Bellman objective: `obj` for `m ↦ V(c m)` is `obj` for `V` at scaled
arguments. -/
lemma obj_comp_mul (u V : ℝ → ℝ) (c m s d : ℝ) :
    obj u (fun x => V (c * x)) m s d = obj u V (c * m) (c * s) (c * d) := by
  simp only [obj, gain, mul_add, mul_sub]

lemma gain_comp_mul (V : ℝ → ℝ) (c s d : ℝ) :
    gain (fun x => V (c * x)) s d = gain V (c * s) (c * d) := by
  simp only [gain, mul_add]

/-- Rescaling of the Bellman operator `H_V`. -/
lemma bellH_comp_mul (u V : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (m s : ℝ) :
    bellH u (fun x => V (c * x)) m s = bellH u V (c * m) (c * s) := by
  unfold bellH
  congr 1
  ext y
  simp only [mem_image, mem_Icc, obj_comp_mul]
  constructor
  · rintro ⟨d, ⟨hd0, hdm⟩, rfl⟩
    exact ⟨c * d, ⟨mul_nonneg hc.le hd0, mul_le_mul_of_nonneg_left hdm hc.le⟩, rfl⟩
  · rintro ⟨d, ⟨hd0, hdm⟩, rfl⟩
    refine ⟨d / c, ⟨div_nonneg hd0 hc.le, (div_le_iff₀' hc).2 hdm⟩, ?_⟩
    rw [mul_div_cancel₀ d hc.ne']

/-- `rem:norm`: if `(V, η, Γ)` is an equilibrium of mean `M` and `λ > 0`, then
`Ṽ(m) = V(λ m)` with the pushforwards of `η, Γ` under division by `λ` is an equilibrium of
mean `M/λ`. -/
theorem IsEquilibrium.rescale {u : ℝ → ℝ} {β M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ}
    {Γ : Measure (ℝ × ℝ × ℝ)} (h : IsEquilibrium u β M V η Γ) {c : ℝ} (hc : 0 < c) :
    IsEquilibrium u β (M / c) (fun m => V (c * m)) (η.map fun x => x / c)
      (Γ.map fun p => (p.1 / c, p.2.1 / c, p.2.2 / c)) := by
  have hc' : c ≠ 0 := hc.ne'
  set f : ℝ → ℝ := fun x => x / c
  set g : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p => (p.1 / c, p.2.1 / c, p.2.2 / c)
  have hfe : MeasurableEmbedding f := by
    have := measurableEmbedding_mulRight₀ (inv_ne_zero hc')
    simpa only [← div_eq_mul_inv] using this
  have hge : MeasurableEmbedding g := hfe.prodMap (hfe.prodMap hfe)
  have hf : Measurable f := hfe.measurable
  have hg : Measurable g := hge.measurable
  have hcf : ∀ x, c * (x / c) = x := fun x => mul_div_cancel₀ x hc'
  have hcf' : ∀ x, c * f x = x := hcf
  have mB : Measurable postB := by unfold postB; fun_prop
  have mS : Measurable postS := by unfold postS; fun_prop
  have mP : Measurable pairBS := by unfold pairBS; fun_prop
  have := h.isProb_η
  have := h.isProb_Γ
  refine
    { value := ?_
      isProb_η := inferInstance
      η_nonneg := ?_
      isProb_Γ := inferInstance
      Γ_meeting := ?_
      bellman := ?_
      marginal := ?_
      argmax := ?_
      stationary := ?_
      integrable_id := ?_
      mean := ?_
      mean_pos := div_pos h.mean_pos hc
      monetary := ?_ }
  · -- value function
    have hV := h.value
    have hmem : ∀ x : ℝ, x ∈ Ici (0:ℝ) → c * x ∈ Ici (0:ℝ) := fun x hx =>
      mul_nonneg hc.le hx
    refine ⟨by simp [hV.zero], ?_, ?_, ?_, ?_⟩
    · exact hV.continuousOn.comp (continuousOn_const.mul continuousOn_id) hmem
    · intro a ha b hb hab
      exact hV.monotoneOn (hmem a ha) (hmem b hb) (mul_le_mul_of_nonneg_left hab hc.le)
    · refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
      have := hV.concaveOn.2 (hmem x hx) (hmem y hy) ha hb hab
      simp only [smul_eq_mul] at this ⊢
      convert this using 2
      ring
    · exact hV.bddAbove.mono (by rintro _ ⟨m, hm, rfl⟩; exact ⟨c * m, hmem m hm, rfl⟩)
  · -- η̃ (Iio 0) = 0
    rw [hfe.map_apply]
    convert h.η_nonneg using 2
    ext x
    simp only [mem_preimage, mem_Iio, f]
    rw [div_lt_iff₀ hc, zero_mul]
  · -- Γ̃ meetingSetᶜ = 0
    rw [hge.map_apply]
    convert h.Γ_meeting using 2
    ext p
    simp only [mem_preimage, mem_compl_iff, meetingSet, mem_ofPred_eq, g]
    rw [le_div_iff₀ hc, zero_mul, div_le_div_iff_of_pos_right hc]
  · -- Bellman equation
    intro m hm
    simp only [bellT]
    rw [hfe.integral_map]
    simp only [bellH_comp_mul u V hc, hcf']
    exact h.bellman (c * m) (mul_nonneg hc.le hm)
  · -- marginal
    rw [Measure.map_map mP hg]
    have e : pairBS ∘ g = Prod.map f f ∘ pairBS := rfl
    rw [e, ← Measure.map_map (hf.prodMap hf) mP, h.marginal, Measure.map_prod_map _ _ hf hf]
  · -- argmax
    rw [hge.ae_map_iff]
    filter_upwards [h.argmax] with p hp
    simp only [g, obj_comp_mul, bellH_comp_mul u V hc, hcf]
    exact hp
  · -- stationarity
    have eB : (Γ.map postB).map f = (Γ.map g).map postB := by
      rw [Measure.map_map hf mB, Measure.map_map mB hg]
      congr 1
      funext p
      simp only [Function.comp, postB, f, g, sub_div]
    have eS : (Γ.map postS).map f = (Γ.map g).map postS := by
      rw [Measure.map_map hf mS, Measure.map_map mS hg]
      congr 1
      funext p
      simp only [Function.comp, postS, f, g, add_div]
    conv_lhs => rw [h.stationary]
    rw [Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable,
      Measure.map_smul _ hf.aemeasurable, eB, eS]
  · -- integrability
    rw [hfe.integrable_map_iff]
    exact h.integrable_id.div_const c
  · -- mean
    rw [hfe.integral_map]
    simp only [f]
    rw [integral_div, h.mean]
  · -- monetary trade
    rw [hge.map_apply]
    convert h.monetary using 2
    ext p
    simp only [mem_preimage, mem_ofPred_eq, g, gain_comp_mul, hcf]

end Molico
