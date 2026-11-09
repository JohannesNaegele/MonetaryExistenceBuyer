import MonetaryExistenceBuyer.General.ValueBound
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Nonexistence for general bargaining power (`prop:necessity`)

Under `ass:utility` on the composite utility `u = U ∘ K⁻¹`, a stationary monetary equilibrium in
the sense of `def:generaleq` with bargaining power `θ ∈ [0,1]` and any admissible threat-point rule
can exist only if `c₀ > 1 + σ` and `θ c₀ > σ` (`eq:generalnecessary`), where `σ = r/π`
(`def:effectivediscount`). In particular, no monetary equilibrium exists when the sellers have
all the bargaining power (`θ = 0`), and for `θ = 1` the conditions reduce to `β c₀ > 1`.

The proof follows the manuscript. `step:necessity:stationarity` averages the Bellman equation
`eq:generalbellman` over the stationary law `η`; the continuation-value changes cancel by
stationarity `eq:generalstationarity`, leaving `σ v̄ = ∫ [u(z) - z] dΞ` with `z = K(q)`, and the
strict concavity `u(z) < c₀ z` on `{z > 0}` gives `c₀ > 1 + σ`. `step:necessity:bargaining` bounds
the buyer's gain by `eq:buyersurplusbound` at every bargaining maximiser (a first-order condition
of the Nash product in the production cost), averages it over the buyer's meetings with Jensen's
inequality, and evaluates the resulting bound along wealth levels whose value approaches the
`η`-essential supremum `L` of `V`.

Measurability: `U` and `K` are only continuous on `[0, q̄)` and `V` only on `[0, ∞)`, so the
integrands are written with the measurable modifications `Ut`, `Kt` (extended by `0` outside
`[0, q̄)`) and `posPart V`; they agree with the original functions on the set of meetings of full
`Ξ`-measure.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Molico.Environment

variable {E : Environment}

/-! ### Measurable modifications of the technology -/

theorem measurableSet_Q (E : Environment) : MeasurableSet E.Q := by
  have : E.Q = {q | 0 ≤ q} ∩ {q | ENNReal.ofReal q < E.qbar} := rfl
  rw [this]
  exact (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

private lemma zero_mem_Q (E : Environment) : (0 : ℝ) ∈ E.Q := ⟨le_rfl, by simpa using E.qbar_pos⟩

theorem K_pos {q : ℝ} (hq : q ∈ E.Q) (h0 : 0 < q) : 0 < E.K q := by
  have := E.K_strictMono E.zero_mem_Q hq h0
  rwa [E.K_zero] at this

open Classical in
/-- The cost function on `[0, q̄)`, extended by `0`: a measurable version of `K`. -/
def Kt (E : Environment) : ℝ → ℝ := E.Q.piecewise E.K 0

open Classical in
/-- The utility of consumption on `[0, q̄)`, extended by `0`: a measurable version of `U`. -/
def Ut (E : Environment) : ℝ → ℝ := E.Q.piecewise E.U 0

open Classical in
theorem Kt_eq {q : ℝ} (hq : q ∈ E.Q) : E.Kt q = E.K q := by
  unfold Kt; exact Set.piecewise_eq_of_mem _ _ _ hq

open Classical in
theorem Ut_eq {q : ℝ} (hq : q ∈ E.Q) : E.Ut q = E.U q := by
  unfold Ut; exact Set.piecewise_eq_of_mem _ _ _ hq

open Classical in
theorem measurable_Kt (E : Environment) : Measurable E.Kt := by
  unfold Kt
  convert E.K_cont.measurable_piecewise (g := 0) continuousOn_const E.measurableSet_Q
  all_goals rfl

open Classical in
theorem measurable_Ut (E : Environment) : Measurable E.Ut := by
  unfold Ut
  convert E.U_cont.measurable_piecewise (g := 0) continuousOn_const E.measurableSet_Q
  all_goals rfl

/-- `U(q) = u(K(q))` on `[0, q̄)` (`def:compositeutility`). -/
theorem U_eq_u_K (U : AdmissibleUtility) (hu : U.u = E.u) {q : ℝ} (hq : q ∈ E.Q) :
    E.U q = U.u (E.K q) := by
  rw [hu]; show E.U q = E.U (E.Kinv (E.K q)); rw [E.Kinv_K hq]

theorem U_Kinv (U : AdmissibleUtility) (hu : U.u = E.u) (x : ℝ) : E.U (E.Kinv x) = U.u x := by
  rw [hu]; rfl

/-! ### The essential supremum of the value function -/

/-- The `η`-essential supremum of `V`, defined as the infimum of its `η`-a.e. upper bounds
(`L = sup_{supp η} V` in `step:necessity:bargaining`). -/
def essBound (V : ℝ → ℝ) (η : Measure ℝ) : ℝ := sInf {c : ℝ | ∀ᵐ m ∂η, V m ≤ c}

section essBound

variable {V : ℝ → ℝ} {η : Measure ℝ}

lemma essBound_bddBelow [NeZero η] (hV0 : ∀ᵐ m ∂η, 0 ≤ V m) :
    BddBelow {c : ℝ | ∀ᵐ m ∂η, V m ≤ c} := by
  refine ⟨0, fun c hc => ?_⟩
  obtain ⟨m, hm1, hm2⟩ := (hV0.and hc).exists
  exact hm1.trans hm2

/-- `V ≤ L` holds `η`-almost everywhere, as soon as `V` has some `η`-a.e. upper bound. -/
lemma ae_le_essBound {C : ℝ} (hC : ∀ᵐ m ∂η, V m ≤ C) :
    ∀ᵐ m ∂η, V m ≤ essBound V η := by
  have hne : ({c : ℝ | ∀ᵐ m ∂η, V m ≤ c}).Nonempty := ⟨C, hC⟩
  have h : ∀ n : ℕ, ∀ᵐ m ∂η, V m ≤ essBound V η + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨c, hc, hlt⟩ := exists_lt_of_csInf_lt hne
      (show essBound V η < essBound V η + 1 / ((n : ℝ) + 1) by linarith)
    filter_upwards [hc] with m hm
    exact hm.trans hlt.le
  rw [← ae_all_iff] at h
  filter_upwards [h] with m hm
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact (hm n).trans_lt (by linarith)

/-- Every set of full `η`-measure contains points whose value is arbitrarily close to `L`. -/
lemma exists_essBound_sub_lt [NeZero η] (hV0 : ∀ᵐ m ∂η, 0 ≤ V m) {S : Set ℝ}
    (hS : ∀ᵐ m ∂η, m ∈ S)
    {ε : ℝ} (hε : 0 < ε) : ∃ m ∈ S, essBound V η - ε < V m := by
  by_contra hcon
  push Not at hcon
  have hmem : essBound V η - ε ∈ {c : ℝ | ∀ᵐ m ∂η, V m ≤ c} := by
    filter_upwards [hS] with m hm
    exact hcon m hm
  have := csInf_le (essBound_bddBelow hV0) hmem
  unfold essBound at this
  linarith

end essBound

/-! ### The buyer-surplus bound at a bargaining maximiser (`eq:buyersurplusbound`) -/

/-- First-order inequality of the Nash product: if lowering the buyer's payoff by `δ` while raising
the seller's by `ε` does not increase `(B - δ)^θ (A + ε)^(1-θ)`, then
`(1-θ) ε (B - δ) ≤ θ δ (A + ε)` (by taking logarithms and using `log x ≤ x - 1`). -/
private lemma nash_foc_aux {θ A B δ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hδ : δ < B)
    (hle : (B - δ) ^ θ * (A + ε) ^ (1 - θ) ≤ B ^ θ * A ^ (1 - θ)) :
    (1 - θ) * ε * (B - δ) ≤ θ * δ * (A + ε) := by
  have hθ1' : 0 < 1 - θ := sub_pos.2 hθ1
  have hBδ : 0 < B - δ := sub_pos.2 hδ
  have hAε : 0 < A + ε := by linarith
  have hlog := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos hBδ _) (Real.rpow_pos_of_pos hAε _)) hle
  rw [Real.log_mul (Real.rpow_pos_of_pos hBδ _).ne' (Real.rpow_pos_of_pos hAε _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hB _).ne' (Real.rpow_pos_of_pos hA _).ne',
    Real.log_rpow hBδ, Real.log_rpow hAε, Real.log_rpow hB, Real.log_rpow hA] at hlog
  -- `log (A+ε) - log A ≥ ε/(A+ε)` and `log B - log (B-δ) ≤ δ/(B-δ)`
  have h1 : ε / (A + ε) ≤ Real.log (A + ε) - Real.log A := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hAε hA)
    rw [Real.log_div hAε.ne' hA.ne', inv_div] at this
    have e : 1 - A / (A + ε) = ε / (A + ε) := by field_simp; ring
    rwa [e] at this
  have h2 : Real.log B - Real.log (B - δ) ≤ δ / (B - δ) := by
    have := Real.log_le_sub_one_of_pos (div_pos hB hBδ)
    rw [Real.log_div hB.ne' hBδ.ne'] at this
    have e : B / (B - δ) - 1 = δ / (B - δ) := by field_simp; ring
    rwa [e] at this
  have h3 : (1 - θ) * (ε / (A + ε)) ≤ θ * (δ / (B - δ)) := by
    linarith [mul_le_mul_of_nonneg_left h1 hθ1'.le, mul_le_mul_of_nonneg_left h2 hθ0.le]
  rwa [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hAε hBδ] at h3

/-- Dividing the first-order inequality by `ε` and using the secant bounds `δ ≤ u'₋(z') ε`,
`δ ≤ c₀ ε`. -/
private lemma nash_foc_step {θ A B δ ε m c : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A)
    (hε : 0 < ε) (h4 : (1 - θ) * ε * (B - δ) ≤ θ * δ * (A + ε)) (hδm : δ ≤ m * ε)
    (hδc : δ ≤ c * ε) : (1 - θ) * (B - c * ε) ≤ θ * m * (A + ε) := by
  have h1 : (1 - θ) * ε * (B - c * ε) ≤ (1 - θ) * ε * (B - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hε.le)
  have h2 : θ * δ * (A + ε) ≤ θ * (m * ε) * (A + ε) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδm hθ0.le) (by linarith)
  have h3 : (1 - θ) * (B - c * ε) * ε ≤ θ * m * (A + ε) * ε := by linarith
  exact le_of_mul_le_mul_right h3 hε

/-- Passing to the limit `z' ↑ z` in the first-order inequality, using the left continuity of
`u'₋` (`lem:utilitybounds`). -/
private lemma nash_foc_limit (U : AdmissibleUtility) {θ A B c z : ℝ} (hz : 0 < z)
    (hev : ∀ᶠ z' in 𝓝[<] z,
      (1 - θ) * (B - c * (z - z')) ≤ θ * U.marg z' * (A + (z - z'))) :
    (1 - θ) * B ≤ θ * U.marg z * A := by
  have hm : Tendsto U.marg (𝓝[<] z) (𝓝 (U.marg z)) :=
    (U.marg_continuousWithinAt_Iic hz).tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hid : Tendsto (fun z' : ℝ => z') (𝓝[<] z) (𝓝 z) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlim : Tendsto
      (fun z' => θ * U.marg z' * (A + (z - z')) - (1 - θ) * (B - c * (z - z')))
      (𝓝[<] z) (𝓝 (θ * U.marg z * (A + (z - z)) - (1 - θ) * (B - c * (z - z)))) :=
    ((tendsto_const_nhds.mul hm).mul (tendsto_const_nhds.add
      (tendsto_const_nhds.sub hid))).sub (tendsto_const_nhds.mul (tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hid))))
  have := ge_of_tendsto hlim (hev.mono fun z' hz' => sub_nonneg.2 hz')
  simp only [sub_self, add_zero, mul_zero, sub_zero] at this
  linarith

/-- `eq:buyersurplusbound`, pointwise form. At a bargaining maximiser `(q, d)` for wealths
`b, s ≥ 0`, with `z = K(q)` and all relevant values of `V` bounded by `L`, the buyer's gain
`G^b = U(q) + V(b-d) - V(b)` satisfies `G^b ≤ θ [u(z) + c₀ (L - z)] + (L - V(b))`.
For `0 < θ < 1`, `z > 0`, `G^b > 0` this is the first-order condition of the Nash product
`eq:nashbargaining` in the direction of a small reduction of output: with `A = J^s - T^s`,
`B = J^b - T^b`, maximality gives `(1-θ) B ≤ θ u'₋(z) A ≤ θ c₀ (L - z)`. -/
theorem buyer_surplus_bound (U : AdmissibleUtility) (hu : U.u = E.u) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) {T : ThreatRule} {V : ℝ → ℝ} (hT : T.Admissible V)
    (hV0 : ∀ x, 0 ≤ x → 0 ≤ V x) {b s : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s) {x : ℝ × ℝ}
    (hx : x ∈ E.bargainSet θ T V b s) {L : ℝ} (hLb : V b ≤ L) (hLB : V (b - x.2) ≤ L)
    (hLS : V (s + x.2) ≤ L) :
    E.U x.1 + V (b - x.2) - V b ≤
      θ * (U.u (E.K x.1) + U.c0 * (L - E.K x.1)) + (L - V b) := by
  obtain ⟨⟨hQ, hd0, hdb, hB, hS⟩, hmax⟩ := hx
  obtain ⟨hTb0, hTbV, hTs0, hTsV⟩ := hT b s hb hs
  simp only [Jb, Js] at hB hS
  have hnashx : E.nash θ T V b s x =
      (E.U x.1 + V (b - x.2) - T.Tb b s) ^ θ * (-E.K x.1 + V (s + x.2) - T.Ts b s) ^ (1 - θ) :=
    rfl
  have hz0 : 0 ≤ E.K x.1 := E.K_nonneg hQ
  have hUq : E.U x.1 = U.u (E.K x.1) := E.U_eq_u_K U hu hQ
  have hc0 := U.c0_pos
  set q := x.1 with hq
  set d := x.2 with hd
  set z := E.K q with hz
  have hVs0 := hV0 s hs
  have hzL : z ≤ L := by linarith
  have hL0 : 0 ≤ L := hz0.trans hzL
  have he0 : 0 ≤ L - V b := by linarith
  have hu0 : 0 ≤ U.u z := U.nonneg hz0
  have hcLz : 0 ≤ U.c0 * (L - z) := mul_nonneg hc0.le (by linarith)
  set Gb := E.U q + V (b - d) - V b with hGb
  have hGb0 : 0 ≤ Gb := by rw [hGb]; linarith
  have hGb_le : Gb ≤ U.u z + (L - V b) := by rw [hGb, hUq]; linarith
  have hrhs0 : 0 ≤ θ * (U.u z + U.c0 * (L - z)) := mul_nonneg hθ0 (add_nonneg hu0 hcLz)
  -- trivial cases: `z = 0` or `G^b = 0`
  rcases hz0.eq_or_lt with hz0' | hzpos
  · have huz : U.u z = 0 := by rw [← hz0', U.u_zero]
    have : 0 ≤ θ * (U.c0 * (L - z)) := mul_nonneg hθ0 hcLz
    rw [huz, zero_add]
    rw [huz, zero_add] at hGb_le
    linarith
  rcases hGb0.eq_or_lt with hGb0' | hGbpos
  · rw [← hGb0']; linarith
  -- the perturbed trades `(K⁻¹(z'), d)` with `z' < z`
  have hfeas : ∀ z', 0 ≤ z' → z' < z → U.u z - U.u z' ≤ Gb →
      (E.Kinv z', d) ∈ E.feasibleSet V b s := by
    intro z' hz'0 hz'z hδ
    refine ⟨E.Kinv_mem hz'0, hd0, hdb, ?_, ?_⟩
    · show V b ≤ E.U (E.Kinv z') + V (b - d)
      rw [E.U_Kinv U hu]
      rw [hGb, hUq] at hδ
      linarith
    · show V s ≤ -E.K (E.Kinv z') + V (s + d)
      rw [E.K_Kinv hz'0]
      linarith
  have hnash' : ∀ z', 0 ≤ z' → E.nash θ T V b s (E.Kinv z', d) =
      (U.u z' + V (b - d) - T.Tb b s) ^ θ * (-z' + V (s + d) - T.Ts b s) ^ (1 - θ) := by
    intro z' hz'0
    simp only [nash, Jb, Js, E.U_Kinv U hu, E.K_Kinv hz'0]
  set A := -z + V (s + d) - T.Ts b s with hA
  set B := E.U q + V (b - d) - T.Tb b s with hB'
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hAle : A ≤ L - z := by rw [hA]; linarith
  have hBG : Gb ≤ B := by rw [hGb, hB']; linarith
  have hBpos : 0 < B := hGbpos.trans_le hBG
  -- the admissible window of perturbations
  have hwin : max 0 (z - Gb / U.c0) < z := max_lt hzpos (by linarith [div_pos hGbpos hc0])
  have hpert : ∀ z' ∈ Ioo (max 0 (z - Gb / U.c0)) z,
      0 < z' ∧ U.u z - U.u z' < Gb ∧ U.u z - U.u z' ≤ U.c0 * (z - z') ∧
      (B - (U.u z - U.u z')) ^ θ * (A + (z - z')) ^ (1 - θ) ≤ B ^ θ * A ^ (1 - θ) := by
    intro z' hz'
    have hz'0 : 0 < z' := (le_max_left _ _).trans_lt hz'.1
    have hlt : z - Gb / U.c0 < z' := (le_max_right _ _).trans_lt hz'.1
    have hδc : U.u z - U.u z' ≤ U.c0 * (z - z') := U.sub_le_c0_mul hz'0.le hz'.2.le
    have hδG : U.u z - U.u z' < Gb := by
      have h1 : z - z' < Gb / U.c0 := by linarith
      have h2 := (lt_div_iff₀ hc0).1 h1
      linarith
    refine ⟨hz'0, hδG, hδc, ?_⟩
    have := hmax _ (hfeas z' hz'0.le hz'.2 hδG.le)
    rw [hnash' z' hz'0.le, hnashx] at this
    have e1 : U.u z' + V (b - d) - T.Tb b s = B - (U.u z - U.u z') := by rw [hB', hUq]; ring
    have e2 : -z' + V (s + d) - T.Ts b s = A + (z - z') := by rw [hA]; ring
    rw [e1, e2] at this
    exact this
  -- `θ = 0`: the seller's objective strictly improves under a small reduction of output
  rcases hθ0.eq_or_lt with hθ | hθpos
  · exfalso
    subst hθ
    obtain ⟨z', hz'⟩ : (Ioo (max 0 (z - Gb / U.c0)) z).Nonempty := nonempty_Ioo.2 hwin
    obtain ⟨-, -, -, hle⟩ := hpert z' hz'
    simp only [Real.rpow_zero, sub_zero, Real.rpow_one, one_mul] at hle
    linarith [hz'.2]
  -- `θ = 1`: the bound `G^b ≤ u(z) + e(b)` suffices
  rcases hθ1.eq_or_lt with hθ1' | hθlt
  · subst hθ1'
    rw [one_mul]
    linarith
  -- `0 < θ < 1`: first-order condition of the Nash product
  have hθ1' : 0 < 1 - θ := sub_pos.2 hθlt
  have hApos : 0 < A := by
    rcases hA0.eq_or_lt with hA0' | hApos
    · exfalso
      obtain ⟨z', hz'⟩ : (Ioo (max 0 (z - Gb / U.c0)) z).Nonempty := nonempty_Ioo.2 hwin
      obtain ⟨-, hδG, -, hle⟩ := hpert z' hz'
      rw [← hA0', Real.zero_rpow hθ1'.ne', mul_zero, zero_add] at hle
      have : 0 < (B - (U.u z - U.u z')) ^ θ * (z - z') ^ (1 - θ) :=
        mul_pos (Real.rpow_pos_of_pos (by linarith) _)
          (Real.rpow_pos_of_pos (by linarith [hz'.2]) _)
      linarith
    · exact hApos
  -- the limiting inequality `(1-θ) B ≤ θ u'₋(z) A`
  have key : (1 - θ) * B ≤ θ * U.marg z * A := by
    refine nash_foc_limit U (c := U.c0) hzpos ?_
    filter_upwards [Ioo_mem_nhdsLT hwin] with z' hz'
    obtain ⟨hz'0, hδG, hδc, hle⟩ := hpert z' hz'
    have hεpos : 0 < z - z' := sub_pos.2 hz'.2
    exact nash_foc_step hθpos hθlt hApos hεpos
      (nash_foc_aux hθpos hθlt hApos hBpos hεpos (by linarith) hle)
      (U.sub_le_marg_mul hz'0.le hz'.2.le) hδc
  -- assemble `eq:buyersurplusbound`
  have hmargA : U.marg z * A ≤ U.c0 * (L - z) :=
    mul_le_mul (U.marg_le_c0 hz0) hAle hA0 hc0.le
  have h6 : (1 - θ) * Gb ≤ θ * (U.c0 * (L - z)) := by
    linarith [mul_le_mul_of_nonneg_left hBG hθ1'.le, mul_le_mul_of_nonneg_left hmargA hθpos.le]
  have h7 : θ * Gb ≤ θ * (U.u z + (L - V b)) := mul_le_mul_of_nonneg_left hGb_le hθpos.le
  have h8 : θ * (L - V b) ≤ L - V b := mul_le_of_le_one_left he0 hθ1
  linarith

/-! ### Almost-sure properties of the meeting distribution `Ξ` -/

/-- The measurable predicate on meetings `((b, s), (q, d))` collecting, in terms of the measurable
modifications `Ut`, `Kt`, `posPart V`: nonnegative wealths, feasibility of the trade
(`eq:tradefeasible`), the value bound `L` for the pre- and post-trade values, and the buyer-surplus
bound `eq:buyersurplusbound`. -/
def Good (E : Environment) (U : AdmissibleUtility) (θ L : ℝ) (V : ℝ → ℝ)
    (z : (ℝ × ℝ) × (ℝ × ℝ)) : Prop :=
  0 ≤ z.1.1 ∧ 0 ≤ z.1.2 ∧ z.2.1 ∈ E.Q ∧ 0 ≤ z.2.2 ∧ z.2.2 ≤ z.1.1 ∧
  posPart V z.1.1 ≤ E.Ut z.2.1 + posPart V (z.1.1 - z.2.2) ∧
  posPart V z.1.2 + E.Kt z.2.1 ≤ posPart V (z.1.2 + z.2.2) ∧
  posPart V z.1.1 ≤ L ∧ posPart V z.1.2 ≤ L ∧
  posPart V (z.1.1 - z.2.2) ≤ L ∧ posPart V (z.1.2 + z.2.2) ≤ L ∧
  E.Ut z.2.1 + posPart V (z.1.1 - z.2.2) - posPart V z.1.1 ≤
    θ * (posPart U.u (E.Kt z.2.1) + U.c0 * (L - E.Kt z.2.1)) + (L - posPart V z.1.1)

theorem measurableSet_good (U : AdmissibleUtility) (θ L : ℝ) {V : ℝ → ℝ}
    (hV : ContinuousOn V (Ici 0)) : MeasurableSet {z | Good E U θ L V z} := by
  have hVt : Measurable (posPart V) := (continuous_posPart hV).measurable
  have hut : Measurable (posPart U.u) := (continuous_posPart U.continuousOn).measurable
  have hKt := E.measurable_Kt
  have hUt := E.measurable_Ut
  have mb : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 := by fun_prop
  have ms : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 := by fun_prop
  have mq : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.1 := by fun_prop
  have md : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.2 := by fun_prop
  have mB : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 - z.2.2 := by fun_prop
  have mS : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 + z.2.2 := by fun_prop
  unfold Good
  refine (measurableSet_le measurable_const mb).inter <|
    (measurableSet_le measurable_const ms).inter <|
    (mq E.measurableSet_Q).inter <|
    (measurableSet_le measurable_const md).inter <|
    (measurableSet_le md mb).inter <|
    (measurableSet_le (hVt.comp mb) ((hUt.comp mq).add (hVt.comp mB))).inter <|
    (measurableSet_le ((hVt.comp ms).add (hKt.comp mq)) (hVt.comp mS)).inter <|
    (measurableSet_le (hVt.comp mb) measurable_const).inter <|
    (measurableSet_le (hVt.comp ms) measurable_const).inter <|
    (measurableSet_le (hVt.comp mB) measurable_const).inter <|
    (measurableSet_le (hVt.comp mS) measurable_const).inter <|
    measurableSet_le (((hUt.comp mq).add (hVt.comp mB)).sub (hVt.comp mb)) ?_
  exact (measurable_const.mul ((hut.comp (hKt.comp mq)).add
    (measurable_const.mul (measurable_const.sub (hKt.comp mq))))).add
    (measurable_const.sub (hVt.comp mb))

namespace IsGeneralEquilibrium

variable {θ : ℝ} {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ}
  {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}

lemma ae_η_nonneg (h : E.IsGeneralEquilibrium θ T M V η κ) : ∀ᵐ m ∂η, 0 ≤ m := by
  rw [ae_iff]
  have e : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [e]; exact h.η_nonneg

lemma ae_V_nonneg (h : E.IsGeneralEquilibrium θ T M V η κ) : ∀ᵐ m ∂η, 0 ≤ V m := by
  filter_upwards [h.ae_η_nonneg] with m hm
  exact h.V_nonneg m hm

lemma ae_prod_nonneg (h : E.IsGeneralEquilibrium θ T M V η κ) :
    ∀ᵐ a ∂(η.prod η), 0 ≤ a.1 ∧ 0 ≤ a.2 := by
  have := h.isProb_η
  refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
  · exact (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  filter_upwards [h.ae_η_nonneg] with b hb
  filter_upwards [h.ae_η_nonneg] with s hs
  exact ⟨hb, hs⟩

/-- The law of the buyer's wealth under `Ξ` is `η`. -/
lemma map_b (h : E.IsGeneralEquilibrium θ T M V η κ) :
    (Ξ η κ).map (fun z => z.1.1) = η := by
  have := h.isProb_η; have := h.markov
  have e : (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1) = Prod.fst ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map measurable_fst measurable_fst]
  change ((Ξ η κ).fst).map Prod.fst = η
  rw [Ξ, Measure.fst_compProd, Measure.map_fst_prod]
  simp

/-- The law of the seller's wealth under `Ξ` is `η`. -/
lemma map_s (h : E.IsGeneralEquilibrium θ T M V η κ) :
    (Ξ η κ).map (fun z => z.1.2) = η := by
  have := h.isProb_η; have := h.markov
  have e : (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2) = Prod.snd ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map measurable_snd measurable_fst]
  change ((Ξ η κ).fst).map Prod.snd = η
  rw [Ξ, Measure.fst_compProd, Measure.map_snd_prod]
  simp

/-- `η`-a.e. properties transfer to the post-trade wealths, since the post-trade laws are
dominated by `2η` (`eq:generalstationarity`). -/
lemma ae_post (h : E.IsGeneralEquilibrium θ T M V η κ) {p : ℝ → Prop} (hp : ∀ᵐ m ∂η, p m) :
    ∀ᵐ z ∂(Ξ η κ), p (z.1.1 - z.2.2) ∧ p (z.1.2 + z.2.2) := by
  have hB : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 - z.2.2 := by fun_prop
  have hS : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 + z.2.2 := by fun_prop
  have h0 : η {m | ¬ p m} = 0 := ae_iff.1 hp
  rw [h.stationary, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul, add_eq_zero, mul_eq_zero, mul_eq_zero] at h0
  have h2 : (2⁻¹ : ℝ≥0∞) ≠ 0 := by simp
  exact (ae_of_ae_map hB.aemeasurable (ae_iff.2 (h0.1.resolve_left h2))).and
    (ae_of_ae_map hS.aemeasurable (ae_iff.2 (h0.2.resolve_left h2)))

/-- Pointwise properties of bargaining maximisers hold `Ξ`-a.e. (for measurable predicates),
possibly using a further `Ξ`-a.e. hypothesis `r`. -/
lemma ae_of_bargain (h : E.IsGeneralEquilibrium θ T M V η κ) {p r : (ℝ × ℝ) × (ℝ × ℝ) → Prop}
    (hp : MeasurableSet {z | p z}) (hr : ∀ᵐ z ∂(Ξ η κ), r z)
    (H : ∀ b s (x : ℝ × ℝ), 0 ≤ b → 0 ≤ s → x ∈ E.bargainSet θ T V b s → r ((b, s), x) →
      p ((b, s), x)) :
    ∀ᵐ z ∂(Ξ η κ), p z := by
  have := h.isProb_η; have := h.markov
  unfold Ξ at hr ⊢
  have hr' : ∀ᵐ a ∂(η.prod η), ∀ᵐ x ∂κ a, r (a, x) := Measure.ae_ae_of_ae_compProd hr
  refine Measure.ae_compProd_of_ae_ae hp ?_
  filter_upwards [hr', h.ae_prod_nonneg] with a ha ha0
  have hsupp : ∀ᵐ x ∂κ a, x ∈ E.bargainSet θ T V a.1 a.2 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.support a.1 a.2 ha0.1 ha0.2)] with x hx
    simpa using hx
  filter_upwards [ha, hsupp] with x hx hxB
  exact H a.1 a.2 x ha0.1 ha0.2 hxB hx

/-- `V ≤ L` `η`-a.e., for the essential bound `L = essBound V η`. -/
lemma ae_le_essBound (U : AdmissibleUtility) (hu : U.u = E.u)
    (h : E.IsGeneralEquilibrium θ T M V η κ) : ∀ᵐ m ∂η, V m ≤ essBound V η := by
  have := h.isProb_η
  exact Molico.Environment.ae_le_essBound (h.value_le_ae U hu)

/-- `Ξ`-almost every meeting is good: feasibility, the value bound `L`, and
`eq:buyersurplusbound` hold. -/
theorem ae_good (U : AdmissibleUtility) (hu : U.u = E.u) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : E.IsGeneralEquilibrium θ T M V η κ) :
    ∀ᵐ z ∂(Ξ η κ), Good E U θ (essBound V η) V z := by
  have := h.isProb_η; have := h.markov
  set L := essBound V η with hL
  have eqV : ∀ {x : ℝ}, 0 ≤ x → posPart V x = V x := fun hx => posPart_eq hx
  have hLt : ∀ᵐ m ∂η, posPart V m ≤ L := by
    filter_upwards [h.ae_le_essBound U hu, h.ae_η_nonneg] with m h1 h2
    rwa [eqV h2]
  have hb : ∀ᵐ z ∂(Ξ η κ), posPart V z.1.1 ≤ L := by
    have := hLt
    rw [← h.map_b] at this
    exact ae_of_ae_map (by fun_prop) this
  have hs : ∀ᵐ z ∂(Ξ η κ), posPart V z.1.2 ≤ L := by
    have := hLt
    rw [← h.map_s] at this
    exact ae_of_ae_map (by fun_prop) this
  have hpost := h.ae_post hLt
  refine h.ae_of_bargain (r := fun z => posPart V z.1.1 ≤ L ∧ posPart V z.1.2 ≤ L ∧
    posPart V (z.1.1 - z.2.2) ≤ L ∧ posPart V (z.1.2 + z.2.2) ≤ L)
    (E.measurableSet_good U θ L h.V_cont) ?_ ?_
  · filter_upwards [hb, hs, hpost] with z h1 h2 h3
    exact ⟨h1, h2, h3.1, h3.2⟩
  · intro b s x hb hs hx hr
    obtain ⟨hLb, hLs, hLB, hLS⟩ := hr
    obtain ⟨hQ, hd0, hdb, hB, hS⟩ := hx.1
    simp only [Jb, Js] at hB hS
    have hK0 : 0 ≤ E.K x.1 := E.K_nonneg hQ
    dsimp only at hLb hLs hLB hLS
    rw [eqV hb] at hLb
    rw [eqV hs] at hLs
    rw [eqV (sub_nonneg.2 hdb)] at hLB
    rw [eqV (add_nonneg hs hd0)] at hLS
    have hsur := E.buyer_surplus_bound U hu hθ0 hθ1 h.threat h.V_nonneg hb hs hx hLb hLB hLS
    unfold Good
    dsimp only
    rw [eqV hb, eqV hs, eqV (sub_nonneg.2 hdb), eqV (add_nonneg hs hd0), E.Ut_eq hQ, E.Kt_eq hQ,
      posPart_eq hK0]
    exact ⟨hb, hs, hQ, hd0, hdb, hB, by linarith, hLb, hLs, hLB, hLS, hsur⟩

/-- `lem:stationaryvaluebound` consequence: the mean value is at most the essential bound. -/
lemma integral_le_essBound (U : AdmissibleUtility) (hu : U.u = E.u)
    (h : E.IsGeneralEquilibrium θ T M V η κ) : ∫ m, V m ∂η ≤ essBound V η := by
  have := h.isProb_η
  calc ∫ m, V m ∂η ≤ ∫ _m, essBound V η ∂η :=
        integral_mono_ae (h.integrable_value U hu) (integrable_const _) (h.ae_le_essBound U hu)
    _ = essBound V η := by simp

/-! ### `step:necessity:stationarity` -/

/-- `step:necessity:stationarity`: the mean value `v̄ = ∫ V dη` is positive, and `c₀ > 1 + σ`.
Averaging `eq:generalbellman` over `η` and cancelling the continuation-value changes by
`eq:generalstationarity` gives `σ v̄ = ∫ [u(z) - z] dΞ < (c₀ - 1) ∫ z dΞ ≤ (c₀ - 1) v̄`. -/
theorem stationarity_restriction (U : AdmissibleUtility) (hu : U.u = E.u) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (h : E.IsGeneralEquilibrium θ T M V η κ) :
    0 < ∫ m, V m ∂η ∧ 1 + E.σ < U.c0 := by
  have := h.isProb_η; have := h.markov
  have hΞ : IsProbabilityMeasure (Ξ η κ) := by unfold Ξ; infer_instance
  set L := essBound V η with hL
  have hgood := h.ae_good U hu hθ0 hθ1
  have hVt : Continuous (posPart V) := continuous_posPart h.V_cont
  have eqV : ∀ {x : ℝ}, 0 ≤ x → posPart V x = V x := fun hx => posPart_eq hx
  have hKt := E.measurable_Kt
  have hUt := E.measurable_Ut
  have mb : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 := by fun_prop
  have ms : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 := by fun_prop
  have mq : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.1 := by fun_prop
  have mB : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1 - z.2.2 := by fun_prop
  have mS : Measurable fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2 + z.2.2 := by fun_prop
  -- the integrands on `Ξ`: production cost, utility, pre- and post-trade values
  set fK : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => E.Kt z.2.1 with hfK
  set fU : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => E.Ut z.2.1 with hfU
  set fVb : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => posPart V z.1.1 with hfVb
  set fVs : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => posPart V z.1.2 with hfVs
  set fVB : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => posPart V (z.1.1 - z.2.2) with hfVB
  set fVS : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => posPart V (z.1.2 + z.2.2) with hfVS
  -- almost-sure bounds
  have hbd : ∀ᵐ z ∂(Ξ η κ), (0 ≤ fK z ∧ fK z ≤ L) ∧ (0 ≤ fU z ∧ fU z ≤ U.ubar) ∧
      (0 ≤ fVb z ∧ fVb z ≤ L) ∧ (0 ≤ fVs z ∧ fVs z ≤ L) ∧ (0 ≤ fVB z ∧ fVB z ≤ L) ∧
      (0 ≤ fVS z ∧ fVS z ≤ L) ∧ fK z ≤ fVS z - fVs z ∧ fU z ≤ U.c0 * fK z ∧
      (0 < z.2.1 → 0 < fK z ∧ fU z < U.c0 * fK z) := by
    filter_upwards [hgood] with z hz
    obtain ⟨hb, hs, hQ, hd0, hdb, hfb, hfs, hLb, hLs, hLB, hLS, -⟩ := hz
    have hK0 : 0 ≤ E.K z.2.1 := E.K_nonneg hQ
    have hUu : E.U z.2.1 = U.u (E.K z.2.1) := E.U_eq_u_K U hu hQ
    simp only [fK, fU, fVb, fVs, fVB, fVS, E.Kt_eq hQ, E.Ut_eq hQ, hUu] at hfb hfs ⊢
    have hVb0 : 0 ≤ posPart V z.1.1 := by rw [eqV hb]; exact h.V_nonneg _ hb
    have hVs0 : 0 ≤ posPart V z.1.2 := by rw [eqV hs]; exact h.V_nonneg _ hs
    have hVB0 : 0 ≤ posPart V (z.1.1 - z.2.2) := by
      rw [eqV (sub_nonneg.2 hdb)]; exact h.V_nonneg _ (sub_nonneg.2 hdb)
    have hVS0 : 0 ≤ posPart V (z.1.2 + z.2.2) := by
      rw [eqV (add_nonneg hs hd0)]; exact h.V_nonneg _ (add_nonneg hs hd0)
    refine ⟨⟨hK0, by linarith⟩, ⟨U.nonneg hK0, U.le_ubar hK0⟩, ⟨hVb0, hLb⟩, ⟨hVs0, hLs⟩,
      ⟨hVB0, hLB⟩, ⟨hVS0, hLS⟩, by linarith, U.le_c0_mul hK0, fun hq => ?_⟩
    have hKpos := E.K_pos hQ hq
    exact ⟨hKpos, U.lt_c0_mul hKpos⟩
  -- integrability
  have intb : ∀ (f : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (C : ℝ), Measurable f →
      (∀ᵐ z ∂(Ξ η κ), 0 ≤ f z ∧ f z ≤ C) → Integrable f (Ξ η κ) := fun f C hf hb =>
    Integrable.of_bound hf.aestronglyMeasurable C (hb.mono fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg hz.1]; exact hz.2)
  have iK : Integrable fK (Ξ η κ) := intb fK L (hKt.comp mq) (hbd.mono fun z hz => hz.1)
  have iU : Integrable fU (Ξ η κ) := intb fU U.ubar (hUt.comp mq) (hbd.mono fun z hz => hz.2.1)
  have iVb : Integrable fVb (Ξ η κ) :=
    intb fVb L (hVt.measurable.comp mb) (hbd.mono fun z hz => hz.2.2.1)
  have iVs : Integrable fVs (Ξ η κ) :=
    intb fVs L (hVt.measurable.comp ms) (hbd.mono fun z hz => hz.2.2.2.1)
  have iVB : Integrable fVB (Ξ η κ) :=
    intb fVB L (hVt.measurable.comp mB) (hbd.mono fun z hz => hz.2.2.2.2.1)
  have iVS : Integrable fVS (Ξ η κ) :=
    intb fVS L (hVt.measurable.comp mS) (hbd.mono fun z hz => hz.2.2.2.2.2.1)
  -- marginals: `∫ V(b) dΞ = ∫ V(s) dΞ = v̄`
  have hv1 : ∫ x, posPart V x ∂η = ∫ z, fVb z ∂(Ξ η κ) := by
    conv_lhs => rw [← h.map_b]
    rw [integral_map (by fun_prop) hVt.aestronglyMeasurable]
  have hv2 : ∫ x, posPart V x ∂η = ∫ z, fVs z ∂(Ξ η κ) := by
    conv_lhs => rw [← h.map_s]
    rw [integral_map (by fun_prop) hVt.aestronglyMeasurable]
  -- stationarity: `v̄ = ½ ∫ V(b-d) dΞ + ½ ∫ V(s+d) dΞ`
  have hstat : ∫ x, posPart V x ∂η =
      2⁻¹ * ∫ z, fVB z ∂(Ξ η κ) + 2⁻¹ * ∫ z, fVS z ∂(Ξ η κ) := by
    have iB' : Integrable (posPart V) ((Ξ η κ).map fun z => z.1.1 - z.2.2) :=
      (integrable_map_measure hVt.aestronglyMeasurable mB.aemeasurable).2 iVB
    have iS' : Integrable (posPart V) ((Ξ η κ).map fun z => z.1.2 + z.2.2) :=
      (integrable_map_measure hVt.aestronglyMeasurable mS.aemeasurable).2 iVS
    conv_lhs => rw [h.stationary]
    rw [integral_add_measure (iB'.smul_measure (by simp)) (iS'.smul_measure (by simp)),
      integral_smul_measure, integral_smul_measure,
      integral_map mB.aemeasurable hVt.aestronglyMeasurable,
      integral_map mS.aemeasurable hVt.aestronglyMeasurable]
    simp [fVB, fVS, ENNReal.toReal_inv]
  -- the Bellman integrands
  set fb : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => fU z + fVB z - fVb z with hfb
  set fs : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => -fK z + fVS z - fVs z with hfs
  have iUB : Integrable (fun z => fU z + fVB z) (Ξ η κ) := iU.add iVB
  have iKn : Integrable (fun z => -fK z) (Ξ η κ) := iK.neg
  have iKS : Integrable (fun z => -fK z + fVS z) (Ξ η κ) := iKn.add iVS
  have ifb : Integrable fb (Ξ η κ) := iUB.sub iVb
  have ifs : Integrable fs (Ξ η κ) := iKS.sub iVs
  -- fiberwise form of the good set
  have hgood' := hgood
  unfold Ξ at hgood'
  have hfib : ∀ᵐ a ∂(η.prod η), ∀ᵐ x ∂κ a, Good E U θ L V (a, x) :=
    Measure.ae_ae_of_ae_compProd hgood'
  have hfib_b : ∀ᵐ m ∂η, ∀ᵐ s ∂η, ∀ᵐ x ∂κ (m, s), Good E U θ L V ((m, s), x) :=
    Measure.ae_ae_of_ae_prod hfib
  have hfib_s : ∀ᵐ m ∂η, ∀ᵐ b ∂η, ∀ᵐ x ∂κ (b, m), Good E U θ L V ((b, m), x) := by
    have hsw : ∀ᵐ a ∂(η.prod η), ∀ᵐ x ∂κ a.swap, Good E U θ L V (a.swap, x) := by
      have := hfib
      rw [← Measure.prod_swap] at this
      exact ae_of_ae_map measurable_swap.aemeasurable this
    exact Measure.ae_ae_of_ae_prod hsw
  -- the Bellman terms in terms of the measurable modifications
  have hb_eq : ∀ᵐ m ∂η, ∫ s, (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η =
      ∫ s, (∫ x, fb ((m, s), x) ∂κ (m, s)) ∂η := by
    filter_upwards [hfib_b, h.ae_η_nonneg] with m hm hm0
    refine integral_congr_ae ?_
    filter_upwards [hm] with s hs
    refine integral_congr_ae ?_
    filter_upwards [hs] with x hx
    obtain ⟨-, -, hQ, hd0, hdb, -⟩ := hx
    dsimp only at hQ hd0 hdb
    simp only [fb, fU, fVB, fVb, Jb, E.Ut_eq hQ, eqV (sub_nonneg.2 hdb), eqV hm0]
  have hs_eq : ∀ᵐ m ∂η, ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η =
      ∫ b, (∫ x, fs ((b, m), x) ∂κ (b, m)) ∂η := by
    filter_upwards [hfib_s, h.ae_η_nonneg] with m hm hm0
    refine integral_congr_ae ?_
    filter_upwards [hm] with b hb
    refine integral_congr_ae ?_
    filter_upwards [hb] with x hx
    obtain ⟨-, -, hQ, hd0, hdb, -⟩ := hx
    dsimp only at hQ hd0 hdb
    simp only [fs, fK, fVS, fVs, Js, E.Kt_eq hQ, eqV (add_nonneg hm0 hd0), eqV hm0]
  -- Fubini
  have hF_b : Integrable (fun a : ℝ × ℝ => ∫ x, fb (a, x) ∂κ a) (η.prod η) := by
    have := ifb
    unfold Ξ at this
    rw [Measure.compProd] at this
    have := this.integral_compProd
    simpa [Kernel.prodMkLeft_apply, Kernel.const_apply] using this
  have hF_s : Integrable (fun a : ℝ × ℝ => ∫ x, fs (a, x) ∂κ a) (η.prod η) := by
    have := ifs
    unfold Ξ at this
    rw [Measure.compProd] at this
    have := this.integral_compProd
    simpa [Kernel.prodMkLeft_apply, Kernel.const_apply] using this
  have ifb' := ifb
  have ifs' := ifs
  unfold Ξ at ifb' ifs'
  have hFub_b : ∫ z, fb z ∂(Ξ η κ) = ∫ m, ∫ s, ∫ x, fb ((m, s), x) ∂κ (m, s) ∂η ∂η := by
    unfold Ξ
    rw [Measure.integral_compProd ifb', integral_prod _ hF_b]
  have hFub_s : ∫ z, fs z ∂(Ξ η κ) = ∫ m, ∫ b, ∫ x, fs ((b, m), x) ∂κ (b, m) ∂η ∂η := by
    unfold Ξ
    rw [Measure.integral_compProd ifs', integral_prod_symm _ hF_s]
  -- the Bellman equation averaged over `η`
  have hbell : E.r * ∫ x, posPart V x ∂η =
      E.π * ∫ z, fb z ∂(Ξ η κ) + E.π * ∫ z, fs z ∂(Ξ η κ) := by
    have step1 : ∫ x, E.r * posPart V x ∂η =
        ∫ m, (E.π * ∫ s, ∫ x, fb ((m, s), x) ∂κ (m, s) ∂η +
          E.π * ∫ b, ∫ x, fs ((b, m), x) ∂κ (b, m) ∂η) ∂η := by
      refine integral_congr_ae ?_
      filter_upwards [h.ae_η_nonneg, hb_eq, hs_eq] with m hm0 h1 h2
      rw [eqV hm0, h.bellman m hm0, h1, h2]
    rw [← integral_const_mul, step1,
      integral_add (hF_b.integral_prod_left.const_mul _) (hF_s.integral_prod_right.const_mul _),
      integral_const_mul, integral_const_mul, hFub_b, hFub_s]
  -- linearity
  have hIb : ∫ z, fb z ∂(Ξ η κ) =
      ∫ z, fU z ∂(Ξ η κ) + ∫ z, fVB z ∂(Ξ η κ) - ∫ z, fVb z ∂(Ξ η κ) := by
    show ∫ z, (fU z + fVB z) - fVb z ∂(Ξ η κ) = _
    rw [integral_sub iUB iVb, integral_add iU iVB]
  have hIs : ∫ z, fs z ∂(Ξ η κ) =
      -∫ z, fK z ∂(Ξ η κ) + ∫ z, fVS z ∂(Ξ η κ) - ∫ z, fVs z ∂(Ξ η κ) := by
    show ∫ z, (-fK z + fVS z) - fVs z ∂(Ξ η κ) = _
    rw [integral_sub iKS iVs, integral_add iKn iVS, integral_neg]
  -- `σ v̄ = ∫ [u(z) - z] dΞ`
  have hcancel : ∫ z, fb z ∂(Ξ η κ) + ∫ z, fs z ∂(Ξ η κ) =
      ∫ z, fU z ∂(Ξ η κ) - ∫ z, fK z ∂(Ξ η κ) := by
    rw [hIb, hIs]; linarith
  have hrv : E.r * ∫ x, posPart V x ∂η =
      E.π * (∫ z, fU z ∂(Ξ η κ) - ∫ z, fK z ∂(Ξ η κ)) := by
    rw [hbell, ← mul_add, hcancel]
  have hσ : E.σ * ∫ x, posPart V x ∂η = ∫ z, fU z ∂(Ξ η κ) - ∫ z, fK z ∂(Ξ η κ) := by
    unfold σ
    rw [div_mul_eq_mul_div, div_eq_iff E.π_pos.ne', hrv, mul_comm]
  -- positivity from monetary trade
  have hposK : 0 < ∫ z, fK z ∂(Ξ η κ) := by
    rw [integral_pos_iff_support_of_nonneg_ae (hbd.mono fun z hz => hz.1.1) iK]
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr h.monetary) (measure_mono_ae ?_)
    filter_upwards [hbd] with z hz hq
    exact (hz.2.2.2.2.2.2.2.2 hq).1.ne'
  have iD : Integrable (fun z => U.c0 * fK z - fU z) (Ξ η κ) := (iK.const_mul _).sub iU
  have hposD : 0 < ∫ z, (U.c0 * fK z - fU z) ∂(Ξ η κ) := by
    rw [integral_pos_iff_support_of_nonneg_ae (hbd.mono fun z hz => by
      show (0 : ℝ) ≤ U.c0 * fK z - fU z
      linarith [hz.2.2.2.2.2.2.2.1]) iD]
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr h.monetary) (measure_mono_ae ?_)
    filter_upwards [hbd] with z hz hq
    have := (hz.2.2.2.2.2.2.2.2 hq).2
    show U.c0 * fK z - fU z ≠ 0
    linarith
  rw [integral_sub (iK.const_mul _) iU, integral_const_mul] at hposD
  -- `∫ z dΞ ≤ v̄ - ∫ V(b-d) dΞ ≤ v̄`
  have iDS : Integrable (fun z => fVS z - fVs z) (Ξ η κ) := iVS.sub iVs
  have hKle : ∫ z, fK z ∂(Ξ η κ) ≤ ∫ z, fVS z ∂(Ξ η κ) - ∫ z, fVs z ∂(Ξ η κ) := by
    rw [← integral_sub iVS iVs]
    exact integral_mono_ae iK iDS (hbd.mono fun z hz => hz.2.2.2.2.2.2.1)
  have hVB0 : 0 ≤ ∫ z, fVB z ∂(Ξ η κ) :=
    integral_nonneg_of_ae (hbd.mono fun z hz => hz.2.2.2.2.1.1)
  have hvK : ∫ z, fK z ∂(Ξ η κ) ≤ ∫ x, posPart V x ∂η := by linarith
  have hvpos : 0 < ∫ x, posPart V x ∂η := hposK.trans_le hvK
  have hVeq : ∫ m, V m ∂η = ∫ x, posPart V x ∂η := by
    refine integral_congr_ae ?_
    filter_upwards [h.ae_η_nonneg] with m hm
    rw [eqV hm]
  refine ⟨hVeq ▸ hvpos, ?_⟩
  -- conclude `c₀ > 1 + σ`
  by_contra hcon
  push Not at hcon
  have hσpos := E.σ_pos
  have h1 : (U.c0 - 1) * ∫ z, fK z ∂(Ξ η κ) ≤ E.σ * ∫ z, fK z ∂(Ξ η κ) :=
    mul_le_mul_of_nonneg_right (by linarith) hposK.le
  have h2 : E.σ * ∫ z, fK z ∂(Ξ η κ) ≤ E.σ * ∫ x, posPart V x ∂η :=
    mul_le_mul_of_nonneg_left hvK hσpos.le
  linarith

/-! ### `step:necessity:bargaining` -/

/-- `step:necessity:bargaining`, conditional bounds: for `η`-a.e. wealth `m`, with
`L = essBound V η`, `e(m) = L - V(m)`, and `z̄(m) = ∫∫ K(q) dκ_{m,s} dη(s)` the buyer's expected
production cost, averaging `eq:buyersurplusbound` over the buyer's meetings (Jensen's inequality
for the concave `u`) and `G^s ≤ e(m)` over the seller's meetings in `eq:generalbellman` gives
`σ V(m) ≤ θ [u(z̄) + c₀ (L - z̄)] + 2 e(m)`, and likewise `σ V(m) ≤ c₀ z̄ + 2 e(m)`. -/
theorem ae_cond_bounds (U : AdmissibleUtility) (hu : U.u = E.u) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h : E.IsGeneralEquilibrium θ T M V η κ) :
    ∀ᵐ m ∂η, 0 ≤ m ∧ V m ≤ essBound V η ∧
      ∃ zb : ℝ, 0 ≤ zb ∧ zb ≤ essBound V η ∧
        E.σ * V m ≤ θ * (U.u zb + U.c0 * (essBound V η - zb)) + 2 * (essBound V η - V m) ∧
        E.σ * V m ≤ U.c0 * zb + 2 * (essBound V η - V m) := by
  have := h.isProb_η; have := h.markov
  set L := essBound V η with hL
  have hgood := h.ae_good U hu hθ0 hθ1
  unfold Ξ at hgood
  have hfib : ∀ᵐ a ∂(η.prod η), ∀ᵐ x ∂κ a, Good E U θ L V (a, x) :=
    Measure.ae_ae_of_ae_compProd hgood
  have hfib_b : ∀ᵐ m ∂η, ∀ᵐ s ∂η, ∀ᵐ x ∂κ (m, s), Good E U θ L V ((m, s), x) :=
    Measure.ae_ae_of_ae_prod hfib
  have hfib_s : ∀ᵐ m ∂η, ∀ᵐ b ∂η, ∀ᵐ x ∂κ (b, m), Good E U θ L V ((b, m), x) := by
    have hsw : ∀ᵐ a ∂(η.prod η), ∀ᵐ x ∂κ a.swap, Good E U θ L V (a.swap, x) := by
      have := hfib
      rw [← Measure.prod_swap] at this
      exact ae_of_ae_map measurable_swap.aemeasurable this
    exact Measure.ae_ae_of_ae_prod hsw
  have eqV : ∀ {x : ℝ}, 0 ≤ x → posPart V x = V x := fun hx => posPart_eq hx
  have hKt := E.measurable_Kt
  have hUt := E.measurable_Ut
  have hVt : Measurable (posPart V) := (continuous_posPart h.V_cont).measurable
  have hut : Measurable (posPart U.u) := (continuous_posPart U.continuousOn).measurable
  have hmeas := E.measurableSet_good U θ L h.V_cont
  have mq : Measurable fun y : ℝ × (ℝ × ℝ) => y.2.1 := by fun_prop
  have mB : Measurable fun y : ℝ × (ℝ × ℝ) => y.2.2 := by fun_prop
  filter_upwards [hfib_b, hfib_s, h.ae_η_nonneg, h.ae_le_essBound U hu] with m hbm hsm hm0 hmL
  refine ⟨hm0, hmL, ?_⟩
  -- the law `η ⊗ κ_{m,·}` of the buyer's meetings at wealth `m`
  have hμm : ∀ᵐ y ∂(η ⊗ₘ κ.comap (Prod.mk m) measurable_prodMk_left),
      Good E U θ L V ((m, y.1), y.2) := by
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · have e : {y : ℝ × (ℝ × ℝ) | Good E U θ L V ((m, y.1), y.2)} =
          (fun y : ℝ × (ℝ × ℝ) => ((m, y.1), y.2)) ⁻¹' {z | Good E U θ L V z} := rfl
      rw [e]
      exact hmeas.preimage (by fun_prop)
    · simpa only [Kernel.comap_apply] using hbm
  -- integrability on the meeting law
  have hint_K : Integrable (fun y : ℝ × (ℝ × ℝ) => E.Kt y.2.1)
      (η ⊗ₘ κ.comap (Prod.mk m) measurable_prodMk_left) := by
    refine Integrable.of_bound (hKt.comp mq).aestronglyMeasurable L ?_
    filter_upwards [hμm] with y hy
    obtain ⟨-, hs, hQ, hd0, -, -, hfs, -, -, -, hLS, -⟩ := hy
    dsimp only at hs hQ hd0 hfs hLS
    rw [E.Kt_eq hQ, eqV hs] at hfs
    rw [E.Kt_eq hQ, Real.norm_eq_abs, abs_of_nonneg (E.K_nonneg hQ)]
    linarith [h.V_nonneg y.1 hs]
  have hint_u : Integrable (fun y : ℝ × (ℝ × ℝ) => posPart U.u (E.Kt y.2.1))
      (η ⊗ₘ κ.comap (Prod.mk m) measurable_prodMk_left) :=
    Integrable.of_bound (hut.comp (hKt.comp mq)).aestronglyMeasurable U.ubar
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (posPart_u_nonneg U _)]
        exact posPart_u_le U _)
  have hint_fb : Integrable (fun y : ℝ × (ℝ × ℝ) => E.Ut y.2.1 + posPart V (m - y.2.2) - V m)
      (η ⊗ₘ κ.comap (Prod.mk m) measurable_prodMk_left) := by
    refine Integrable.of_bound (((hUt.comp mq).add
      (hVt.comp (measurable_const.sub mB))).sub measurable_const).aestronglyMeasurable
      (U.ubar + L + V m) ?_
    filter_upwards [hμm] with y hy
    obtain ⟨-, -, hQ, hd0, hdb, -, -, -, -, hLB, -, -⟩ := hy
    dsimp only at hQ hd0 hdb hLB
    have hK0 : 0 ≤ E.K y.2.1 := E.K_nonneg hQ
    have hU0 : 0 ≤ E.U y.2.1 := by rw [E.U_eq_u_K U hu hQ]; exact U.nonneg hK0
    have hUb : E.U y.2.1 ≤ U.ubar := by rw [E.U_eq_u_K U hu hQ]; exact U.le_ubar hK0
    have hVB0 : 0 ≤ posPart V (m - y.2.2) := by
      rw [eqV (sub_nonneg.2 hdb)]; exact h.V_nonneg _ (sub_nonneg.2 hdb)
    have hVm0 := h.V_nonneg m hm0
    rw [E.Ut_eq hQ, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- the buyer-side Bellman term as an integral against the meeting law
  have hBb : ∫ s, (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η =
      ∫ y, (E.Ut y.2.1 + posPart V (m - y.2.2) - V m)
        ∂(η ⊗ₘ κ.comap (Prod.mk m) measurable_prodMk_left) := by
    rw [Measure.integral_compProd hint_fb]
    simp only [Kernel.comap_apply]
    refine integral_congr_ae ?_
    filter_upwards [hbm] with s hs
    refine integral_congr_ae ?_
    filter_upwards [hs] with x hx
    obtain ⟨-, -, hQ, hd0, hdb, -⟩ := hx
    dsimp only at hQ hd0 hdb
    simp only [Jb, E.Ut_eq hQ, eqV (sub_nonneg.2 hdb)]
  -- the seller-side Bellman term is at most `e(m)`
  have hBs : ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η ≤ L - V m := by
    have hin : ∀ᵐ b ∂η, 0 ≤ ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m) ∧
        ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m) ≤ L - V m := by
      filter_upwards [hsm] with b hb
      have hpt : ∀ᵐ x ∂κ (b, m), 0 ≤ E.Js V b m x.1 x.2 - V m ∧
          E.Js V b m x.1 x.2 - V m ≤ L - V m := by
        filter_upwards [hb] with x hx
        obtain ⟨-, -, hQ, hd0, -, -, hfs, -, -, -, hLS, -⟩ := hx
        dsimp only at hQ hd0 hfs hLS
        rw [E.Kt_eq hQ, eqV hm0, eqV (add_nonneg hm0 hd0)] at hfs
        rw [eqV (add_nonneg hm0 hd0)] at hLS
        simp only [Js]
        exact ⟨by linarith, by linarith [E.K_nonneg hQ]⟩
      refine ⟨integral_nonneg_of_ae (hpt.mono fun x hx => hx.1), ?_⟩
      calc ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m) ≤ ∫ _x, (L - V m) ∂κ (b, m) :=
            integral_mono_of_nonneg (hpt.mono fun x hx => hx.1) (integrable_const _)
              (hpt.mono fun x hx => hx.2)
        _ = L - V m := by simp
    calc ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η ≤ ∫ _b, (L - V m) ∂η :=
          integral_mono_of_nonneg (hin.mono fun b hb => hb.1) (integrable_const _)
            (hin.mono fun b hb => hb.2)
      _ = L - V m := by simp
  -- abbreviate the meeting law
  set μm := η ⊗ₘ κ.comap (Prod.mk m) measurable_prodMk_left with hμm_def
  have hprob : IsProbabilityMeasure μm := by rw [hμm_def]; infer_instance
  have hae0 : ∀ᵐ y ∂μm, E.Kt y.2.1 ∈ Ici (0 : ℝ) := by
    filter_upwards [hμm] with y hy
    obtain ⟨-, -, hQ, -⟩ := hy
    dsimp only at hQ
    rw [E.Kt_eq hQ]
    exact E.K_nonneg hQ
  have hbell := h.bellman m hm0
  rw [hBb] at hbell
  have hπ := E.π_pos
  -- Jensen's inequality for the concave `u`
  have hJ : ∫ y, posPart U.u (E.Kt y.2.1) ∂μm ≤ U.u (∫ y, E.Kt y.2.1 ∂μm) := by
    have h1 : ∫ y, posPart U.u (E.Kt y.2.1) ∂μm = ∫ y, U.u (E.Kt y.2.1) ∂μm :=
      integral_congr_ae (by filter_upwards [hae0] with y hy; exact posPart_eq hy)
    rw [h1]
    exact U.concaveOn.le_map_integral U.continuousOn isClosed_Ici hae0 hint_K
      (hint_u.congr (by
        filter_upwards [hae0] with y hy
        simp only [Function.comp_apply]
        exact posPart_eq hy))
  refine ⟨∫ y, E.Kt y.2.1 ∂μm, integral_nonneg_of_ae hae0, ?_, ?_, ?_⟩
  · -- `z̄ ≤ L`
    calc ∫ y, E.Kt y.2.1 ∂μm ≤ ∫ _y, L ∂μm := by
          refine integral_mono_ae hint_K (integrable_const _) ?_
          filter_upwards [hμm] with y hy
          obtain ⟨-, hs, hQ, hd0, -, -, hfs, -, -, -, hLS, -⟩ := hy
          dsimp only at hs hQ hd0 hfs hLS
          rw [E.Kt_eq hQ, eqV hs] at hfs
          show E.Kt y.2.1 ≤ L
          rw [E.Kt_eq hQ]
          linarith [h.V_nonneg y.1 hs]
      _ = L := by simp
  · -- the main bound
    have hint_K' : Integrable (fun y : ℝ × (ℝ × ℝ) => L - E.Kt y.2.1) μm :=
      (integrable_const L).sub hint_K
    have hint_mid : Integrable (fun y : ℝ × (ℝ × ℝ) =>
        posPart U.u (E.Kt y.2.1) + U.c0 * (L - E.Kt y.2.1)) μm :=
      hint_u.add (hint_K'.const_mul _)
    have hint_rhs : Integrable (fun y : ℝ × (ℝ × ℝ) =>
        θ * (posPart U.u (E.Kt y.2.1) + U.c0 * (L - E.Kt y.2.1)) + (L - V m)) μm :=
      (hint_mid.const_mul _).add (integrable_const _)
    have hmono : ∫ y, (E.Ut y.2.1 + posPart V (m - y.2.2) - V m) ∂μm ≤
        ∫ y, (θ * (posPart U.u (E.Kt y.2.1) + U.c0 * (L - E.Kt y.2.1)) + (L - V m)) ∂μm := by
      refine integral_mono_ae hint_fb hint_rhs ?_
      filter_upwards [hμm] with y hy
      have hsur := hy.2.2.2.2.2.2.2.2.2.2.2
      dsimp only at hsur
      rwa [eqV hm0] at hsur
    have hlin : ∫ y, (θ * (posPart U.u (E.Kt y.2.1) + U.c0 * (L - E.Kt y.2.1)) + (L - V m)) ∂μm =
        θ * (∫ y, posPart U.u (E.Kt y.2.1) ∂μm + U.c0 * (L - ∫ y, E.Kt y.2.1 ∂μm)) +
          (L - V m) := by
      rw [integral_add (hint_mid.const_mul _) (integrable_const _), integral_const_mul,
        integral_add hint_u (hint_K'.const_mul _), integral_const_mul,
        integral_sub (integrable_const _) hint_K]
      simp
    have hθJ := mul_le_mul_of_nonneg_left hJ hθ0
    have h1 : ∫ y, (E.Ut y.2.1 + posPart V (m - y.2.2) - V m) ∂μm ≤
        θ * (U.u (∫ y, E.Kt y.2.1 ∂μm) + U.c0 * (L - ∫ y, E.Kt y.2.1 ∂μm)) + (L - V m) := by
      rw [hlin] at hmono
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hπ.le
    have h3 := mul_le_mul_of_nonneg_left hBs hπ.le
    unfold σ
    rw [div_mul_eq_mul_div, div_le_iff₀ hπ, hbell]
    linarith
  · -- the simpler bound `σ V(m) ≤ c₀ z̄ + 2 e(m)`
    have hint_rhs : Integrable (fun y : ℝ × (ℝ × ℝ) => U.c0 * E.Kt y.2.1 + (L - V m)) μm :=
      (hint_K.const_mul _).add (integrable_const _)
    have hmono : ∫ y, (E.Ut y.2.1 + posPart V (m - y.2.2) - V m) ∂μm ≤
        ∫ y, (U.c0 * E.Kt y.2.1 + (L - V m)) ∂μm := by
      refine integral_mono_ae hint_fb hint_rhs ?_
      filter_upwards [hμm] with y hy
      obtain ⟨-, -, hQ, hd0, hdb, -, -, -, -, hLB, -, -⟩ := hy
      dsimp only at hQ hd0 hdb hLB
      show E.Ut y.2.1 + posPart V (m - y.2.2) - V m ≤ U.c0 * E.Kt y.2.1 + (L - V m)
      rw [E.Ut_eq hQ, E.Kt_eq hQ, E.U_eq_u_K U hu hQ]
      linarith [U.le_c0_mul (E.K_nonneg hQ)]
    have hlin : ∫ y, (U.c0 * E.Kt y.2.1 + (L - V m)) ∂μm =
        U.c0 * ∫ y, E.Kt y.2.1 ∂μm + (L - V m) := by
      rw [integral_add (hint_K.const_mul _) (integrable_const _), integral_const_mul]
      simp
    have h1 : ∫ y, (E.Ut y.2.1 + posPart V (m - y.2.2) - V m) ∂μm ≤
        U.c0 * ∫ y, E.Kt y.2.1 ∂μm + (L - V m) := hlin ▸ hmono
    have h2 := mul_le_mul_of_nonneg_left h1 hπ.le
    have h3 := mul_le_mul_of_nonneg_left hBs hπ.le
    unfold σ
    rw [div_mul_eq_mul_div, div_le_iff₀ hπ, hbell]
    linarith

end IsGeneralEquilibrium

/-! ### `prop:necessity` -/

/-- `prop:necessity` (nonexistence for general bargaining power), eq. `eq:generalnecessary`:
under `ass:utility` on the composite utility, a stationary monetary equilibrium in the sense of
`def:generaleq` with bargaining power `θ ∈ [0,1]` and any admissible threat-point rule can exist
only if `c₀ > 1 + σ` and `θ c₀ > σ`, where `σ = r/π`. -/
theorem necessity_general (U : AdmissibleUtility) (hu : U.u = E.u) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ}
    {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)} (h : E.IsGeneralEquilibrium θ T M V η κ) :
    1 + E.σ < U.c0 ∧ E.σ < θ * U.c0 := by
  have := h.isProb_η
  obtain ⟨hv, hc0⟩ := h.stationarity_restriction U hu hθ0 hθ1
  refine ⟨hc0, ?_⟩
  set L := essBound V η with hLdef
  have hL : 0 < L := hv.trans_le (h.integral_le_essBound U hu)
  have hσ := E.σ_pos
  have hc0pos := U.c0_pos
  have hcond := h.ae_cond_bounds U hu hθ0 hθ1
  -- wealth levels `m n` in the good set with `V (m n) → L`
  have hex : ∀ n : ℕ, ∃ m, (0 ≤ m ∧ V m ≤ L ∧ ∃ zb : ℝ, 0 ≤ zb ∧ zb ≤ L ∧
      E.σ * V m ≤ θ * (U.u zb + U.c0 * (L - zb)) + 2 * (L - V m) ∧
      E.σ * V m ≤ U.c0 * zb + 2 * (L - V m)) ∧ L - 1 / ((n : ℝ) + 1) < V m := fun n =>
    exists_essBound_sub_lt h.ae_V_nonneg hcond Nat.one_div_pos_of_nat
  choose m hm hmV using hex
  choose zb hzb0 hzbL hzb1 hzb2 using fun n => (hm n).2.2
  have hVlim : Tendsto (fun n => V (m n)) atTop (𝓝 L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
      (fun n => (hmV n).le) (fun n => (hm n).2.1)
    have := (tendsto_const_nhds (x := L)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  -- a convergent subsequence of the expected production costs
  obtain ⟨zs, hzs, φ, hφ, hzlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 L)
    (fun n => (⟨hzb0 n, hzbL n⟩ : zb n ∈ Icc 0 L))
  rw [closure_Icc] at hzs
  have hVφ : Tendsto (fun n => V (m (φ n))) atTop (𝓝 L) := hVlim.comp hφ.tendsto_atTop
  have he : Tendsto (fun n => 2 * (L - V (m (φ n)))) atTop (𝓝 (2 * (L - L))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hVφ)
  have hzφ : Tendsto (fun n => zb (φ n)) atTop (𝓝 zs) := hzlim
  have hulim : Tendsto (fun n => U.u (zb (φ n))) atTop (𝓝 (U.u zs)) :=
    (U.continuousOn zs hzs.1).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hzφ, Eventually.of_forall fun n => hzb0 (φ n)⟩)
  -- pass to the limit in the two conditional bounds
  have h2 : E.σ * L ≤ U.c0 * zs + 2 * (L - L) :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hVφ)
      ((tendsto_const_nhds.mul hzφ).add he) (Eventually.of_forall fun n => hzb2 (φ n))
  have h1 : E.σ * L ≤ θ * (U.u zs + U.c0 * (L - zs)) + 2 * (L - L) :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hVφ)
      ((tendsto_const_nhds.mul (hulim.add (tendsto_const_nhds.mul
        (tendsto_const_nhds.sub hzφ)))).add he) (Eventually.of_forall fun n => hzb1 (φ n))
  simp only [sub_self, mul_zero, add_zero] at h1 h2
  -- `z_* > 0`, and strict concavity gives `σ L < θ c₀ L`
  have hzs_pos : 0 < zs := by
    by_contra hcon
    push Not at hcon
    have : U.c0 * zs ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc0pos.le hcon
    nlinarith
  have hstrict : E.σ * L < θ * U.c0 * L := by
    rcases hθ0.eq_or_lt with hθ | hθpos
    · exfalso
      rw [← hθ, zero_mul] at h1
      linarith [mul_pos hσ hL]
    · have hu := U.lt_c0_mul hzs_pos
      have : θ * (U.u zs + U.c0 * (L - zs)) < θ * (U.c0 * zs + U.c0 * (L - zs)) :=
        mul_lt_mul_of_pos_left (by linarith) hθpos
      have e : θ * (U.c0 * zs + U.c0 * (L - zs)) = θ * U.c0 * L := by ring
      linarith
  by_contra hcon
  push Not at hcon
  have := mul_le_mul_of_nonneg_right hcon hL.le
  linarith

/-- `prop:necessity`: no monetary equilibrium exists when the sellers have all the bargaining
power (`θ = 0`). -/
theorem necessity_general_zero (U : AdmissibleUtility) (hu : U.u = E.u) {T : ThreatRule}
    {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ} {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    (h : E.IsGeneralEquilibrium 0 T M V η κ) : False := by
  have := (necessity_general U hu le_rfl zero_le_one h).2
  rw [zero_mul] at this
  exact absurd this (not_lt.2 E.σ_pos.le)

/-- `prop:necessity`: the first condition `c₀ > 1 + σ` is the activation condition
`β c₀ > 1` (`eq:active`), since `1 + σ = 1/β`. -/
theorem necessity_general_active (U : AdmissibleUtility) (hu : U.u = E.u) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ}
    {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)} (h : E.IsGeneralEquilibrium θ T M V η κ) :
    1 < E.β * U.c0 := by
  have h1 := (necessity_general U hu hθ0 hθ1 h).1
  rw [E.σ_eq, add_sub_cancel, div_lt_iff₀ E.β_pos] at h1
  linarith

/-- `prop:necessity` at `θ = 1`: the conditions reduce to `β c₀ > 1`. -/
theorem necessity_general_one (U : AdmissibleUtility) (hu : U.u = E.u) {T : ThreatRule}
    {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ} {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)}
    (h : E.IsGeneralEquilibrium 1 T M V η κ) : 1 < E.β * U.c0 :=
  necessity_general_active U hu zero_le_one le_rfl h

end Molico.Environment
