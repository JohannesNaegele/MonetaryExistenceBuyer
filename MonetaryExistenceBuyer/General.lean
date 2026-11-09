import MonetaryExistenceBuyer.Model
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# The general model: technology, bargaining, and stationary equilibrium (§2.1–2.4)

Formalizes, from `existence-theorem.tex`:

* `def:environment` — technology, money, matching (`Environment`);
* `def:compositeutility` — the composite utility `u = U ∘ K⁻¹` (`Environment.u`);
* `def:effectivediscount` — `β = π/(r + π)`, `σ = r/π` (`Environment.β`);
* `def:bargaining` — payoffs `J^b, J^s`, the individually rational set `ℱ_V(b,s)`, and the
  bargaining correspondence `ℬ^θ_{V,T}(b,s)` (`Jb`, `Js`, `feasibleSet`, `bargainSet`);
* `def:generaleq` — stationary equilibrium in relaxed strategies for general bargaining power
  (`IsGeneralEquilibrium`);
* `lem:buyerreduction`, eq. `eq:sellerbinding` — the seller's constraint binds for `θ = 1`.

The Bellman part of `lem:buyerreduction` (`eq:buyerflow`) and `rem:physicaloutput` are in
`General/Bargain.lean` and `General/PhysicalOutput.lean`.

A trade is a pair `(q, d)` of physical output and payment; a meeting record is
`((b, s), (q, d)) ∈ (ℝ × ℝ) × (ℝ × ℝ)`.
-/

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Molico

/-- `def:environment`: utility `U` of consumption and cost `K` of production on outputs
`q ∈ [0, q̄)`, `q̄ ∈ (0, ∞]`; both continuous, strictly increasing, vanishing at `0`, with
`K(q) → ∞` as `q ↑ q̄`. Each period an agent has a buying opportunity with probability
`π ∈ (0, 1/2]` and a selling opportunity with the same probability; `r > 0` is the discount
rate. -/
structure Environment where
  U : ℝ → ℝ
  K : ℝ → ℝ
  qbar : ℝ≥0∞
  qbar_pos : 0 < qbar
  π : ℝ
  r : ℝ
  π_pos : 0 < π
  π_le : π ≤ 1 / 2
  r_pos : 0 < r
  U_cont : ContinuousOn U {q | 0 ≤ q ∧ ENNReal.ofReal q < qbar}
  K_cont : ContinuousOn K {q | 0 ≤ q ∧ ENNReal.ofReal q < qbar}
  U_strictMono : StrictMonoOn U {q | 0 ≤ q ∧ ENNReal.ofReal q < qbar}
  K_strictMono : StrictMonoOn K {q | 0 ≤ q ∧ ENNReal.ofReal q < qbar}
  U_zero : U 0 = 0
  K_zero : K 0 = 0
  /-- `K(q) → ∞` as `q ↑ q̄` (with strict monotonicity: `K` is unbounded on `[0, q̄)`). -/
  K_unbounded : ∀ C : ℝ, ∃ q, 0 ≤ q ∧ ENNReal.ofReal q < qbar ∧ C ≤ K q

namespace Environment

variable (E : Environment)

/-- The output range `[0, q̄)`. -/
def Q : Set ℝ := {q | 0 ≤ q ∧ ENNReal.ofReal q < E.qbar}

/-- `K⁻¹ : ℝ₊ → [0, q̄)`. -/
def Kinv (x : ℝ) : ℝ := Function.invFunOn E.K E.Q x

/-- `def:environment`: `K` has a continuous increasing inverse from `ℝ₊` onto `[0, q̄)`. -/
theorem Kinv_spec {x : ℝ} (hx : 0 ≤ x) : E.Kinv x ∈ E.Q ∧ E.K (E.Kinv x) = x := by
  apply Function.invFunOn_pos
  obtain ⟨q₁, hq₁0, hq₁Q, hq₁⟩ := E.K_unbounded x
  have hsub : Icc 0 q₁ ⊆ E.Q := fun q hq =>
    ⟨hq.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hq.2) hq₁Q⟩
  have hcont : ContinuousOn E.K (Icc 0 q₁) := E.K_cont.mono hsub
  obtain ⟨q, hq, hKq⟩ := intermediate_value_Icc hq₁0 hcont
    ⟨by rw [E.K_zero]; exact hx, hq₁⟩
  exact ⟨q, hsub hq, hKq⟩

/-- `def:compositeutility`: `u(x) = U(K⁻¹(x))` (in disutility units). -/
def u (x : ℝ) : ℝ := E.U (E.Kinv x)

/-- `def:effectivediscount`: `β = π/(r+π)`. -/
def β : ℝ := E.π / (E.r + E.π)

lemma β_pos : 0 < E.β := div_pos E.π_pos (by linarith [E.π_pos, E.r_pos])

lemma β_lt_one : E.β < 1 := by
  unfold β; rw [div_lt_one (by linarith [E.π_pos, E.r_pos])]; linarith [E.r_pos]

/-- `def:effectivediscount`: `σ = 1/β - 1 = r/π`. -/
lemma one_div_β_sub_one : 1 / E.β - 1 = E.r / E.π := by
  unfold β; have := E.π_pos; have := E.r_pos; field_simp; ring

/-! ### Bargaining (`def:bargaining`) -/

/-- Buyer's payoff `J^b_V(b,s;q,d) = U(q) + V(b - d)` (`eq:tradepayoffs`). -/
def Jb (V : ℝ → ℝ) (b _s q d : ℝ) : ℝ := E.U q + V (b - d)

/-- Seller's payoff `J^s_V(b,s;q,d) = -K(q) + V(s + d)` (`eq:tradepayoffs`). -/
def Js (V : ℝ → ℝ) (_b s q d : ℝ) : ℝ := -E.K q + V (s + d)

/-- The individually rational feasible set `ℱ_V(b,s)` (`eq:tradefeasible`). -/
def feasibleSet (V : ℝ → ℝ) (b s : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ E.Q ∧ 0 ≤ x.2 ∧ x.2 ≤ b ∧ V b ≤ E.Jb V b s x.1 x.2 ∧ V s ≤ E.Js V b s x.1 x.2}

/-- A threat-point rule `T^b = T^b(b,s)`, `T^s = T^s(b,s)`. -/
structure ThreatRule where
  Tb : ℝ → ℝ → ℝ
  Ts : ℝ → ℝ → ℝ

/-- The threat points are admissible for `V`: `0 ≤ T^b ≤ V(b)`, `0 ≤ T^s ≤ V(s)`. -/
def ThreatRule.Admissible (T : ThreatRule) (V : ℝ → ℝ) : Prop :=
  ∀ b s, 0 ≤ b → 0 ≤ s → 0 ≤ T.Tb b s ∧ T.Tb b s ≤ V b ∧ 0 ≤ T.Ts b s ∧ T.Ts b s ≤ V s

/-- The (generalized) Nash product `(J^b - T^b)^θ (J^s - T^s)^{1-θ}` (`eq:nashbargaining`),
with `0^0 = 1`. For `θ = 1` it is `J^b - T^b`. -/
def nash (θ : ℝ) (T : ThreatRule) (V : ℝ → ℝ) (b s : ℝ) (x : ℝ × ℝ) : ℝ :=
  (E.Jb V b s x.1 x.2 - T.Tb b s) ^ θ * (E.Js V b s x.1 x.2 - T.Ts b s) ^ (1 - θ)

/-- The bargaining correspondence `ℬ^θ_{V,T}(b,s)`: maximisers of the Nash product over
`ℱ_V(b,s)` (`eq:nashbargaining`; for `θ = 1` the buyer's payoff is maximised). -/
def bargainSet (θ : ℝ) (T : ThreatRule) (V : ℝ → ℝ) (b s : ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ E.feasibleSet V b s ∧ ∀ y ∈ E.feasibleSet V b s, E.nash θ T V b s y ≤ E.nash θ T V b s x}

/-! ### Stationary equilibrium for general bargaining power (`def:generaleq`) -/

/-- The meeting distribution `Ξ = (η ⊗ η) ⊗ κ` of `((b, s), (q, d))`. -/
def Ξ (η : Measure ℝ) (κ : Kernel (ℝ × ℝ) (ℝ × ℝ)) : Measure ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (η.prod η) ⊗ₘ κ

/-- `def:generaleq`: a stationary equilibrium in relaxed strategies `(V, η, κ)` of mean `M`, for
bargaining power `θ` and threat-point rule `T`. The value function is only assumed continuous and
nonnegative; boundedness on `supp η` is automatic (`lem:stationaryvaluebound`). The two
`bellman_integrable` fields say that the integrals in `eq:generalbellman` exist. -/
structure IsGeneralEquilibrium (θ : ℝ) (T : ThreatRule) (M : ℝ) (V : ℝ → ℝ) (η : Measure ℝ)
    (κ : Kernel (ℝ × ℝ) (ℝ × ℝ)) : Prop where
  V_cont : ContinuousOn V (Ici 0)
  V_nonneg : ∀ x, 0 ≤ x → 0 ≤ V x
  threat : T.Admissible V
  isProb_η : IsProbabilityMeasure η
  η_nonneg : η (Iio 0) = 0
  integrable_id : Integrable id η
  mean : ∫ x, x ∂η = M
  markov : IsMarkovKernel κ
  /-- `κ_{b,s}` is supported on the bargaining set. -/
  support : ∀ b s, 0 ≤ b → 0 ≤ s → κ (b, s) (E.bargainSet θ T V b s)ᶜ = 0
  /-- The buyer-side integral in `eq:generalbellman` exists. -/
  bellman_integrable_b : ∀ m, 0 ≤ m →
    Integrable (fun s => ∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) η
  /-- The seller-side integral in `eq:generalbellman` exists. -/
  bellman_integrable_s : ∀ m, 0 ≤ m →
    Integrable (fun b => ∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) η
  /-- The Bellman equation `eq:generalbellman`. -/
  bellman : ∀ m, 0 ≤ m →
    E.r * V m = E.π * ∫ s, (∫ x, (E.Jb V m s x.1 x.2 - V m) ∂κ (m, s)) ∂η +
      E.π * ∫ b, (∫ x, (E.Js V b m x.1 x.2 - V m) ∂κ (b, m)) ∂η
  /-- Stationarity `eq:generalstationarity`: `η = ½ B_# Ξ + ½ S_# Ξ`. -/
  stationary : η = (2⁻¹ : ℝ≥0∞) • (Ξ η κ).map (fun z => z.1.1 - z.2.2) +
    (2⁻¹ : ℝ≥0∞) • (Ξ η κ).map (fun z => z.1.2 + z.2.2)
  /-- Monetary: `Ξ{q > 0} > 0`. -/
  monetary : Ξ η κ {z | 0 < z.2.1} ≠ 0

/-- `def:generaleq`: the equilibrium is deterministic if every kernel is a Dirac mass. -/
def IsDeterministicKernel (κ : Kernel (ℝ × ℝ) (ℝ × ℝ)) : Prop :=
  ∀ b s, 0 ≤ b → 0 ≤ s → ∃ x, κ (b, s) = Measure.dirac x

/-! ### The buyer-takes-all specialization -/

/-- `lem:buyerreduction`, eq. `eq:sellerbinding`: for `θ = 1` every bargaining maximiser makes
the seller's participation constraint bind, `K(q) = V(s + d) - V(s)`; hence
`q = K⁻¹(Δ_V(s,d))` and the seller's surplus is zero. -/
theorem buyerreduction_binding (T : ThreatRule) {V : ℝ → ℝ} {b s : ℝ} {x : ℝ × ℝ}
    (hx : x ∈ E.bargainSet 1 T V b s) : E.K x.1 = V (s + x.2) - V s := by
  obtain ⟨hF, hmax⟩ := hx
  obtain ⟨hQ, hd0, hdb, hB, hS⟩ := hF
  -- for `θ = 1` the Nash product is the buyer's surplus
  have hnash : ∀ y, E.nash 1 T V b s y = E.Jb V b s y.1 y.2 - T.Tb b s := fun y => by
    simp [nash]
  have hle : E.K x.1 ≤ V (s + x.2) - V s := by
    simp only [Js] at hS; linarith
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  -- the seller's constraint is slack: raise output slightly
  obtain ⟨r', hr'0, hqr', hr'Q⟩ := ENNReal.lt_iff_exists_real_btwn.1 hQ.2
  have hqr : x.1 < r' := (ENNReal.ofReal_lt_ofReal_iff'.1 hqr').1
  have hsub : Ioo x.1 r' ⊆ E.Q := fun q hq =>
    ⟨hQ.1.trans hq.1.le, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hq.2.le) hr'Q⟩
  have hcont : ContinuousWithinAt E.K (Ioo x.1 r') x.1 :=
    (E.K_cont x.1 hQ).mono hsub
  haveI : (𝓝[Ioo x.1 r'] x.1).NeBot := left_nhdsWithin_Ioo_neBot hqr
  obtain ⟨q', hq'K, hq'⟩ := ((hcont.eventually (gt_mem_nhds hlt)).and
    self_mem_nhdsWithin).exists
  have hU : E.U x.1 < E.U q' := E.U_strictMono hQ (hsub hq') hq'.1
  have hy : (q', x.2) ∈ E.feasibleSet V b s := by
    refine ⟨hsub hq', hd0, hdb, ?_, ?_⟩
    · simp only [Jb] at hB ⊢; linarith
    · simp only [Js]; linarith
  have := hmax _ hy
  rw [hnash, hnash] at this
  simp only [Jb] at this
  linarith

end Environment

end Molico
