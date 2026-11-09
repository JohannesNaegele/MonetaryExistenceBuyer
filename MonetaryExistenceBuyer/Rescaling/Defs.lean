import MonetaryExistenceBuyer.Limit.Props
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Rescaling inside the jump (§5 of `existence-theorem.tex`)

Fix a bad sequence (`def:bad`) with jump `J₀ = V(0+) > 0` and a normalization level
`a ∈ (0, J₀)`.

* `SelectedSeq.crossIdx`, `scale` (`e_n`), `δn`, `Wn`, `ι`, `αn`, `Γhat` — `def:normalization`,
  `def:normalizedmeeting`. Normalized wealth lives in `[0, ∞] = ℝ≥0∞`.
* `NormalizedLimit` — a normalized limit `(W, α)` (with the limiting meeting measure `Γ̂` of
  `lem:flowpassage`) along a subsequence.
* `NormalizedLimit.Lsup` (`L`), `J'`, `Wbar` (`W̄`), `Xplus` (`𝒳₊`), `A` (`𝒜_m`), `EW` (`ℰ_W`),
  `Hc` (`ℋ(m; z, y)`, `def:normalizedobjective`), `HasFiniteSaturation` (`def:onset`).
* `normalizedLimit_exists`, `NormalizedLimit.props` — `lem:normalizedlimits`;
  `passage` — `prop:passage`; `flowpassage` — `lem:flowpassage`;
  `bellmanInfinity` — `lem:bellmaninfinity`; `pin` — `prop:pin`; `nonEscape` — `prop:non-escape`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

namespace SelectedSeq

variable (S : SelectedSeq P) (a : ℝ)

/-- The crossing index: the first grid index `i ≤ N_n` with `V_n(i h_n) ≥ a`
(`eq:crossing`; `0` if there is none, which does not happen for large `n`). -/
def crossIdx (n : ℕ) : ℕ := sInf {i | i ≤ S.N n ∧ a ≤ S.V n i}

/-- The normalization scale `e_n(a) = min{x ∈ 𝒳_n : V_n(x) ≥ a}` (`eq:crossing`). -/
def scale (n : ℕ) : ℝ := S.h n * S.crossIdx a n

/-- `δ_n = h_n / e_n`. -/
def δn (n : ℕ) : ℝ := S.h n / S.scale a n

/-- The normalized value profile `W_n(x) = V_n(e_n x)`. -/
def Wn (n : ℕ) (x : ℝ) : ℝ := S.Vn n (S.scale a n * x)

/-- The normalized state `ι_n(s) = (s/e_n, V_n(s)) ∈ [0, ∞] × ℝ` (`eq:jointstates`). -/
def ι (n : ℕ) (s : ℝ) : ℝ≥0∞ × ℝ := (ENNReal.ofReal (s / S.scale a n), S.Vn n s)

/-- The joint state distribution `α_n = (ι_n)_# η_n` (`eq:jointstates`). -/
def αn (n : ℕ) : Measure (ℝ≥0∞ × ℝ) := (S.ηn n).map (S.ι a n)

/-- `def:normalizedmeeting`: the normalized meeting measures `Γ̂_n` on `[0,∞]⁵`, recording
normalized `(b, s, d, b - d, s + d)`. -/
def Γhat (n : ℕ) : Measure (ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞) :=
  (S.Γn n).map fun p => (ENNReal.ofReal (p.1 / S.scale a n), ENNReal.ofReal (p.2.1 / S.scale a n),
    ENNReal.ofReal (p.2.2 / S.scale a n), ENNReal.ofReal ((p.1 - p.2.2) / S.scale a n),
    ENNReal.ofReal ((p.2.1 + p.2.2) / S.scale a n))

end SelectedSeq

/-- `def:normalization` + `lem:flowpassage`: a *normalized limit* at level `a`, along a
subsequence `φ`:
* either `δ_n → 0` (non-lattice case, `δ = 0`) or `δ_n ≡ δ > 0` (lattice case);
* `W_n → W` locally uniformly on `(0, ∞)`, with `W(0) := 0`;
* `α_n ⇒ α` on the compact normalized state space `𝕄 = [0, ∞] × [0, L_*]`;
* `Γ̂_n ⇒ Γ̂` on `[0, ∞]⁵`. -/
structure NormalizedLimit (S : SelectedSeq P) (a : ℝ) where
  φ : ℕ → ℕ
  φ_mono : StrictMono φ
  δ : ℝ
  lattice : (δ = 0 ∧ Tendsto (fun n => S.δn a (φ n)) atTop (𝓝 0)) ∨
    (0 < δ ∧ ∀ n, S.δn a (φ n) = δ)
  W : ℝ → ℝ
  W_zero : W 0 = 0
  W_conv : TendstoLocallyUniformlyOn (fun n => S.Wn a (φ n)) W atTop (Ioi 0)
  α : Measure (ℝ≥0∞ × ℝ)
  α_prob : IsProbabilityMeasure α
  α_conv : WeakConv (fun n => S.αn a (φ n)) α
  Γh : Measure (ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞)
  Γh_prob : IsProbabilityMeasure Γh
  Γh_conv : WeakConv (fun n => S.Γhat a (φ n)) Γh

namespace NormalizedLimit

variable {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)

/-- `L = sup_{x > 0} W(x)`. -/
def Lsup : ℝ := sSup (NL.W '' Ioi 0)

/-- `J' = W(0+)`. -/
def J' : ℝ := sInf (NL.W '' Ioi 0)

/-- `W̄ = W` on `(0, ∞)`, `W̄(0) = J'`. -/
def Wbar (x : ℝ) : ℝ := if x = 0 then NL.J' else NL.W x

/-- Admissible limit buyer wealths `𝒳₊` (`eq:buyerset`): `(0, ∞)` or `δ ℕ`. -/
def Xplus : Set ℝ := if NL.δ = 0 then Ioi 0 else {x | ∃ k : ℕ, 1 ≤ k ∧ x = k * NL.δ}

/-- Admissible limit transfers `𝒜_m = [0, m] ∩ (𝒳₊ ∪ {0})` (`eq:buyerset`). -/
def A (m : ℝ) : Set ℝ := Icc 0 m ∩ (NL.Xplus ∪ {0})

/-- The compatible states `ℰ_W` (`eq:compatiblestates`). -/
def EW : Set (ℝ≥0∞ × ℝ) :=
  ({0} ×ˢ Icc 0 NL.J') ∪ {p | ∃ z ∈ NL.Xplus, p = (ENNReal.ofReal z, NL.W z)} ∪
    ({⊤} ×ˢ Icc NL.Lsup P.Lstar)

/-- `def:normalizedobjective`, eq. `eq:normalizedobjective`: the limiting maximized payoff
`ℋ(m; z, y)`. -/
def Hc (m : ℝ) (p : ℝ≥0∞ × ℝ) : ℝ :=
  if p.1 = ⊤ then NL.W m
  else sSup ((fun d => P.U.u (NL.Wbar (p.1.toReal + d) - p.2) + NL.Wbar (m - d)) '' NL.A m)

/-- `def:onset`: the normalized limit has *finite-wealth saturation* if `x_p = inf{x > 0 : W(x) = L}`
is finite. -/
def HasFiniteSaturation : Prop := ∃ x > 0, NL.W x = NL.Lsup

/-- The wealth marginal `α^w = (pr_z)_# α` (`def:normalizedmeeting`). -/
def αw : Measure ℝ≥0∞ := NL.α.map Prod.fst

end NormalizedLimit

end Molico
