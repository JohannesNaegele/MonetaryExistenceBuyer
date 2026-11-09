import MonetaryExistenceBuyer.Limit.Basic

/-!
# Selected approximants and their Helly limit (`def:selected`)

* `SelectedSeq`: a sequence of approximant equilibria (`thm:approx`) along `h_n ↓ 0`,
  `R_n ↑ ∞`, already passed to a subsequence along which the value functions converge locally
  uniformly on `(0,∞)` and the laws `η_n` and value distributions `ν_n = (V_n)_# η_n` converge
  weakly.
* `SelectedSeq.jump`: the jump `V(0+)` at the origin; `IsBad` (`def:bad`).
* `SelectedSeq.comp`: passing to a further subsequence.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

/-- `def:selected`: selected approximant equilibria along `h_n ↓ 0`, `R_n = N_n h_n ↑ ∞`,
`R_n ≥ R_amp`, satisfying `eq:floor`, passed to a subsequence on which
* the interpolated values `V_n` converge locally uniformly on `(0, ∞)` to `V` (with `V(0) := 0`),
* `η_n ⇒ η` weakly,
* the value distributions `ν_n = (V_n)_# η_n ⇒ ν` weakly (`eq:valuelimit`). -/
structure SelectedSeq (P : Primitives) where
  h : ℕ → ℝ
  N : ℕ → ℕ
  V : ℕ → ℕ → ℝ
  η : ℕ → ℕ → ℝ
  κ : ℕ → ℕ → ℕ → ℕ → ℝ
  h_pos : ∀ n, 0 < h n
  h_tendsto : Tendsto h atTop (𝓝 0)
  R_tendsto : Tendsto (fun n => (N n : ℝ) * h n) atTop atTop
  R_ge : ∀ n, P.Ramp ≤ (N n : ℝ) * h n
  isApproxEq : ∀ n, Grid.IsApproxEq P (h n) (N n) (V n) (η n) (κ n)
  floor : ∀ n, P.ℓ0 ≤ V n (N n) ∧ V n (N n) ≤ P.Lstar
  /-- The Helly limit `V` on `(0, ∞)`, with `V(0) := 0`. -/
  Vlim : ℝ → ℝ
  Vlim_zero : Vlim 0 = 0
  V_conv : TendstoLocallyUniformlyOn (fun n => interp (h n) (N n) (V n)) Vlim atTop (Ioi 0)
  /-- The weak limit `η` of the laws. -/
  ηlim : Measure ℝ
  ηlim_prob : IsProbabilityMeasure ηlim
  η_conv : WeakConv (fun n => gridMeasure (h n) (N n) (η n)) ηlim
  /-- The limiting value distribution `ν` (`eq:valuelimit`). -/
  νlim : Measure ℝ
  νlim_prob : IsProbabilityMeasure νlim
  ν_conv : WeakConv (fun n => (gridMeasure (h n) (N n) (η n)).map (interp (h n) (N n) (V n)))
    νlim

namespace SelectedSeq

variable {P : Primitives} (S : SelectedSeq P)

/-- The interpolated value functions `V_n` on `ℝ₊`. -/
def Vn (n : ℕ) : ℝ → ℝ := interp (S.h n) (S.N n) (S.V n)

/-- The laws `η_n` as measures on `ℝ`. -/
def ηn (n : ℕ) : Measure ℝ := gridMeasure (S.h n) (S.N n) (S.η n)

/-- The joint meeting measures `Γ_n`. -/
def Γn (n : ℕ) : Measure (ℝ × ℝ × ℝ) := gridMeeting (S.h n) (S.N n) (S.η n) (S.κ n)

/-- The jump at the origin `V(0+) - V(0) = V(0+) = inf_{x > 0} V(x)`. -/
def jump : ℝ := sInf (S.Vlim '' Ioi 0)

/-- `def:bad`: a *bad sequence* is a selected sequence whose Helly limit jumps at the origin. -/
def IsBad : Prop := 0 < S.jump

/-- Passing to a further subsequence preserves all properties of a selected sequence. -/
def comp (φ : ℕ → ℕ) (hφ : StrictMono φ) : SelectedSeq P where
  h n := S.h (φ n)
  N n := S.N (φ n)
  V n := S.V (φ n)
  η n := S.η (φ n)
  κ n := S.κ (φ n)
  h_pos n := S.h_pos (φ n)
  h_tendsto := S.h_tendsto.comp hφ.tendsto_atTop
  R_tendsto := S.R_tendsto.comp hφ.tendsto_atTop
  R_ge n := S.R_ge (φ n)
  isApproxEq n := S.isApproxEq (φ n)
  floor n := S.floor (φ n)
  Vlim := S.Vlim
  Vlim_zero := S.Vlim_zero
  V_conv := fun u hu x hx => by
    obtain ⟨t, ht, hev⟩ := S.V_conv u hu x hx
    exact ⟨t, ht, hφ.tendsto_atTop.eventually hev⟩
  ηlim := S.ηlim
  ηlim_prob := S.ηlim_prob
  η_conv := by intro f; exact (S.η_conv f).comp hφ.tendsto_atTop
  νlim := S.νlim
  νlim_prob := S.νlim_prob
  ν_conv := by intro f; exact (S.ν_conv f).comp hφ.tendsto_atTop

end SelectedSeq

end Molico
