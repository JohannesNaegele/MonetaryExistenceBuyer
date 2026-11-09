import MonetaryExistenceBuyer.Model
import MonetaryExistenceBuyer.Grid.Bootstrap
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Basic limit objects

* `WeakConv`: weak convergence of measures (convergence of integrals of bounded continuous
  functions). For probability measures this is Mathlib's topology on `ProbabilityMeasure`
  (`weakConv_iff_tendsto` in `Analysis/Weak.lean`).
* `interp`: piecewise-linear interpolation of a grid function on `[0, R]`, constant on `[R, ∞)`.
* `gridMeasure`, `gridMeeting`: the grid law `η_n` and the joint meeting measure `Γ_n` as
  measures on `ℝ` and `ℝ³`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

/-- Weak convergence `μ_n ⇒ μ`: `∫ f dμ_n → ∫ f dμ` for every bounded continuous `f`. -/
def WeakConv {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μs : ℕ → Measure X)
    (μ : Measure X) : Prop :=
  ∀ f : BoundedContinuousFunction X ℝ, Tendsto (fun n => ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂μ))

/-- Piecewise-linear interpolation of the grid function `V` (values `V i` at `i h`) on
`[0, N h]`, constant continuation `V N` on `[N h, ∞)` (and `V 0` on `(-∞, 0]`). -/
def interp (h : ℝ) (N : ℕ) (V : ℕ → ℝ) (x : ℝ) : ℝ :=
  if (N : ℝ) * h ≤ x then V N
  else
    V ⌊max x 0 / h⌋₊ + (max x 0 / h - ⌊max x 0 / h⌋₊) * (V (⌊max x 0 / h⌋₊ + 1) - V ⌊max x 0 / h⌋₊)

/-- The grid law `η` as a measure on `ℝ` (weights `η l` at `l h`). -/
def gridMeasure (h : ℝ) (N : ℕ) (η : ℕ → ℝ) : Measure ℝ :=
  ∑ l ∈ Finset.range (N + 1), ENNReal.ofReal (η l) • Measure.dirac ((l : ℝ) * h)

/-- The joint meeting measure `Γ = η ⊗ η ⊗ κ` on triples `(b, s, d)` (`def:approx`). -/
def gridMeeting (h : ℝ) (N : ℕ) (η : ℕ → ℝ) (κ : ℕ → ℕ → ℕ → ℝ) : Measure (ℝ × ℝ × ℝ) :=
  ∑ m ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (N + 1), ∑ j ∈ Grid.feas N m l,
    ENNReal.ofReal (η m * η l * κ m l j) • Measure.dirac ((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h)

end Molico
