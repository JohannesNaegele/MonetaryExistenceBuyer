import MonetaryExistenceBuyer.Necessity
import MonetaryExistenceBuyer.Comparison
import MonetaryExistenceBuyer.Limit.ZeroJump
import MonetaryExistenceBuyer.Limit.Deterministic
import MonetaryExistenceBuyer.Limit.Selection
import MonetaryExistenceBuyer.General.PhysicalOutput
import MonetaryExistenceBuyer.General.Necessity

/-!
# Main result (`thm:main`)

For every mean money stock `M > 0`, the buyer-takes-all model has a stationary monetary
equilibrium of mean `M` (in the sense of `def:eq`) if and only if `β c₀ > 1`
(`eq:active`). Moreover the equilibrium can be taken deterministic (`prop:deterministic`), and
the same holds for the original primitives `(U, K)` (`def:generaleq` with `θ = 1`,
`rem:physicaloutput`), where necessity is `prop:necessity` at `θ = 1`.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace Molico

/-- **`thm:main`**: under `ass:utility`, for `β ∈ (0,1)` and every `M > 0`, a stationary monetary
equilibrium of mean `M` exists if and only if `β c₀ > 1`. -/
theorem main (U : AdmissibleUtility) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {M : ℝ} (hM : 0 < M) :
    (∃ V η Γ, IsEquilibrium U.u β M V η Γ) ↔ 1 < β * U.c0 := by
  constructor
  · -- necessity: `prop:necessity`
    rintro ⟨V, η, Γ, h⟩
    by_contra hc
    exact necessity U hβ0 hβ1 (not_lt.1 hc) h
  · -- sufficiency: proof of `thm:main` in §7
    intro hact
    let P : Primitives := ⟨U, β, M, hβ0, hβ1, hM, hact⟩
    obtain ⟨S⟩ := SelectedSeq.nonempty P
    have hnz := halflevel S
    have h0 : S.jump = 0 := le_antisymm (not_lt.1 (nojump S)) S.jump_nonneg
    obtain ⟨Γ, hΓ⟩ := zerojump S h0 hnz
    have hpos : 0 < ∫ x, x ∂S.ηlim := hΓ.mean_pos
    have hc : 0 < (∫ x, x ∂S.ηlim) / M := div_pos hpos hM
    have hres := hΓ.rescale hc
    have hmean : (∫ x, x ∂S.ηlim) / ((∫ x, x ∂S.ηlim) / M) = M := by
      field_simp
    rw [hmean] at hres
    exact ⟨_, _, _, hres⟩

/-- `thm:main` with `prop:deterministic`: if `β c₀ > 1`, for every `M > 0` there is a
*deterministic* stationary monetary equilibrium of mean `M`. -/
theorem main_deterministic (U : AdmissibleUtility) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hact : 1 < β * U.c0) {M : ℝ} (hM : 0 < M) :
    ∃ V η Γ, IsEquilibrium U.u β M V η Γ ∧ IsDeterministic Γ := by
  obtain ⟨V, η, Γ, h⟩ := (main U hβ0 hβ1 hM).2 hact
  exact ⟨V, η, Γ, h, h.isDeterministic U hβ0 hβ1⟩

/-- `thm:main`, last sentence, with `rem:physicaloutput`: for primitives `(U, K)` whose composite
utility `u = U ∘ K⁻¹` is admissible, and `β c₀ > 1` with the effective discount factor
`β = π/(r+π)`, there is, for every `M > 0`, a deterministic stationary monetary equilibrium of
mean `M` of the original model (`def:generaleq`, `θ = 1`), for any threat-point rule that is
admissible for every candidate value function (e.g. zero or continuation-value threat points). -/
theorem main_physical (E : Environment) (U : AdmissibleUtility) (hu : U.u = E.u)
    (hact : 1 < E.β * U.c0) {M : ℝ} (hM : 0 < M) (T : (ℝ → ℝ) → Environment.ThreatRule)
    (hT : ∀ V, IsValueFn V → (T V).Admissible V) :
    ∃ V η κ, E.IsGeneralEquilibrium 1 (T V) M V η κ ∧ Environment.IsDeterministicKernel κ := by
  obtain ⟨V, η, Γ, h, hdet⟩ := main_deterministic U E.β_pos E.β_lt_one hact hM
  rw [hu] at h
  obtain ⟨κ, hκ, hdk⟩ := E.physicaloutput (T V) h (hT V h.value)
  exact ⟨V, η, κ, hκ, hdk hdet⟩

/-- `thm:main` for the original primitives `(U, K)`, both directions: for primitives whose
composite utility `u = U ∘ K⁻¹` is admissible, with the effective discount factor `β = π/(r+π)`,
every `M > 0` and every threat-point rule that is admissible for all candidate value functions,
a stationary monetary equilibrium of mean `M` of the general model (`def:generaleq`, `θ = 1`)
exists if and only if `β c₀ > 1`. Necessity is `prop:necessity` at `θ = 1`
(`Environment.necessity_general_one`); sufficiency is `main_physical`. -/
theorem main_physical_iff (E : Environment) (U : AdmissibleUtility) (hu : U.u = E.u) {M : ℝ}
    (hM : 0 < M) (T : (ℝ → ℝ) → Environment.ThreatRule)
    (hT : ∀ V, IsValueFn V → (T V).Admissible V) :
    (∃ V η κ, E.IsGeneralEquilibrium 1 (T V) M V η κ) ↔ 1 < E.β * U.c0 := by
  constructor
  · rintro ⟨V, η, κ, h⟩
    exact Environment.necessity_general_one U hu h
  · intro hact
    obtain ⟨V, η, κ, h, -⟩ := main_physical E U hu hact hM T hT
    exact ⟨V, η, κ, h⟩

end Molico
