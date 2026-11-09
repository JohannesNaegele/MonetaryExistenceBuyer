import MonetaryExistenceBuyer.General.Reinsert
import MonetaryExistenceBuyer.General.TransferKernel

/-!
# Recovering physical output (`rem:physicaloutput`)

An equilibrium of the buyer-takes-all specialization (`def:eq`) for the composite utility
`u = U ∘ K⁻¹` yields a stationary monetary equilibrium in relaxed strategies of the general model
(`def:generaleq`, `θ = 1`): disintegrate `Γ` into a transfer kernel (`exists_transfer_kernel`) and
reinsert physical output `q = K⁻¹(Δ_V(s,d))` (`physicaloutput_of_kernel`).
-/

open Set Filter Topology MeasureTheory ProbabilityTheory

noncomputable section

namespace Molico.Environment

variable (E : Environment)

/-- `rem:physicaloutput`: an equilibrium `(V, η, Γ)` in the sense of `def:eq` for the composite
utility `u = U ∘ K⁻¹` and `β = π/(r+π)` yields a stationary monetary equilibrium in relaxed
strategies of `def:generaleq` for the original primitives `(U, K)` with `θ = 1` (for every
admissible threat-point rule), by sending `(b, s, d)` to `(b, s, K⁻¹(Δ_V(s,d)), d)`. If `Γ` is
deterministic, so is the reconstructed kernel. -/
theorem physicaloutput (T : ThreatRule) {M : ℝ} {V : ℝ → ℝ} {η : Measure ℝ}
    {Γ : Measure (ℝ × ℝ × ℝ)} (h : IsEquilibrium E.u E.β M V η Γ) (hT : T.Admissible V) :
    ∃ κ : Kernel (ℝ × ℝ) (ℝ × ℝ), E.IsGeneralEquilibrium 1 T M V η κ ∧
      (IsDeterministic Γ → IsDeterministicKernel κ) := by
  obtain ⟨ν, hν, hrep, hsupp, hdet⟩ := exists_transfer_kernel E.continuousOn_u E.u_monotoneOn h
  obtain ⟨κ, hκ, hdk⟩ := E.physicaloutput_of_kernel T h hT ν hrep hsupp
  exact ⟨κ, hκ, fun hΓ => hdk (hdet hΓ)⟩

end Molico.Environment
