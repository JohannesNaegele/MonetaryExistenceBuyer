import MonetaryExistenceBuyer.General.Bargain
import MonetaryExistenceBuyer.General.ValueBound

/-!
# The uniform value bound `V ≤ ū/σ` (`lem:buyerreduction`, last clause)

Under `ass:utility`, every increasing equilibrium value function satisfies `0 ≤ V(m) ≤ ū/σ` for
all `m ≥ 0`, where `σ = 1/β - 1 = r/π` (`def:effectivediscount`). Indeed, the buyer's gain in
`eq:HT` is at most `ū`, so `H_V(m, s) ≤ ū + sup V`, and the fixed-point equation `V = T_η V`
gives `sup V ≤ β (ū + sup V)`, i.e. `sup V ≤ β ū/(1 - β) = ū/σ`.

* `IsEquilibrium.value_le_ubar_div_σ` — the buyer-takes-all simplified model (`def:eq`);
* `Environment.IsGeneralEquilibrium.value_le_ubar_div_σ` — the general model with `θ = 1` and an
  admissible value function, via `buyerreduction_bellman` (`eq:buyerflow`).

The lower bound `0 ≤ V` is `IsValueFn.nonneg` (`rem:bellmandomain`).
-/

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Molico

/-- `∫ H_V(m, s) dη(s) ≤ ū + sup V` for a probability law `η` on `ℝ₊`. No integrability of
`s ↦ H_V(m, s)` is needed: the bound follows from the a.e. bound `0 ≤ H_V ≤ ū + sup V`. -/
private lemma integral_bellH_le (U : AdmissibleUtility) {V : ℝ → ℝ} (hV : IsValueFn V)
    {η : Measure ℝ} [IsProbabilityMeasure η] (hη : η (Iio 0) = 0) {m : ℝ} (hm : 0 ≤ m) :
    ∫ s, bellH U.u V m s ∂η ≤ U.ubar + hV.sup := by
  have hae : ∀ᵐ s ∂η, 0 ≤ s := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hη] with s hs
    simpa using hs
  have hb : ∀ᵐ s ∂η, ‖bellH U.u V m s‖ ≤ U.ubar + hV.sup := by
    filter_upwards [hae] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (bellH_nonneg U hV hm hs)]
    exact bellH_le_const U hV hm hs
  have h := norm_integral_le_of_norm_le_const hb
  rw [probReal_univ, mul_one] at h
  exact (le_abs_self _).trans h

/-- `sup V ≤ c` if `V ≤ c` on `[0, ∞)`. -/
private lemma IsValueFn.sup_le {V : ℝ → ℝ} (hV : IsValueFn V) {c : ℝ}
    (hc : ∀ x, 0 ≤ x → V x ≤ c) : hV.sup ≤ c :=
  csSup_le ⟨V 0, 0, self_mem_Ici, rfl⟩ (by rintro _ ⟨x, hx, rfl⟩; exact hc x hx)

/-- The arithmetic of the bound: `s ≤ β (ū + s)` with `0 < β < 1` gives `s ≤ ū/(1/β - 1)`. -/
private lemma le_div_of_le_mul_add {β s ubar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (h : s ≤ β * (ubar + s)) : s ≤ ubar / (1 / β - 1) := by
  have hσ : 0 < 1 / β - 1 := sub_pos.2 (one_lt_one_div hβ0 hβ1)
  rw [le_div_iff₀ hσ]
  have h1 : s / β ≤ ubar + s := (div_le_iff₀ hβ0).2 (by linarith)
  calc s * (1 / β - 1) = s / β - s := by ring
    _ ≤ ubar := by linarith

/-- The fixed-point inequality `sup V ≤ β (ū + sup V)` for a solution of `V = T_η V` on
`[0, ∞)` with `η ∈ 𝒫(ℝ₊)`. -/
private lemma sup_le_of_bellman (U : AdmissibleUtility) {β : ℝ} (hβ0 : 0 < β) {V : ℝ → ℝ}
    (hV : IsValueFn V) {η : Measure ℝ} [IsProbabilityMeasure η] (hη : η (Iio 0) = 0)
    (hbell : ∀ m, 0 ≤ m → V m = bellT U.u β η V m) : hV.sup ≤ β * (U.ubar + hV.sup) := by
  refine hV.sup_le fun x hx => ?_
  rw [hbell x hx]
  unfold bellT
  exact mul_le_mul_of_nonneg_left (integral_bellH_le U hV hη hx) hβ0.le

/-- `lem:buyerreduction`, last clause (buyer-takes-all simplified form `def:eq`): `V ≤ ū/σ` on
`[0,∞)` with `σ = 1/β - 1`. -/
theorem IsEquilibrium.value_le_ubar_div_σ (U : AdmissibleUtility) {β M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {V : ℝ → ℝ} {η : Measure ℝ} {Γ : Measure (ℝ × ℝ × ℝ)}
    (h : IsEquilibrium U.u β M V η Γ) {m : ℝ} (hm : 0 ≤ m) : V m ≤ U.ubar / (1 / β - 1) := by
  have := h.isProb_η
  exact (h.value.le_sup hm).trans
    (le_div_of_le_mul_add hβ0 hβ1 (sup_le_of_bellman U hβ0 h.value h.η_nonneg h.bellman))

/-- `lem:buyerreduction`, last clause (general model, `θ = 1`, admissible value function):
`V ≤ ū/σ` on `[0,∞)` with `σ = r/π = 1/β - 1`. -/
theorem Environment.IsGeneralEquilibrium.value_le_ubar_div_σ (E : Environment)
    (U : AdmissibleUtility) (hu : U.u = E.u) {T : ThreatRule} {M : ℝ} {V : ℝ → ℝ}
    {η : Measure ℝ} {κ : Kernel (ℝ × ℝ) (ℝ × ℝ)} (hV : IsValueFn V)
    (h : E.IsGeneralEquilibrium 1 T M V η κ) {m : ℝ} (hm : 0 ≤ m) : V m ≤ U.ubar / E.σ := by
  have := h.isProb_η
  have := h.markov
  -- `eq:buyerflow`: the general Bellman equation reduces to `V = T_η V` with `u = U ∘ K⁻¹`.
  have hbell : ∀ x, 0 ≤ x → V x = bellT U.u E.β η V x := fun x hx => by
    rw [hu]
    exact (E.buyerreduction_bellman T hV h.η_nonneg h.support hx).1 (h.bellman x hx)
  rw [E.σ_eq]
  exact (hV.le_sup hm).trans
    (le_div_of_le_mul_add E.β_pos E.β_lt_one (sup_le_of_bellman U E.β_pos hV h.η_nonneg hbell))

end Molico
