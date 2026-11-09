import MonetaryExistenceBuyer.Rescaling.Pin
import MonetaryExistenceBuyer.Grid.Entropy

/-!
# Exclusion of normalized limits with asymptotic saturation (§6 of `existence-theorem.tex`)

* `NormalizedLimit.count` — `prop:count` (almost surely finite normalized wealth);
* `NormalizedLimit.coeff` — `lem:coeff` (coefficient bound `C̄ ≤ σ`);
* `adjnorm` — `rem:exact`, eq. `eq:adjnorm` (exact adjoint normalisation, grid identity);
* `neighbour` — `lem:neighbour` (marginal bounds at every optimiser, grid statement);
* `NormalizedLimit.wdf` — `thm:wdf` (dyadic slope decay);
* `NormalizedLimit.inversion` — `lem:inversion` (inverting dyadic decay);
* `NormalizedLimit.splitting` — `thm:splitting` (uniform wealth splitting at large buyer wealth);
* `NormalizedLimit.noplateau` — `thm:noplateau` (every normalized limit exhibits finite-wealth saturation),
  using `lem:entropy` (`Molico.entropy`).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace Molico

variable {P : Primitives}

/-! ### Grid statements -/

/-- `rem:exact`, first identity of `eq:adjnorm` (index form, before dividing by the mesh):
subtracting adjacent Bellman equations, `V(i) - V(i-1) = β ∑_l η_l [H_V(i,l) - H_V(i-1,l)]`. -/
theorem adjnorm {h : ℝ} {N : ℕ} {V η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ}
    (hE : Grid.IsApproxEq P h N V η κ) {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ N) :
    V i - V (i - 1) = P.β * ∑ l ∈ Finset.range (N + 1),
      η l * (Grid.gH P.U.u N V i l - Grid.gH P.U.u N V (i - 1) l) := by
  rw [hE.bellman i hi, hE.bellman (i - 1) (by omega), Grid.gT, Grid.gT, ← mul_sub,
    ← Finset.sum_sub_distrib]
  simp_rw [mul_sub]

/-- `lem:neighbour` (marginal bounds at every optimiser), eqs. `eq:neighbour`, `eq:actualrow`,
in index form (multiply the manuscript's slopes by the normalized mesh `δ_n`). For buyer index
`1 ≤ i ≤ N`, seller index `l`, and any maximiser `j ∈ 𝒥_l(i)`, with landing indices
`B = i - j`, `S = l + j`, `p = H_V(i,l) - H_V(i-1,l)` and `Δ_k = V(l+k) - V(l)`:
* `p ≤ V(B) - V(B-1)` if `B ≥ 1`;
* `p ≤ u(Δ_j) - u(Δ_{j-1}) ≤ u'₋(Δ_{j-1}) (V(S) - V(S-1))` if `j ≥ 1`;
* `V(B+1) - V(B) ≤ p` if `B < N`;
* `u'₋(C) (V(S+1) - V(S)) ≤ p` if `S < N`, where `C` bounds `V` (`C = C_*` on `𝒦_{h,R}`). -/
theorem neighbour (U : AdmissibleUtility) {C : ℝ} {N : ℕ} {V : ℕ → ℝ}
    (hV : Grid.InCone C N V) {i l j : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ N) (hl : l ≤ N)
    (hj : j ∈ Grid.feas N i l) (hmax : Grid.gobj U.u V i l j = Grid.gH U.u N V i l) :
    (1 ≤ i - j →
      Grid.gH U.u N V i l - Grid.gH U.u N V (i - 1) l ≤ V (i - j) - V (i - j - 1)) ∧
    (1 ≤ j →
      Grid.gH U.u N V i l - Grid.gH U.u N V (i - 1) l ≤
        U.u (V (l + j) - V l) - U.u (V (l + (j - 1)) - V l) ∧
      U.u (V (l + j) - V l) - U.u (V (l + (j - 1)) - V l) ≤
        U.marg (V (l + (j - 1)) - V l) * (V (l + j) - V (l + j - 1))) ∧
    (i - j < N →
      V (i - j + 1) - V (i - j) ≤ Grid.gH U.u N V i l - Grid.gH U.u N V (i - 1) l) ∧
    (l + j < N →
      U.marg C * (V (l + j + 1) - V (l + j)) ≤
        Grid.gH U.u N V i l - Grid.gH U.u N V (i - 1) l) := by
  have hmax' : V (i - j) + Grid.sellerSeq U.u V l j = maxConv V (Grid.sellerSeq U.u V l) N (N - l) i := by
    rw [← Grid.gobj_eq]; exact hmax
  obtain ⟨m1, m2, m3, m4⟩ := maxConv_merge hV.incr (Grid.sellerSeq_incr U hV.incr hl) hi1
    (by omega) hj hmax'
  have hjf := hj
  rw [Grid.mem_feas hi hl] at hjf
  -- seller gains are nonnegative and bounded by `C`
  have hΔ0 : ∀ k, l + k ≤ N → 0 ≤ V (l + k) - V l := fun k hk => by
    linarith [hV.incr.le_of_le (show l ≤ l + k by omega) hk]
  have hΔC : ∀ k, l + k ≤ N → V (l + k) - V l ≤ C := fun k hk =>
    (hV.incr.gain_le hV.zero hk).trans (hV.le k (by omega))
  refine ⟨fun h => m1 h, fun h => ⟨m2 h, ?_⟩, fun h => m3 h, fun h => ?_⟩
  · -- secant bound at the lower endpoint
    have hle : V (l + (j - 1)) - V l ≤ V (l + j) - V l := by
      have := hV.incr.le_of_le (show l + (j - 1) ≤ l + j by omega) hjf.2; linarith
    have := U.sub_le_marg_mul (hΔ0 (j - 1) (by omega)) hle
    have e : V (l + j) - V l - (V (l + (j - 1)) - V l) = V (l + j) - V (l + j - 1) := by
      rw [show l + (j - 1) = l + j - 1 by omega]; ring
    rw [e] at this
    exact this
  · -- secant bound at the upper endpoint, then `u'₋(Δ_{j+1}) ≥ u'₋(C)`
    have hQ : j < N - l := by omega
    have h4 := m4 hQ
    simp only [Grid.sellerSeq] at h4
    have hle : V (l + j) - V l ≤ V (l + (j + 1)) - V l := by
      have := hV.incr.le_of_le (show l + j ≤ l + (j + 1) by omega) (by omega); linarith
    have hsec := U.marg_mul_le_sub (hΔ0 j (by omega)) hle
    have e : V (l + (j + 1)) - V l - (V (l + j) - V l) = V (l + j + 1) - V (l + j) := by
      rw [show l + (j + 1) = l + j + 1 by omega]; ring
    rw [e] at hsec
    have hinc : 0 ≤ V (l + j + 1) - V (l + j) := by
      linarith [hV.incr.mono (l + j) h]
    have hmarg : U.marg C ≤ U.marg (V (l + (j + 1)) - V l) :=
      U.marg_antitoneOn (hΔ0 (j + 1) (by omega)) ((hΔ0 (j + 1) (by omega)).trans
        (hΔC (j + 1) (by omega))) (hΔC (j + 1) (by omega))
    calc U.marg C * (V (l + j + 1) - V (l + j))
        ≤ U.marg (V (l + (j + 1)) - V l) * (V (l + j + 1) - V (l + j)) :=
          mul_le_mul_of_nonneg_right hmarg hinc
      _ ≤ _ := hsec
      _ ≤ _ := h4

/-! ### Normalized grid quantities -/

namespace NormalizedLimit

variable {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)

/-- `N_n` along the subsequence. -/
def Nn (n : ℕ) : ℕ := S.N (NL.φ n)

/-- `δ_n` along the subsequence. -/
def δ' (n : ℕ) : ℝ := S.δn a (NL.φ n)

/-- The normalized grid slope `v_{n,i} = (W_n(iδ_n) - W_n((i-1)δ_n))/δ_n`. -/
def slope (n i : ℕ) : ℝ := (S.V (NL.φ n) i - S.V (NL.φ n) (i - 1)) / NL.δ' n

/-- The optimal transfer indices `𝒥_{n,l}(i)`. -/
def argmaxSet (n i l : ℕ) : Finset ℕ :=
  (Grid.feas (NL.Nn n) i l).filter fun j =>
    Grid.gobj P.U.u (S.V (NL.φ n)) i l j = Grid.gH P.U.u (NL.Nn n) (S.V (NL.φ n)) i l

/-- The splitting seller set `E_{n,i}` of `thm:splitting`: sellers `l δ_n ∈ K` with whom every
optimal trade leaves the buyer a wealth share `(i-j)δ_n/(iδ_n + lδ_n) ∈ [ω, 1-ω]`. -/
def splitSet (ω : ℝ) (K : Set ℝ) (n i : ℕ) : Finset ℕ :=
  (Finset.range (NL.Nn n + 1)).filter fun l =>
    (l : ℝ) * NL.δ' n ∈ K ∧
      ∀ j ∈ NL.argmaxSet n i l, ((i - j : ℕ) : ℝ) / ((i : ℝ) + l) ∈ Icc ω (1 - ω)

/-- The mass `η̃_n(E)` of a set of seller indices under the normalized grid law. -/
def lawMass (n : ℕ) (E : Finset ℕ) : ℝ := ∑ l ∈ E, S.η (NL.φ n) l

/-- `def:coefficient`: the coefficient average `C̄ = ∫ u'₋(L - y) dα`. -/
def Cbar : ℝ := ∫ p, P.U.marg (NL.Lsup - p.2) ∂NL.α

end NormalizedLimit

end Molico
