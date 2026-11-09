import MonetaryExistenceBuyer.Grid.Defs

/-!
# Every grid slope is positive (`lem:slopepos`)

A nonzero grid Bellman fixed point is strictly increasing on all of `𝒳`: no nontrivial monetary
equilibrium exhibits value satiation on the truncated state space.
-/

open Finset

noncomputable section

namespace Molico

/-- `lem:slopepos`: if `V = T_η V` on the grid, `V` is nondecreasing and discretely concave with
`V(0) = 0`, and `V ≢ 0`, then every grid slope `a_i = (V(ih) - V((i-1)h))/h` is positive. -/
theorem slopepos (U : AdmissibleUtility) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {N : ℕ}
    {V η : ℕ → ℝ} (hV : IncrSeq V N) (hV0 : V 0 = 0) (hη0 : ∀ l, 0 ≤ η l)
    (hη1 : ∑ l ∈ range (N + 1), η l = 1) (hbell : ∀ m ≤ N, V m = Grid.gT U.u β N η V m)
    (hne : ∃ i ≤ N, V i ≠ 0) : ∀ i, i < N → V i < V (i + 1) := by
  classical
  by_contra hcon
  push Not at hcon
  -- some slope vanishes; take the least such index `k0` (the paper's `i₀ - 1`)
  have hex : ∃ k, k < N ∧ V (k + 1) = V k := by
    obtain ⟨i, hi, hle⟩ := hcon
    exact ⟨i, hi, le_antisymm hle (hV.mono i hi)⟩
  obtain ⟨k0, ⟨hk0N, hk0eq⟩, hmin⟩ : ∃ k0, (k0 < N ∧ V (k0 + 1) = V k0) ∧
      ∀ k < k0, ¬ (k < N ∧ V (k + 1) = V k) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  -- all later slopes vanish: `V` is constant on `[k0, N]`
  have hflat : ∀ k, k0 ≤ k → k ≤ N → V k = V k0 := by
    intro k hk hkN
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      have h1 := hV.step_anti (x := k0) (y := n) hn (by omega)
      have h2 := hV.mono n (by omega)
      rw [← ih (by omega)]
      linarith
  -- every seller index charged by `η` lies in `[k0, N]`
  have hsupp : ∀ l ≤ N, η l ≠ 0 → k0 ≤ l := by
    intro l hl hηl
    -- Step 1: subtract the Bellman equations at `k0 + 1` and `k0`
    have hdiff : ∑ l ∈ range (N + 1),
        η l * (Grid.gH U.u N V (k0 + 1) l - Grid.gH U.u N V k0 l) = 0 := by
      have e1 := hbell (k0 + 1) (by omega)
      have e2 := hbell k0 (by omega)
      unfold Grid.gT at e1 e2
      have : β * ∑ l ∈ range (N + 1),
          η l * (Grid.gH U.u N V (k0 + 1) l - Grid.gH U.u N V k0 l) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun l' hl' => mul_nonneg (hη0 l')
      (sub_nonneg.2 (Grid.gH_mono U hV hk0N (by simp at hl'; omega))))).1 hdiff l
      (by simp; omega)
    have hgeq : Grid.gH U.u N V (k0 + 1) l = Grid.gH U.u N V k0 l := by
      rcases mul_eq_zero.1 hterm with h | h
      · exact absurd h hηl
      · linarith
    -- Step 2: every maximiser at buyer index `k0` is the zero transfer
    obtain ⟨j, hj, hjmax⟩ := Grid.exists_gH_eq U (V := V) (show k0 ≤ N by omega) hl
    rw [Grid.mem_feas (by omega) hl] at hj
    have hj' : j ∈ Grid.feas N (k0 + 1) l := by rw [Grid.mem_feas (by omega) hl]; omega
    have hge := Grid.gobj_le_gH U (V := V) (by omega) hl hj'
    unfold Grid.gobj at hge hjmax
    have hj0 : j = 0 := by
      have hstep : V (k0 - j + 1) = V (k0 - j) := by
        have := hV.mono (k0 - j) (by omega)
        rw [show k0 + 1 - j = k0 - j + 1 by omega] at hge
        linarith
      by_contra hjne
      exact hmin (k0 - j) (by omega) ⟨by omega, hstep⟩
    subst hj0
    rw [Nat.add_zero, sub_self, U.u_zero, zero_add, Nat.sub_zero] at hjmax
    -- Step 3: the unit transfer at buyer index `k0 + 1` forces a vanishing slope at `l`
    by_contra hlt
    push Not at hlt
    have hj1 : 1 ∈ Grid.feas N (k0 + 1) l := by rw [Grid.mem_feas (by omega) hl]; omega
    have hge1 := Grid.gobj_le_gH U (V := V) (by omega) hl hj1
    unfold Grid.gobj at hge1
    rw [Nat.add_sub_cancel] at hge1
    have hpos : 0 < V (l + 1) - V l := by
      rcases lt_or_eq_of_le (hV.mono l (by omega)) with h | h
      · linarith
      · exact absurd ⟨by omega, h.symm⟩ (hmin l hlt)
    linarith [U.pos hpos]
  -- Step 4: on the support of `η`, no trade gains anything: `H_V(m, l) = V m`
  have hgH : ∀ m ≤ N, ∀ l ≤ N, η l ≠ 0 → Grid.gH U.u N V m l = V m := by
    intro m hm l hl hηl
    have hkl := hsupp l hl hηl
    apply le_antisymm
    · obtain ⟨j, hj, hjmax⟩ := Grid.exists_gH_eq U (V := V) hm hl
      rw [Grid.mem_feas hm hl] at hj
      rw [← hjmax]
      unfold Grid.gobj
      rw [hflat (l + j) (by omega) hj.2, hflat l hkl hl, sub_self, U.u_zero, zero_add]
      exact hV.le_of_le (by omega) hm
    · exact Grid.le_gH U hV0 hm hl
  -- Step 5: `V = β V`, so `V ≡ 0`
  obtain ⟨i, hi, hVi⟩ := hne
  apply hVi
  have e := hbell i hi
  unfold Grid.gT at e
  have hs : ∑ l ∈ range (N + 1), η l * Grid.gH U.u N V i l = V i := by
    rw [show ∑ l ∈ range (N + 1), η l * Grid.gH U.u N V i l =
        ∑ l ∈ range (N + 1), η l * V i from ?_]
    · rw [← Finset.sum_mul, hη1, one_mul]
    · apply Finset.sum_congr rfl
      intro l hl
      by_cases h : η l = 0
      · simp [h]
      · rw [hgH i hi l (by simp at hl; omega) h]
  rw [hs] at e
  have : (1 - β) * V i = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact h

end Molico
