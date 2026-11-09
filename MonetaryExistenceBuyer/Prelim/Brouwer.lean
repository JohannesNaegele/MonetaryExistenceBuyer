import MonetaryExistenceBuyer.Brouwer.Ball
import MonetaryExistenceBuyer.Brouwer.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic

/-!
# Brouwer's fixed point theorem and the continuation principle

`thm:approx` in `existence-theorem.tex` uses the *continuation principle* (`lem:continuation`):
if a homotopy is admissible at level `ϱ` of a gauge `g` (`def:homotopy`) and `H_1` has no fixed
point in `{g ≤ ϱ}`, then `H_0` has one in `{g > ϱ}`. As in the manuscript, `continuation` is
derived directly from Brouwer's fixed point theorem on the compact convex set `[0,1] × D`, applied
to the map `F(t, x) = (p(t + ϱ - g(x)), H_t(x))` with the clamp `p(r) = min{1, max{0, r}}`.
Brouwer's theorem (`brouwer`) is not in Mathlib; it is proved in `MonetaryExistenceBuyer/Brouwer/`
(analytic proof via the `C¹` no-retraction theorem) and transferred here from the unit ball of
`ℝⁿ` to an arbitrary compact convex set.
-/

open Set

namespace Molico

/-- **Brouwer's fixed point theorem** for a nonempty compact convex subset of a
finite-dimensional real normed space. Reduced to `Brouwer.brouwer_ball` by a linear chart
`E ≃ ℝⁿ`, the nearest-point retraction onto the image of `D`, and rescaling. -/
theorem brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D : Set E} (hDc : IsCompact D) (hDconv : Convex ℝ D) (hDne : D.Nonempty) {f : E → E}
    (hf : ContinuousOn f D) (hfD : MapsTo f D D) : ∃ x ∈ D, f x = x := by
  -- Transport to `ℝⁿ` with its Euclidean structure.
  set n := Module.finrank ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  set D' : Set (EuclideanSpace ℝ (Fin n)) := e '' D with hD'def
  have hD'c : IsCompact D' := hDc.image e.continuous
  have hD'conv : Convex ℝ D' := hDconv.linear_image (e.toLinearEquiv.toLinearMap)
  have hD'ne : D'.Nonempty := hDne.image _
  -- Nearest-point retraction onto `D'`.
  obtain ⟨P, hPc, hPD, hPfix⟩ := Brouwer.exists_retraction_convex hD'c.isClosed hD'conv hD'ne
  have hmemD : ∀ y, e.symm (P y) ∈ D := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hPD y
    rw [← hxy, e.symm_apply_apply]
    exact hx
  -- `D'` lies in a ball of radius `R > 0`.
  obtain ⟨R0, hR0⟩ := hD'c.isBounded.subset_closedBall 0
  set R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hD'R : D' ⊆ Metric.closedBall 0 R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  -- The rescaled self-map of the unit ball.
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun y => R⁻¹ • e (f (e.symm (P (R • y))))
  have hgc : ContinuousOn g (Metric.closedBall 0 1) := by
    have hin : ContinuousOn (fun y => f (e.symm (P (R • y)))) univ :=
      hf.comp (e.symm.continuous.comp (hPc.comp (continuous_const_smul R))).continuousOn
        (fun y _ => hmemD _)
    exact ((continuous_const_smul R⁻¹).comp_continuousOn
      (e.continuous.comp_continuousOn hin)).mono (subset_univ _)
  have hgB : MapsTo g (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro y _
    have h1 : e (f (e.symm (P (R • y)))) ∈ D' := ⟨_, hfD (hmemD _), rfl⟩
    have h2 := hD'R h1
    rw [mem_closedBall_zero_iff] at h2 ⊢
    simp only [g, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hRpos]
    rw [inv_mul_le_iff₀ hRpos, mul_one]
    exact h2
  obtain ⟨y, -, hy⟩ := Brouwer.brouwer_ball hgc hgB
  -- Undo the rescaling: `z = R • y` is a fixed point of `e ∘ f ∘ e.symm ∘ P`.
  set z := R • y with hzdef
  have hz : e (f (e.symm (P z))) = z := by
    have h : R • g y = R • y := by rw [hy]
    simpa [g, smul_smul, mul_inv_cancel₀ hRpos.ne'] using h
  have hzD' : z ∈ D' := by
    rw [← hz]
    exact ⟨_, hfD (hmemD z), rfl⟩
  have hPz : P z = z := hPfix z hzD'
  refine ⟨e.symm z, ?_, ?_⟩
  · rw [← hPz]
    exact hmemD z
  · rw [hPz] at hz
    have h := congrArg e.symm hz
    simpa using h

/-- **Continuation principle** (`lem:continuation`).

Let `D` be a nonempty compact convex set and `H : [0,1] × D → D` a homotopy. Let `g` be a
continuous gauge and `ϱ` a level such that
* no map `H t` has a fixed point on the level set `{g = ϱ}` (admissibility), and
* `H 1` has no fixed point in `{g ≤ ϱ}`.

Then `H 0` has a fixed point in `{g > ϱ}`. -/
theorem continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D : Set E} (hDc : IsCompact D) (hDconv : Convex ℝ D) (hDne : D.Nonempty)
    {H : ℝ → E → E} (hH : ContinuousOn (fun p : ℝ × E => H p.1 p.2) (Icc 0 1 ×ˢ D))
    (hHD : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (H t) D D) {g : E → ℝ} (hg : ContinuousOn g D) {ϱ : ℝ}
    (hadm : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ D, H t x = x → g x ≠ ϱ)
    (hone : ∀ x ∈ D, H 1 x = x → ϱ < g x) :
    ∃ x ∈ D, H 0 x = x ∧ ϱ < g x := by
  -- The clamp `p r = min 1 (max 0 r)` onto `[0,1]`.
  let p : ℝ → ℝ := fun r => min 1 (max 0 r)
  have hp_mem : ∀ r, p r ∈ Icc (0:ℝ) 1 := fun r =>
    ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  -- `K = [0,1] × D` is nonempty, compact and convex in the finite-dimensional space `ℝ × E`.
  set K : Set (ℝ × E) := Icc (0:ℝ) 1 ×ˢ D with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod hDc
  have hKconv : Convex ℝ K := (convex_Icc 0 1).prod hDconv
  have hKne : K.Nonempty := (nonempty_Icc.2 zero_le_one).prod hDne
  -- The map `F (t, x) = (p (t + ϱ - g x), H t x)`.
  let F : ℝ × E → ℝ × E := fun q => (p (q.1 + ϱ - g q.2), H q.1 q.2)
  have hFc : ContinuousOn F K := by
    refine ContinuousOn.prodMk ?_ hH
    refine (continuous_const.min (continuous_const.max continuous_id)).comp_continuousOn ?_
    exact (continuousOn_fst.add continuousOn_const).sub
      (hg.comp continuousOn_snd fun q hq => hq.2)
  have hFK : MapsTo F K K := fun q hq => ⟨hp_mem _, hHD q.1 hq.1 hq.2⟩
  obtain ⟨⟨t, x⟩, ⟨ht, hx⟩, hfix⟩ := brouwer hKc hKconv hKne hFc hFK
  rw [Prod.ext_iff] at hfix
  obtain ⟨hteq, hHfix⟩ := hfix
  simp only [F, p] at hteq hHfix
  -- `hteq : min 1 (max 0 (t + ϱ - g x)) = t`, `hHfix : H t x = x`.
  have hne : g x ≠ ϱ := hadm t ht x hx hHfix
  -- `t = 0`: the cases `0 < t < 1` and `t = 1` are excluded by admissibility and by `hone`.
  have ht0 : t = 0 := by
    rcases min_cases (1:ℝ) (max 0 (t + ϱ - g x)) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases max_cases (0:ℝ) (t + ϱ - g x) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
    · linarith
    · -- `t = 1` and `g x ≤ ϱ`
      have ht1 : t = 1 := by linarith
      subst ht1
      exact absurd (hone x hx hHfix) (not_lt.2 (by linarith))
    · linarith
    · -- `0 < t < 1` and `g x = ϱ`
      exact absurd (by linarith : g x = ϱ) hne
  subst ht0
  -- `t = 0` gives `ϱ ≤ g x`, strict by admissibility.
  refine ⟨x, hx, hHfix, lt_of_le_of_ne ?_ hne.symm⟩
  rcases min_cases (1:ℝ) (max 0 (0 + ϱ - g x)) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases max_cases (0:ℝ) (0 + ϱ - g x) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith

end Molico
