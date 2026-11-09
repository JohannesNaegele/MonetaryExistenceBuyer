import MonetaryExistenceBuyer.Brouwer.Approx
import MonetaryExistenceBuyer.Brouwer.NoRetraction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Brouwer's fixed point theorem for the closed unit ball of `ℝⁿ`

If `f` has no fixed point, `‖f x - x‖ ≥ ε > 0` on the ball. A `C¹` approximation `q` of `f`
(`exists_contDiff_near`, rescaled to map the ball into itself) still has no fixed point near the
ball. Following the ray from `q x` through `x` to the unit sphere gives
`r x = x + λ(x) (x - q x)`, with `λ ≥ 0` the root of `‖x + λ u‖ = 1`, `u = x - q x`:
`λ = (-⟪x,u⟫ + √(⟪x,u⟫² + ‖u‖²(1 - ‖x‖²))) / ‖u‖²`. On the sphere `⟪x,u⟫ ≥ ‖u‖²/2 > 0`, so the
discriminant is positive near the ball, `r` is `C¹` there, and `r` fixes the sphere. This
contradicts `no_C1_retraction`.
-/

open Set Metric InnerProductSpace

namespace Molico.Brouwer

/-- A `C¹` map `q` with `‖q x‖ < 1` and `q x ≠ x` on the closed unit ball cannot exist: the ray
from `q x` through `x` gives a `C¹` retraction of a neighbourhood of the ball onto the sphere. -/
private lemma no_fixfree_C1 {n : ℕ} {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hq : ContDiff ℝ 1 q)
    (hqB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ‖q x‖ < 1)
    (hfix : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, q x ≠ x) : False := by
  obtain ⟨u, hu_eq⟩ : ∃ u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      u = fun x => x - q x := ⟨_, rfl⟩
  obtain ⟨a, ha_eq⟩ : ∃ a : EuclideanSpace ℝ (Fin n) → ℝ, a = fun x => ⟪x, u x⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨N, hN_eq⟩ : ∃ N : EuclideanSpace ℝ (Fin n) → ℝ, N = fun x => ‖u x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD_eq⟩ : ∃ D : EuclideanSpace ℝ (Fin n) → ℝ,
      D = fun x => a x ^ 2 + N x * (1 - ‖x‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨lam, hlam_eq⟩ : ∃ lam : EuclideanSpace ℝ (Fin n) → ℝ,
      lam = fun x => (-a x + √(D x)) / N x := ⟨_, rfl⟩
  obtain ⟨r, hr_eq⟩ : ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      r = fun x => x + lam x • u x := ⟨_, rfl⟩
  have hu : ContDiff ℝ 1 u := by rw [hu_eq]; exact contDiff_id.sub hq
  have ha : ContDiff ℝ 1 a := by rw [ha_eq]; exact contDiff_id.inner ℝ hu
  have hN : ContDiff ℝ 1 N := by rw [hN_eq]; exact hu.norm_sq ℝ
  have hD : ContDiff ℝ 1 D := by
    rw [hD_eq]; exact (ha.pow 2).add (hN.mul (contDiff_const.sub (contDiff_norm_sq ℝ)))
  let U : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < N x} ∩ {x | 0 < D x}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hN.continuous).inter (isOpen_lt continuous_const hD.continuous)
  -- `a > 0` on the unit sphere
  have ha_sph : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → 0 < a x := by
    intro x hx
    have hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      mem_closedBall_zero_iff.2 hx.le
    have h1 : a x = 1 - ⟪x, q x⟫_ℝ := by
      rw [ha_eq, hu_eq]
      simp only [inner_sub_right, real_inner_self_eq_norm_sq, hx]
      norm_num
    have h2 : ⟪x, q x⟫_ℝ ≤ ‖q x‖ := by simpa [hx] using real_inner_le_norm x (q x)
    have := hqB x hxB
    linarith
  have hBU : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ U := by
    intro x hx
    have hux : u x ≠ 0 := by rw [hu_eq]; exact sub_ne_zero.2 (hfix x hx).symm
    have hNx : 0 < N x := by rw [hN_eq]; exact pow_pos (norm_pos_iff.2 hux) 2
    refine ⟨hNx, ?_⟩
    show 0 < D x
    rw [mem_closedBall_zero_iff] at hx
    rw [hD_eq]
    rcases hx.lt_or_eq with hlt | heq
    · have h1 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      have h2 : 0 < N x * (1 - ‖x‖ ^ 2) := mul_pos hNx h1
      have h3 : 0 ≤ a x ^ 2 := sq_nonneg _
      show 0 < a x ^ 2 + N x * (1 - ‖x‖ ^ 2)
      linarith
    · have h1 := ha_sph x heq
      show 0 < a x ^ 2 + N x * (1 - ‖x‖ ^ 2)
      rw [heq]; nlinarith
  have hr : ContDiffOn ℝ 1 r U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    have hlam : ContDiffAt ℝ 1 lam x := by
      rw [hlam_eq]
      exact (ha.contDiffAt.neg.add (hD.contDiffAt.sqrt hx.2.ne')).div hN.contDiffAt hx.1.ne'
    rw [hr_eq]
    exact contDiffAt_id.add (hlam.smul hu.contDiffAt)
  have hrS : ∀ y ∈ U, ‖r y‖ = 1 := by
    intro y hy
    have hNy : 0 < N y := hy.1
    have hDy : 0 < D y := hy.2
    have hs : √(D y) ^ 2 = D y := Real.sq_sqrt hDy.le
    have hL : lam y * N y = -a y + √(D y) := by
      rw [hlam_eq]; exact div_mul_cancel₀ _ hNy.ne'
    have hDy' : D y = a y ^ 2 + N y * (1 - ‖y‖ ^ 2) := by rw [hD_eq]
    have hay : ⟪y, u y⟫_ℝ = a y := by rw [ha_eq]
    have hNy' : ‖u y‖ ^ 2 = N y := by rw [hN_eq]
    have hsq : ‖r y‖ ^ 2 = 1 := by
      rw [hr_eq]
      simp only
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        hay, hNy']
      apply mul_left_cancel₀ hNy.ne'
      linear_combination (lam y * N y + a y + √(D y)) * hL + hs + hDy'
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq
  have hrid : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → r x = x := by
    intro x hx
    have hDx : D x = a x ^ 2 := by rw [hD_eq]; simp only [hx]; ring
    have hlam0 : lam x = 0 := by
      rw [hlam_eq]
      simp only
      rw [hDx, Real.sqrt_sq (ha_sph x hx).le]
      simp
    rw [hr_eq]
    simp [hlam0]
  exact no_C1_retraction hUo hBU hr hrS hrid

/-- Brouwer's fixed point theorem for the closed unit ball of `ℝⁿ`. -/
theorem brouwer_ball {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContinuousOn f (closedBall 0 1)) (hfB : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x = x := by
  by_contra hcon'
  have hcon : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x ≠ x :=
    fun x hx h => hcon' ⟨x, hx, h⟩
  have hBc : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_closedBall 0 1
  have hBne : (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨x0, hx0B, hmin⟩ := hBc.exists_isMinOn hBne
    (f := fun x => ‖f x - x‖) (hf.sub continuousOn_id).norm
  have hε : 0 < ‖f x0 - x0‖ := norm_pos_iff.2 (sub_ne_zero.2 (hcon x0 hx0B))
  set ε := ‖f x0 - x0‖ with hε_def
  set δ := ε / 4 with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨p, hp, hpf⟩ := exists_contDiff_near hBc hf hδ
  set c : ℝ := (1 + δ)⁻¹ with hc_def
  have hc1 : c * (1 + δ) = 1 := inv_mul_cancel₀ (by positivity)
  have hc0 : 0 < c := by positivity
  have hcl : c < 1 := by nlinarith
  -- bound on `‖p x‖` on the ball
  have hpB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ‖p x‖ < 1 + δ := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hfB hx)
    have h2 := norm_sub_norm_le (p x) (f x)
    linarith [hpf x hx]
  refine no_fixfree_C1 (q := fun x => c • p x) (hp.const_smul c) ?_ ?_
  · intro x hx
    show ‖c • p x‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    have := hpB x hx
    nlinarith [norm_nonneg (p x)]
  · intro x hx heq
    have heq' : c • p x = x := heq
    have hmx : ε ≤ ‖f x - x‖ := (isMinOn_iff.1 hmin) x hx
    have hpq : ‖p x - c • p x‖ < δ := by
      have : p x - c • p x = (1 - c) • p x := by rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have := hpB x hx
      nlinarith [norm_nonneg (p x)]
    have hsplit : f x - x = (f x - p x) + (p x - c • p x) := by rw [heq']; abel
    have h3 : ‖f x - x‖ ≤ ‖f x - p x‖ + ‖p x - c • p x‖ := by
      rw [hsplit]; exact norm_add_le _ _
    have h4 : ‖f x - p x‖ < δ := by rw [norm_sub_rev]; exact hpf x hx
    linarith

end Molico.Brouwer
