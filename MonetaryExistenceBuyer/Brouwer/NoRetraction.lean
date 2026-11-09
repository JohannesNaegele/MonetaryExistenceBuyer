import MonetaryExistenceBuyer.Brouwer.DetPoly
import MonetaryExistenceBuyer.Brouwer.Homotopy
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# No `C¹` retraction of the ball onto the sphere

Suppose `r` is `C¹` near the closed unit ball `B`, takes values in the unit sphere and fixes the
sphere. With `w = r - id` and `f_t = id + t • w`:
* for small `t ≥ 0`, `f_t` is a bijection of `B` with positive Jacobian (`homotopy_small`), so by
  the change of variables formula `vol B = ∫_B det (id + t • Dw)`;
* the right side is a polynomial in `t` (`det_id_add_smul_interp`), so the identity holds for all
  `t`, in particular at `t = 1`;
* but `det (id + Dw) = det Dr = 0` on `B`, since `‖r‖ = 1` forces `Dr x` to take values in
  `(r x)ᗮ`. Contradiction with `vol B > 0`.
-/

open Set Metric MeasureTheory

namespace Molico.Brouwer

/-- If `‖r‖ = 1` near `x`, then `Dr x` is not surjective (its range is orthogonal to `r x`),
so its determinant vanishes. -/
private lemma det_fderiv_eq_zero {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hr : ContDiffOn ℝ 1 r U) (hrS : ∀ y ∈ U, ‖r y‖ = 1) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ U) : (fderiv ℝ r x).det = 0 := by
  have hd : HasFDerivAt r (fderiv ℝ r x) x :=
    ((hr.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have h1 := hd.norm_sq
  have h2 : HasFDerivAt (fun y => ‖r y‖ ^ 2) (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    simp [hrS y hy]
  have h3 := h1.unique h2
  have horth : ∀ v, inner ℝ (r x) (fderiv ℝ r x v) = 0 := by
    intro v
    have := congrArg (fun L => L v) h3
    simpa using this
  by_contra hdet
  have hunit : IsUnit ((fderiv ℝ r x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨v, hv⟩ := ((Module.End.isUnit_iff _).1 hunit).2 (r x)
  have hv' : fderiv ℝ r x v = r x := hv
  have h4 := horth v
  rw [hv', real_inner_self_eq_norm_sq, hrS x hx] at h4
  norm_num at h4

/-- There is no `C¹` retraction of the closed unit ball of `ℝⁿ` onto the unit sphere. -/
theorem no_C1_retraction {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hBU : closedBall 0 1 ⊆ U) {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hr : ContDiffOn ℝ 1 r U) (hrS : ∀ y ∈ U, ‖r y‖ = 1)
    (hrid : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → r x = x) : False := by
  set B : Set (EuclideanSpace ℝ (Fin n)) := closedBall 0 1 with hB
  set w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => r x - x with hw_def
  have hw : ContDiffOn ℝ 1 w U := hr.sub contDiffOn_id
  have hw0 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → w x = 0 := fun x hx => by
    simp [w, hrid x hx]
  have hwB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, x + w x ∈ closedBall 0 1 := by
    intro x hx
    have : x + w x = r x := by simp [w]
    rw [this, mem_closedBall, dist_zero_right, hrS x (hBU hx)]
  obtain ⟨ε, hε, hsmall⟩ := homotopy_small hU hBU hw hw0 hwB
  have hdr : ∀ x ∈ U, HasFDerivAt r (fderiv ℝ r x) x := fun x hx =>
    ((hr.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hdiff : ∀ x ∈ U, HasFDerivAt w (fderiv ℝ w x) x := fun x hx =>
    ((hw.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcont : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hU le_rfl
  have hint : ∀ c : ℝ, IntegrableOn
      (fun x => (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + c • fderiv ℝ w x).det) B := by
    intro c
    refine ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1) ?_
    refine ContinuousLinearMap.continuous_det.comp_continuousOn ?_
    exact continuousOn_const.add ((hcont.mono hBU).const_smul c)
  set F : ℝ → ℝ := fun t =>
    ∫ x in B, (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + t • fderiv ℝ w x).det
    with hF_def
  -- change of variables for small `t`
  have hcov : ∀ t ∈ Icc 0 ε, F t = volume.real B := by
    intro t ht
    obtain ⟨hinj, himg, hpos⟩ := hsmall t ht
    have hf' : ∀ x ∈ B, HasFDerivWithinAt (fun x => x + t • w x)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + t • fderiv ℝ w x) B x := by
      intro x hx
      exact ((hasFDerivAt_id x).add ((hdiff x (hBU hx)).const_smul t)).hasFDerivWithinAt
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall hf'
      hinj (fun _ => (1 : ℝ))
    rw [himg, setIntegral_const] at h
    simp only [smul_eq_mul, mul_one] at h
    rw [h]
    exact setIntegral_congr_fun measurableSet_closedBall (fun x hx => (abs_of_pos (hpos x hx)).symm)
  -- `F` is a polynomial
  obtain ⟨m, c, ℓ, hinterp⟩ := det_id_add_smul_interp (EuclideanSpace ℝ (Fin n))
  set a : Fin m → ℝ := fun j =>
    ∫ x in B, (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + c j • fderiv ℝ w x).det
    with ha_def
  have hF : ∀ t, F t = ∑ j, (ℓ j).eval t * a j := by
    intro t
    simp only [hF_def, ha_def, hinterp _ t]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      exact integral_const_mul _ _
    · intro j _
      exact (hint (c j)).const_mul _
  set Q : Polynomial ℝ := ∑ j, Polynomial.C (a j) * ℓ j - Polynomial.C (volume.real B) with hQ_def
  have hQeval : ∀ t, Q.eval t = F t - volume.real B := by
    intro t
    simp [hQ_def, Polynomial.eval_finsetSum, hF, mul_comm]
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (Set.Icc_infinite hε).mono ?_
    intro t ht
    simp [Polynomial.IsRoot, hQeval, hcov t ht]
  have h1 : F 1 = volume.real B := by
    have := hQeval 1
    rw [hQ, Polynomial.eval_zero] at this
    linarith
  -- but at `t = 1` the integrand is `det (Dr) = 0`
  have h0 : F 1 = 0 := by
    have : EqOn (fun x =>
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) + (1 : ℝ) • fderiv ℝ w x).det)
        (fun _ => (0 : ℝ)) B := by
      intro x hx
      have hwx : fderiv ℝ w x = fderiv ℝ r x - ContinuousLinearMap.id ℝ _ :=
        ((hdr x (hBU hx)).sub (hasFDerivAt_id x)).fderiv
      simp only [hwx, one_smul, add_sub_cancel]
      exact det_fderiv_eq_zero hU hr hrS (hBU hx)
    simp only [hF_def]
    rw [setIntegral_congr_fun measurableSet_closedBall this, integral_zero]
  have hpos : 0 < volume.real B := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  linarith

end Molico.Brouwer
