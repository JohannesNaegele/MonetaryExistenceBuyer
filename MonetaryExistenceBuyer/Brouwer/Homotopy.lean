import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Small perturbations of the identity on the unit ball

Let `w` be `C¹` near the closed unit ball `B`, vanishing on the unit sphere, with `x + w x ∈ B`
for `x ∈ B`. Then for all small `t ≥ 0` the map `f_t x = x + t • w x` is injective on `B`,
maps `B` onto `B`, and has positive Jacobian determinant on `B`.

Injectivity: `w` is Lipschitz on `B`. Onto: `f_t` fixes the sphere, maps the open ball into the
open ball (by injectivity), is open there (inverse function theorem), and its image of `B` is
compact; connectedness of the open ball concludes.
-/

open Set Metric

namespace Molico.Brouwer

/-- `f_t = id + t • w` is a bijection of the closed unit ball with positive Jacobian, for all
small `t ≥ 0`. -/
theorem homotopy_small {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hBU : closedBall 0 1 ⊆ U) {w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hw : ContDiffOn ℝ 1 w U) (hw0 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → w x = 0)
    (hwB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, x + w x ∈ closedBall 0 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc 0 ε,
      InjOn (fun x => x + t • w x) (closedBall 0 1) ∧
      (fun x => x + t • w x) '' closedBall 0 1 = closedBall 0 1 ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        0 < (ContinuousLinearMap.id ℝ _ + t • fderiv ℝ w x).det := by
  -- uniform bound on the derivative over the closed ball
  have hcontD : ContinuousOn (fderiv ℝ w) U := hw.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).exists_bound_of_continuousOn
    (hcontD.mono hBU)
  set L : ℝ := max C 0 + 1 with hL
  have hLpos : 0 < L := by positivity
  have hDL : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ‖fderiv ℝ w x‖ ≤ L := fun x hx =>
    (hC x hx).trans (by rw [hL]; linarith [le_max_left C 0])
  have hdiff : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, DifferentiableAt ℝ w x :=
    fun x hx => (hw.contDiffAt (hU.mem_nhds (hBU hx))).differentiableAt one_ne_zero
  have hLip : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, ‖w y - w x‖ ≤ L * ‖y - x‖ :=
    fun x hx y hy => (convex_closedBall 0 1).norm_image_sub_le_of_norm_fderiv_le hdiff hDL hx hy
  -- continuity of the determinant at the identity
  have hdc : ContinuousAt (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A.det)
      (ContinuousLinearMap.id ℝ _) :=
    ContinuousLinearMap.continuous_det.continuousAt
  obtain ⟨δ, hδ, hdet⟩ := Metric.continuousAt_iff.1 hdc 1 one_pos
  have hid : (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).det = 1 := by
    simp [ContinuousLinearMap.det]
  refine ⟨min 1 (min 1 δ / (2 * L)), ?_, ?_⟩
  · exact lt_min one_pos (div_pos (lt_min one_pos hδ) (by positivity))
  rintro t ⟨ht0, htε⟩
  have ht1 : t ≤ 1 := htε.trans (min_le_left _ _)
  have htL : t * L ≤ min 1 δ / 2 := by
    have h1 : t ≤ min 1 δ / (2 * L) := htε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hm1 : min 1 δ ≤ 1 := min_le_left _ _
  have hmδ : min 1 δ ≤ δ := min_le_right _ _
  have hmpos : 0 < min 1 δ := lt_min one_pos hδ
  have htL1 : t * L < 1 := by linarith
  have htLδ : t * L < δ := by linarith
  -- injectivity
  have hinj : InjOn (fun x => x + t • w x) (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    intro x hx y hy hxy
    simp only at hxy
    have h1 : x - y = t • (w y - w x) := by
      calc x - y = (x + t • w x) - (y + t • w y) + (t • w y - t • w x) := by abel
        _ = t • (w y - w x) := by rw [hxy, sub_self, zero_add, smul_sub]
    have h2 : ‖x - y‖ ≤ t * L * ‖x - y‖ := by
      have h4 : ‖w y - w x‖ ≤ L * ‖x - y‖ := by
        have := hLip x hx y hy
        rwa [norm_sub_rev y x] at this
      calc ‖x - y‖ = t * ‖w y - w x‖ := by rw [h1, norm_smul, Real.norm_of_nonneg ht0]
        _ ≤ t * (L * ‖x - y‖) := mul_le_mul_of_nonneg_left h4 ht0
        _ = t * L * ‖x - y‖ := by ring
    have h3 : ‖x - y‖ = 0 := by
      nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)
  -- positivity of the Jacobian
  have hdetpos : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      0 < (ContinuousLinearMap.id ℝ _ + t • fderiv ℝ w x).det := by
    intro x hx
    have hd : dist (ContinuousLinearMap.id ℝ _ + t • fderiv ℝ w x)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      calc t * ‖fderiv ℝ w x‖ ≤ t * L := mul_le_mul_of_nonneg_left (hDL x hx) ht0
        _ < δ := htLδ
    have h := hdet hd
    rw [Real.dist_eq, hid] at h
    have := (abs_lt.1 h).1
    linarith
  -- the closed ball is mapped into itself
  have hfB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      x + t • w x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro x hx
    have := (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) hx (hwB x hx)
      (sub_nonneg.2 ht1) ht0 (sub_add_cancel 1 t)
    convert this using 1
    simp only [smul_add, sub_smul, one_smul]
    abel
  -- the sphere is fixed
  have hfix : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 → x + t • w x = x := by
    intro x hx
    simp [hw0 x hx]
  -- the open ball is mapped into itself
  have hball : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      x + t • w x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro x hx
    have hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := ball_subset_closedBall hx
    have hfxB := hfB x hxB
    rw [mem_ball_zero_iff]
    rw [mem_closedBall_zero_iff] at hfxB
    rcases hfxB.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hfix _ h
      have h2 : x + t • w x = x := hinj (hfB x hxB) hxB h1
      rw [mem_ball_zero_iff] at hx
      rw [h2] at h
      linarith
  -- openness of the image of the open ball (inverse function theorem)
  have hopen : IsOpen ((fun x => x + t • w x) '' ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x, hx, rfl⟩
    have hxU : U ∈ nhds x := hU.mem_nhds (hBU (ball_subset_closedBall hx))
    have hs : HasStrictFDerivAt w (fderiv ℝ w x) x :=
      (hw.contDiffAt hxU).hasStrictFDerivAt one_ne_zero
    have hfs : HasStrictFDerivAt (fun x => x + t • w x)
        (ContinuousLinearMap.id ℝ _ + t • fderiv ℝ w x) x :=
      (hasStrictFDerivAt_id x).add (hs.const_smul t)
    have hA : (ContinuousLinearMap.id ℝ _ + t • fderiv ℝ w x).det ≠ 0 :=
      (hdetpos x (ball_subset_closedBall hx)).ne'
    have hfs' : HasStrictFDerivAt (fun x => x + t • w x)
        (((ContinuousLinearMap.id ℝ _ + t • fderiv ℝ w x).toContinuousLinearEquivOfDetNeZero hA :
          EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) x := by
      rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    rw [← hfs'.map_nhds_eq_of_equiv]
    exact Filter.image_mem_map (isOpen_ball.mem_nhds hx)
  -- connectedness of the open ball
  have hcont : ContinuousOn (fun x => x + t • w x) (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    continuousOn_id.add ((hw.continuousOn.mono hBU).const_smul t)
  have hcomp : IsCompact ((fun x => x + t • w x) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn hcont
  have hsub : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆
      (fun x => x + t • w x) '' ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    refine (convex_ball (0 : EuclideanSpace ℝ (Fin n)) 1).isPreconnected.subset_of_closure_inter_subset
      hopen ?_ ?_
    · exact ⟨_, hball 0 (mem_ball_self one_pos), 0, mem_ball_self one_pos, rfl⟩
    · rintro y ⟨hycl, hyb⟩
      have hy : y ∈ (fun x => x + t • w x) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        (closure_minimal (image_mono ball_subset_closedBall) hcomp.isClosed) hycl
      obtain ⟨x, hxB, rfl⟩ := hy
      refine ⟨x, ?_, rfl⟩
      rw [mem_ball_zero_iff]
      rw [mem_closedBall_zero_iff] at hxB
      rcases hxB.lt_or_eq with h | h
      · exact h
      · exfalso
        simp only at hyb
        rw [hfix x h, mem_ball_zero_iff, h] at hyb
        exact lt_irrefl _ hyb
  refine ⟨hinj, ?_, hdetpos⟩
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hfB x hx
  · intro y hy
    rw [mem_closedBall_zero_iff] at hy
    rcases hy.lt_or_eq with h | h
    · obtain ⟨x, hx, hxy⟩ := hsub (mem_ball_zero_iff.2 h)
      exact ⟨x, ball_subset_closedBall hx, hxy⟩
    · exact ⟨y, mem_closedBall_zero_iff.2 h.le, hfix y h⟩

end Molico.Brouwer
