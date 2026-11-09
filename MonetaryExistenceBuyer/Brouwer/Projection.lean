import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Nearest-point retraction onto a closed convex set

In a real Hilbert space, the nearest-point map onto a nonempty closed convex set is a continuous
(indeed `1`-Lipschitz) retraction.
-/

open Set
open scoped InnerProductSpace

namespace Molico.Brouwer

/-- A nonempty closed convex subset of a real Hilbert space is a retract of the whole space. -/
theorem exists_retraction_convex {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {K : Set F} (hKc : IsClosed K) (hK : Convex ℝ K) (hne : K.Nonempty) :
    ∃ P : F → F, Continuous P ∧ (∀ x, P x ∈ K) ∧ ∀ x ∈ K, P x = x := by
  choose P hPK hPmin using exists_norm_eq_iInf_of_complete_convex hne hKc.isComplete hK
  -- Variational inequality characterising the nearest point.
  have hvi : ∀ x, ∀ w ∈ K, ⟪x - P x, w - P x⟫_ℝ ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hK (hPK x)).1 (hPmin x)
  -- `P` is `1`-Lipschitz.
  have hlip : ∀ x y, ‖P x - P y‖ ≤ ‖x - y‖ := by
    intro x y
    have h1 := hvi x (P y) (hPK y)
    have h2 := hvi y (P x) (hPK x)
    have key : ‖P x - P y‖ ^ 2 ≤ ⟪x - y, P x - P y⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
      linarith
    have hcs := real_inner_le_norm (x - y) (P x - P y)
    nlinarith [norm_nonneg (P x - P y), norm_nonneg (x - y)]
  refine ⟨P, ?_, hPK, ?_⟩
  · exact (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
      simpa [dist_eq_norm] using hlip x y).continuous
  · intro x hx
    have h := hvi x x hx
    rw [real_inner_self_eq_norm_sq] at h
    have h0 : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
    exact (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm

end Molico.Brouwer
