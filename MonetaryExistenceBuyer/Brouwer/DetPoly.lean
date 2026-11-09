import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# `det (1 + t A)` is a polynomial in `t`

For a fixed finite-dimensional space, `t ↦ det (id + t • A)` is a polynomial of degree at most
`dim E`. We record this in interpolation form: there are fixed nodes `c j` and fixed polynomial
weights `ℓ j` (independent of `A`) with `det (id + t • A) = ∑ⱼ ℓⱼ(t) · det (id + cⱼ • A)`.
This is what makes `t ↦ ∫ det (id + t • A x) dx` a polynomial in `t`.
-/

open Polynomial

namespace Molico.Brouwer

/-- For fixed `A`, `t ↦ det (id + t • A)` is the evaluation of a polynomial of degree at most
`finrank ℝ E`. -/
private lemma exists_poly_det_id_add_smul (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) :
    ∃ P : ℝ[X], P.natDegree ≤ Module.finrank ℝ E ∧
      ∀ t : ℝ, P.eval t = (ContinuousLinearMap.id ℝ E + t • A).det := by
  classical
  set b := Module.finBasis ℝ E
  set M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix _ _ ℝ).map C), ?_, ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · intro t
    rw [← coe_evalRingHom, RingHom.map_det]
    have hR : LinearMap.toMatrix b b
        ((ContinuousLinearMap.id ℝ E + t • A : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 + t • M := by
      rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.coe_id, LinearEquiv.map_add, LinearEquiv.map_smul,
        LinearMap.toMatrix_id]
    have hL : (evalRingHom t).mapMatrix ((X : ℝ[X]) • M.map C + (1 : Matrix _ _ ℝ).map C) =
        1 + t • M := by
      ext i j
      by_cases hij : i = j <;> simp [hij] <;> ring
    rw [hL, ← hR, LinearMap.det_toMatrix]

theorem det_id_add_smul_interp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ (m : ℕ) (c : Fin m → ℝ) (ℓ : Fin m → ℝ[X]), ∀ (A : E →L[ℝ] E) (t : ℝ),
      (ContinuousLinearMap.id ℝ E + t • A).det =
        ∑ j, (ℓ j).eval t * (ContinuousLinearMap.id ℝ E + c j • A).det := by
  classical
  set d := Module.finrank ℝ E
  let c : Fin (d + 1) → ℝ := fun j => ((j : ℕ) : ℝ)
  have hc : Set.InjOn c (Finset.univ : Finset (Fin (d + 1))) := by
    intro i _ j _ hij
    exact Fin.ext (Nat.cast_injective hij)
  refine ⟨d + 1, c, fun j => Lagrange.basis Finset.univ c j, fun A t => ?_⟩
  obtain ⟨P, hPdeg, hPeval⟩ := exists_poly_det_id_add_smul E A
  have hdeg : P.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hPdeg).trans_lt (by exact_mod_cast Nat.lt_succ_self d)
  rw [← hPeval, Lagrange.eq_interpolate hc hdeg, Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_comm, hPeval, ← hPeval (c j)]

end Molico.Brouwer
