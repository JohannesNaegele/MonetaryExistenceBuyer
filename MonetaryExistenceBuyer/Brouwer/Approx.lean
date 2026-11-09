import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth approximation (Stone–Weierstrass)

A continuous map on a compact subset of `ℝⁿ` is uniformly approximated by a `C¹` map on all of
`ℝⁿ`. Used to reduce Brouwer's theorem to the `C¹` no-retraction theorem.

Proof: the `C¹` functions form a subalgebra of `C(ℝⁿ, ℝ)` which separates points (coordinate
functions). Each coordinate of `f|_K` is extended to `ℝⁿ` (Tietze) and approximated on `K` within
`δ / (n + 1)` (Stone–Weierstrass); the Euclidean norm of the error is then `< δ`.
-/

open Set

namespace Molico.Brouwer

/-- The subalgebra of `C¹` functions in `C(E, ℝ)`. -/
private def c1Subalgebra (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Subalgebra ℝ C(E, ℝ) where
  carrier := {g | ContDiff ℝ 1 (g : E → ℝ)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.coe_mul] at *
    exact ha.mul hb
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.coe_add] at *
    exact ha.add hb
  algebraMap_mem' r := by
    simp only [Set.mem_ofPred_eq]
    have : ((algebraMap ℝ C(E, ℝ) r : C(E, ℝ)) : E → ℝ) = fun _ => r := by
      ext x; simp
    rw [this]
    exact contDiff_const

/-- The `C¹` subalgebra of `C(ℝⁿ, ℝ)` separates points (via coordinate functions). -/
private lemma c1Subalgebra_separatesPoints (n : ℕ) :
    (c1Subalgebra (EuclideanSpace ℝ (Fin n))).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (PiLp.ext h)
  refine ⟨_, ⟨⟨fun z => z i, (EuclideanSpace.proj (𝕜 := ℝ) i).continuous⟩, ?_, rfl⟩, hi⟩
  change ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin n) => z i)
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- Uniform `C¹` approximation of a continuous map on a compact subset of `ℝⁿ`. -/
theorem exists_contDiff_near {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : ContinuousOn f K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), ContDiff ℝ 1 p ∧
      ∀ x ∈ K, ‖p x - f x‖ < δ := by
  set ε : ℝ := δ / (n + 1) with hε
  have hεpos : 0 < ε := by positivity
  have key : ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 g ∧
      ∀ x ∈ K, |g x - f x i| < ε := by
    intro i
    have hcont : Continuous (fun x : K => f x i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hf.domRestrict
    obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK.isClosed ⟨fun x : K => f x i, hcont⟩
    obtain ⟨g, hgA, hg⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
        (c1Subalgebra_separatesPoints n) F hK hεpos
    refine ⟨g, hgA, fun x hx => ?_⟩
    have hFx : F x = f x i := by
      have := congrArg (fun G : C(K, ℝ) => G ⟨x, hx⟩) hF
      simpa using this
    have := hg x hx
    rwa [hFx, Real.norm_eq_abs] at this
  choose g hgC hg using key
  refine ⟨fun x => WithLp.toLp 2 (fun i => g i x), ?_, ?_⟩
  · exact PiLp.contDiff_toLp.comp (contDiff_pi.2 hgC)
  · intro x hx
    have hsq : ‖(WithLp.toLp 2 (fun i => g i x) : EuclideanSpace ℝ (Fin n)) - f x‖ ^ 2
        < δ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, ((WithLp.toLp 2 (fun i => g i x) : EuclideanSpace ℝ (Fin n)) - f x) i ^ 2
          ≤ ∑ _i : Fin n, ε ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            simp only [PiLp.sub_apply]
            have h1 : |g i x - f x i| ≤ |ε| := by
              rw [abs_of_pos hεpos]; exact (hg i x hx).le
            exact sq_le_sq.mpr h1
        _ = n * ε ^ 2 := by simp
        _ < δ ^ 2 := by
            have hn : (0 : ℝ) ≤ n := n.cast_nonneg
            have hn1 : (0 : ℝ) < n + 1 := by positivity
            have hδ2 : 0 < δ ^ 2 := by positivity
            rw [hε, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
            nlinarith [mul_nonneg hδ2.le (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2 + n)]
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le hsq

end Molico.Brouwer
