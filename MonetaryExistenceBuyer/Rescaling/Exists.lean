import MonetaryExistenceBuyer.Rescaling.Defs

/-!
# Existence of normalized limits (`lem:normalizedlimits`)

The construction of `def:normalization` along nested subsequences:
1. the lattice dichotomy for `δ_n = h_n / e_n = 1 / crossIdx_n` (`exists_lattice`);
2. Helly extraction (`helly_concave`) for the concave nondecreasing profiles `W_n`;
3. Prokhorov extraction (`exists_subseq_weakConv_of_compact`) for `α_n` on the compact
   normalized state space `[0, ∞] × [0, L_*]`;
4. Prokhorov extraction for the normalized meeting measures `Γ̂_n` on the compact `[0, ∞]⁵`.

No crossing property is needed for the existence of these limits: the dichotomy holds for every
`ℕ`-valued crossing index (a value `crossIdx = 0` gives `δ_n = 0`, which falls in the
non-lattice case).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

namespace SelectedSeq

variable (S : SelectedSeq P)

/-- The interpolated values take values in `[0, L_*]`. -/
private lemma Vn_mem_Icc (n : ℕ) (x : ℝ) : 0 ≤ S.Vn n x ∧ S.Vn n x ≤ P.Lstar := by
  have hE := S.isApproxEq n
  have h := interp_mem_Icc (S.h_pos n) hE.cone.incr x
  rw [hE.cone.zero] at h
  exact ⟨h.1, h.2.trans (S.floor n).2⟩

private lemma scale_nonneg (a : ℝ) (n : ℕ) : 0 ≤ S.scale a n :=
  mul_nonneg (S.h_pos n).le (Nat.cast_nonneg _)

private lemma Wn_monotoneOn (a : ℝ) (n : ℕ) : MonotoneOn (S.Wn a n) (Ici 0) := by
  intro x _ y _ hxy
  exact interp_monotone (S.h_pos n) (S.isApproxEq n).cone.incr
    (mul_le_mul_of_nonneg_left hxy (S.scale_nonneg a n))

private lemma Wn_concaveOn (a : ℝ) (n : ℕ) : ConcaveOn ℝ (Ici 0) (S.Wn a n) := by
  have hc := interp_concaveOn (S.h_pos n) (S.isApproxEq n).cone.incr
  refine ⟨convex_Ici 0, fun x hx y hy s t hs ht hst => ?_⟩
  have hx' : S.scale a n * x ∈ Ici (0 : ℝ) := mul_nonneg (S.scale_nonneg a n) hx
  have hy' : S.scale a n * y ∈ Ici (0 : ℝ) := mul_nonneg (S.scale_nonneg a n) hy
  have key := hc.2 hx' hy' hs ht hst
  simp only [smul_eq_mul] at key ⊢
  unfold Wn Vn
  convert key using 2
  ring

/-- `δ_n = 1 / crossIdx_n` (with `1/0 = 0`). -/
private lemma δn_eq (a : ℝ) (n : ℕ) : S.δn a n = ((S.crossIdx a n : ℕ) : ℝ)⁻¹ := by
  unfold δn scale
  exact div_mul_cancel_left₀ (S.h_pos n).ne' _

/-- The lattice dichotomy: along a subsequence, `δ_n → 0` or `δ_n ≡ δ > 0`. -/
private lemma exists_lattice (a : ℝ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ δ : ℝ,
    (δ = 0 ∧ Tendsto (fun n => S.δn a (φ n)) atTop (𝓝 0)) ∨
      (0 < δ ∧ ∀ n, S.δn a (φ n) = δ) := by
  by_cases hc : Tendsto (S.crossIdx a) atTop atTop
  · refine ⟨id, strictMono_id, 0, Or.inl ⟨rfl, ?_⟩⟩
    simp only [id, S.δn_eq]
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hc)
  · have hex : ∃ m, ∃ᶠ n in atTop, S.crossIdx a n ≤ m := by
      simp only [tendsto_atTop, not_forall, not_eventually, not_le] at hc
      obtain ⟨b, hb⟩ := hc
      exact ⟨b, hb.mono fun n hn => hn.le⟩
    classical
    have hfreq : ∃ᶠ n in atTop, S.crossIdx a n = Nat.find hex := by
      have h1 : ∃ᶠ n in atTop, S.crossIdx a n ≤ Nat.find hex := Nat.find_spec hex
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · exact h1.mono fun n hn => by omega
      · have h2 : ¬ ∃ᶠ n in atTop, S.crossIdx a n ≤ Nat.find hex - 1 :=
          Nat.find_min hex (by omega)
        rw [not_frequently] at h2
        exact (h1.and_eventually h2).mono fun n hn => by omega
    obtain ⟨φ, hφ, hφm⟩ := extraction_of_frequently_atTop hfreq
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · refine ⟨φ, hφ, 0, Or.inl ⟨rfl, ?_⟩⟩
      have h : ∀ n, S.δn a (φ n) = 0 := fun n => by rw [S.δn_eq, hφm n, h0]; simp
      simp only [h]
      exact tendsto_const_nhds
    · refine ⟨φ, hφ, ((Nat.find hex : ℕ) : ℝ)⁻¹, Or.inr ⟨by positivity, fun n => ?_⟩⟩
      rw [S.δn_eq, hφm n]

/-- The lattice dichotomy passes to further subsequences. -/
private lemma lattice_comp {a δ : ℝ} {φ ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (h : (δ = 0 ∧ Tendsto (fun n => S.δn a (φ n)) atTop (𝓝 0)) ∨
      (0 < δ ∧ ∀ n, S.δn a (φ n) = δ)) :
    (δ = 0 ∧ Tendsto (fun n => S.δn a (φ (ψ n))) atTop (𝓝 0)) ∨
      (0 < δ ∧ ∀ n, S.δn a (φ (ψ n)) = δ) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2.comp hψ.tendsto_atTop⟩
  · exact Or.inr ⟨h1, fun n => h2 (ψ n)⟩

private lemma continuous_ι (a : ℝ) (n : ℕ) : Continuous (S.ι a n) := by
  unfold ι Vn
  exact (ENNReal.continuous_ofReal.comp (continuous_id.div_const _)).prodMk
    (continuous_interp (S.h_pos n))

private lemma αn_prob (a : ℝ) (n : ℕ) : IsProbabilityMeasure (S.αn a n) := by
  have := gridMeasure_isProb (S.isApproxEq n).law
  unfold αn ηn
  infer_instance

private lemma αn_compl (a : ℝ) (n : ℕ) :
    S.αn a n (univ ×ˢ Icc (0 : ℝ) P.Lstar)ᶜ = 0 := by
  have hK : IsClosed (univ ×ˢ Icc (0 : ℝ) P.Lstar : Set (ℝ≥0∞ × ℝ)) :=
    isClosed_univ.prod isClosed_Icc
  unfold αn
  rw [Measure.map_apply (S.continuous_ι a n).measurable hK.measurableSet.compl]
  have hempty : S.ι a n ⁻¹' (univ ×ˢ Icc (0 : ℝ) P.Lstar)ᶜ = ∅ := by
    ext s
    simp only [mem_preimage, mem_compl_iff, mem_prod, mem_univ, true_and, mem_Icc,
      mem_empty_iff_false, iff_false, not_not]
    exact S.Vn_mem_Icc n s
  rw [hempty, measure_empty]

private lemma Γhat_prob (a : ℝ) (n : ℕ) : IsProbabilityMeasure (S.Γhat a n) := by
  have := gridMeeting_isProb (S.h_pos n) (S.isApproxEq n)
  unfold Γhat Γn
  infer_instance

end SelectedSeq

/-- Locally uniform convergence passes to subsequences. -/
private lemma tendstoLocallyUniformlyOn_subseq {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {s : Set ℝ}
    (h : TendstoLocallyUniformlyOn F f atTop s) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    TendstoLocallyUniformlyOn (fun n => F (ψ n)) f atTop s := fun u hu x hx => by
  obtain ⟨t, ht, hev⟩ := h u hu x hx
  exact ⟨t, ht, hψ.tendsto_atTop.eventually hev⟩

/-- `lem:normalizedlimits` (existence): for every level `a ∈ (0, J₀)` of a bad sequence, the
choices in `def:normalization` (and the limiting meeting measure of `lem:flowpassage`) exist. -/
theorem normalizedLimit_exists (S : SelectedSeq P) {a : ℝ} (ha : 0 < a) (haJ : a < S.jump) :
    Nonempty (NormalizedLimit S a) := by
  obtain ⟨φ₀, hφ₀, δ, hlat⟩ := S.exists_lattice a
  obtain ⟨φ₁, hφ₁, W', hW'⟩ := helly_concave (f := fun n => S.Wn a (φ₀ n)) (B := P.Lstar)
    (fun n => S.Wn_monotoneOn a _) (fun n => S.Wn_concaveOn a _)
    (fun n x _ => S.Vn_mem_Icc _ _)
  obtain ⟨φ₂, hφ₂, α, hαp, -, hα⟩ := exists_subseq_weakConv_of_compact
    (μs := fun n => S.αn a (φ₀ (φ₁ n))) (fun n => S.αn_prob a _)
    (isCompact_univ.prod isCompact_Icc) (fun n => S.αn_compl a _)
  obtain ⟨φ₃, hφ₃, Γh, hΓp, -, hΓ⟩ := exists_subseq_weakConv_of_compact
    (μs := fun n => S.Γhat a (φ₀ (φ₁ (φ₂ n)))) (fun n => S.Γhat_prob a _) isCompact_univ
    (fun n => by rw [compl_univ, measure_empty])
  refine ⟨{ φ := fun n => φ₀ (φ₁ (φ₂ (φ₃ n)))
            φ_mono := hφ₀.comp (hφ₁.comp (hφ₂.comp hφ₃))
            δ := δ
            lattice := S.lattice_comp (φ := φ₀) (ψ := fun n => φ₁ (φ₂ (φ₃ n)))
              (hφ₁.comp (hφ₂.comp hφ₃)) hlat
            W := Function.update W' 0 0
            W_zero := by simp
            W_conv := (tendstoLocallyUniformlyOn_subseq hW' (hφ₂.comp hφ₃)).congr_right
              fun x hx => (Function.update_of_ne (ne_of_gt hx) _ _).symm
            α := α
            α_prob := hαp
            α_conv := fun f => (hα f).comp hφ₃.tendsto_atTop
            Γh := Γh
            Γh_prob := hΓp
            Γh_conv := hΓ }⟩

end Molico
