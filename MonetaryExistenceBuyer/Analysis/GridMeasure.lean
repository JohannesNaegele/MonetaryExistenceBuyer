import MonetaryExistenceBuyer.Limit.Basic
import MonetaryExistenceBuyer.Analysis.Interp

/-!
# Grid laws and grid meeting measures as measures

`gridMeasure h N η = ∑_l η_l δ_{l h}` and `gridMeeting h N η κ = ∑ η_m η_l κ_{m,l,j} δ_{(mh,lh,jh)}`
(`def:approx`): integrals are finite sums, marginals and stationarity hold in measure form, and
Markov's inequality bounds the tail.
-/

open Set Filter Topology MeasureTheory Finset
open scoped ENNReal Classical

noncomputable section

namespace Molico

/-! ### Weighted Dirac masses -/

section Dirac

variable {α : Type*} [MeasurableSpace α]

/-- Every function is integrable for a Dirac mass with finite weight. -/
theorem integrable_smul_dirac [MeasurableSingletonClass α] (f : α → ℝ) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (a : α) : Integrable f (c • Measure.dirac a) :=
  (integrable_dirac enorm_lt_top).smul_measure hc

theorem integral_ofReal_smul_dirac [MeasurableSingletonClass α] (f : α → ℝ) {w : ℝ} (hw : 0 ≤ w)
    (a : α) : ∫ x, f x ∂(ENNReal.ofReal w • Measure.dirac a) = w * f a := by
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw, smul_eq_mul]

theorem ofReal_smul_dirac_apply {w : ℝ} (a : α) {s : Set α} (hs : MeasurableSet s) :
    (ENNReal.ofReal w • Measure.dirac a) s = ENNReal.ofReal (if a ∈ s then w else 0) := by
  rw [Measure.smul_apply, Measure.dirac_apply' a hs, Set.indicator_apply]
  split_ifs <;> simp

/-- A weighted Dirac mass is carried by its atom (if the weight is nonzero). -/
theorem ae_smul_dirac [MeasurableSingletonClass α] {c : ℝ≥0∞} {a : α} {p : α → Prop}
    (hp : c ≠ 0 → p a) : ∀ᵐ x ∂(c • Measure.dirac a), p x := by
  by_cases hc : c = 0
  · simp [hc]
  · refine Measure.ae_smul_measure ?_ c
    rw [ae_dirac_eq]
    exact Filter.eventually_pure.2 (hp hc)

end Dirac

variable {P : Primitives} {h M : ℝ} {N : ℕ} {V η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ}

/-- `gridMeasure` of a measurable set, as the `ofReal` of a real sum. -/
theorem gridMeasure_apply' (hη0 : ∀ l, 0 ≤ η l) {s : Set ℝ} (hs : MeasurableSet s) :
    gridMeasure h N η s =
      ENNReal.ofReal (∑ l ∈ range (N + 1), if (l : ℝ) * h ∈ s then η l else 0) := by
  rw [gridMeasure, Measure.finsetSum_apply, ENNReal.ofReal_sum_of_nonneg fun l _ => by
    split_ifs
    exacts [hη0 l, le_rfl]]
  exact Finset.sum_congr rfl fun l _ => ofReal_smul_dirac_apply _ hs

theorem gridMeasure_isProb (hη : Grid.IsLaw h M N η) : IsProbabilityMeasure (gridMeasure h N η) := by
  constructor
  rw [gridMeasure_apply' hη.nonneg MeasurableSet.univ]
  simp only [Set.mem_univ, ↓reduceIte, hη.sum_one, ENNReal.ofReal_one]

theorem integral_gridMeasure (hη0 : ∀ l, 0 ≤ η l) (f : ℝ → ℝ) :
    ∫ x, f x ∂gridMeasure h N η = ∑ l ∈ range (N + 1), η l * f (l * h) := by
  rw [gridMeasure, integral_finsetSum_measure fun l _ =>
    integrable_smul_dirac f ENNReal.ofReal_ne_top _]
  exact Finset.sum_congr rfl fun l _ => integral_ofReal_smul_dirac f (hη0 l) _

theorem gridMeasure_apply (hη0 : ∀ l, 0 ≤ η l) {s : Set ℝ} (hs : MeasurableSet s) :
    gridMeasure h N η s = ∑ l ∈ range (N + 1), if (l : ℝ) * h ∈ s then ENNReal.ofReal (η l) else 0 := by
  rw [gridMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hs, Set.indicator_apply]
  split_ifs <;> simp

/-- Almost-everywhere statements reduce to the charged grid points. -/
theorem ae_gridMeasure (hη0 : ∀ l, 0 ≤ η l) {p : ℝ → Prop}
    (hp : ∀ l ≤ N, η l ≠ 0 → p (l * h)) : ∀ᵐ x ∂gridMeasure h N η, p x := by
  rw [gridMeasure, ae_finsetSum_measure_iff]
  intro l hl
  refine ae_smul_dirac fun hc => hp l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)) fun h0 => ?_
  exact hc (by rw [h0, ENNReal.ofReal_zero])

theorem gridMeasure_map (hη0 : ∀ l, 0 ≤ η l) {Y : Type*} [MeasurableSpace Y] {f : ℝ → Y}
    (hf : Measurable f) :
    (gridMeasure h N η).map f = ∑ l ∈ range (N + 1), ENNReal.ofReal (η l) • Measure.dirac (f (l * h)) := by
  rw [← Measure.mapₗ_apply_of_measurable hf, gridMeasure, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Measure.mapₗ_apply_of_measurable hf, Measure.map_dirac' hf]

/-- Mean and Markov's inequality: `η_n((S, ∞)) ≤ M/S`. -/
theorem gridMeasure_mean (hh : 0 ≤ h) (hη : Grid.IsLaw h M N η) :
    ∫ x, x ∂gridMeasure h N η = M :=
  (integral_gridMeasure hη.nonneg fun x => x).trans hη.mean

theorem gridMeasure_Ioi_le (hh : 0 ≤ h) (hη : Grid.IsLaw h M N η) {S : ℝ} (hS : 0 < S) :
    (gridMeasure h N η).real (Ioi S) ≤ M / S := by
  rw [measureReal_def, gridMeasure_apply' hη.nonneg measurableSet_Ioi,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun l _ => by
      split_ifs
      exacts [hη.nonneg l, le_rfl]),
    le_div_iff₀ hS, ← hη.mean, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with hl
  · exact mul_le_mul_of_nonneg_left (Set.mem_Ioi.1 hl).le (hη.nonneg l)
  · rw [zero_mul]
    exact mul_nonneg (hη.nonneg l) (mul_nonneg (Nat.cast_nonneg l) hh)

theorem gridMeasure_compl_Icc (hh : 0 ≤ h) (hη : Grid.IsLaw h M N η) :
    gridMeasure h N η (Icc 0 (N * h))ᶜ = 0 := by
  rw [gridMeasure_apply hη.nonneg measurableSet_Icc.compl]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl' : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have hmem : (l : ℝ) * h ∈ Icc 0 (N * h) :=
    ⟨mul_nonneg (Nat.cast_nonneg l) hh, mul_le_mul_of_nonneg_right (by exact_mod_cast hl') hh⟩
  exact ite_eq_right fun hc => hc hmem

/-! ### The grid meeting measure -/

/-- `gridMeeting` of a measurable set, as the `ofReal` of a real triple sum. -/
theorem gridMeeting_apply (hη0 : ∀ l, 0 ≤ η l) (hκ0 : ∀ m l j, 0 ≤ κ m l j)
    {s : Set (ℝ × ℝ × ℝ)} (hs : MeasurableSet s) :
    gridMeeting h N η κ s = ENNReal.ofReal (∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1),
      ∑ j ∈ Grid.feas N m l,
        if ((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) ∈ s then η m * η l * κ m l j else 0) := by
  have hite : ∀ m l j : ℕ, 0 ≤ (if ((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) ∈ s then
      η m * η l * κ m l j else 0) := fun m l j => by
    split_ifs
    exacts [mul_nonneg (mul_nonneg (hη0 m) (hη0 l)) (hκ0 m l j), le_rfl]
  rw [ENNReal.ofReal_sum_of_nonneg fun m _ => Finset.sum_nonneg fun l _ =>
    Finset.sum_nonneg fun j _ => hite m l j, gridMeeting, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun l _ => Finset.sum_nonneg fun j _ => hite m l j,
    Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hite m l j, Measure.finsetSum_apply]
  exact Finset.sum_congr rfl fun j _ => ofReal_smul_dirac_apply _ hs

/-- The kernel `κ m l` sums to one over feasible transfers. -/
theorem sum_feas_mul_kernel {κ : ℕ → ℕ → ℕ → ℝ} (hκ : Grid.IsKernel N κ) {m l : ℕ}
    (hm : m ∈ range (N + 1)) (hl : l ∈ range (N + 1)) (c : ℝ) :
    ∑ j ∈ Grid.feas N m l, c * κ m l j = c := by
  rw [← Finset.mul_sum, hκ.sum_one m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) l
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)), mul_one]

theorem gridMeeting_isProb (hh : 0 < h) (hE : Grid.IsApproxEq P h N V η κ) :
    IsProbabilityMeasure (gridMeeting h N η κ) := by
  constructor
  rw [gridMeeting_apply hE.law.nonneg hE.kernel.nonneg MeasurableSet.univ, ← ENNReal.ofReal_one]
  congr 1
  simp only [Set.mem_univ, ↓reduceIte]
  calc ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), ∑ j ∈ Grid.feas N m l, η m * η l * κ m l j
      = ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), η m * η l :=
        Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl =>
          sum_feas_mul_kernel hE.kernel hm hl _
    _ = 1 := by rw [← Finset.sum_mul_sum, hE.law.sum_one, mul_one]

theorem integral_gridMeeting (hE : Grid.IsApproxEq P h N V η κ) (f : ℝ × ℝ × ℝ → ℝ) :
    ∫ p, f p ∂gridMeeting h N η κ = ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1),
      ∑ j ∈ Grid.feas N m l, η m * η l * κ m l j * f ((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) := by
  have hI : ∀ m l j, Integrable f (ENNReal.ofReal (η m * η l * κ m l j) •
      Measure.dirac ((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h)) := fun m l j =>
    integrable_smul_dirac f ENNReal.ofReal_ne_top _
  have hw : ∀ m l j, 0 ≤ η m * η l * κ m l j := fun m l j =>
    mul_nonneg (mul_nonneg (hE.law.nonneg m) (hE.law.nonneg l)) (hE.kernel.nonneg m l j)
  unfold gridMeeting
  rw [integral_finsetSum_measure fun m _ => integrable_finsetSum_measure.2 fun l _ =>
    integrable_finsetSum_measure.2 fun j _ => hI m l j]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum_measure fun l _ => integrable_finsetSum_measure.2 fun j _ => hI m l j]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum_measure fun j _ => hI m l j]
  exact Finset.sum_congr rfl fun j _ => integral_ofReal_smul_dirac f (hw m l j) _

/-- The meeting measure is carried by the charged optimal triples. -/
theorem ae_gridMeeting (hE : Grid.IsApproxEq P h N V η κ) :
    ∀ᵐ p ∂gridMeeting h N η κ, ∃ m l j, m ≤ N ∧ l ≤ N ∧ j ∈ Grid.feas N m l ∧
      η m ≠ 0 ∧ η l ≠ 0 ∧ κ m l j ≠ 0 ∧
      Grid.gobj P.U.u V m l j = Grid.gH P.U.u N V m l ∧
      p = ((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) := by
  unfold gridMeeting
  rw [ae_finsetSum_measure_iff]
  intro m hm
  rw [ae_finsetSum_measure_iff]
  intro l hl
  rw [ae_finsetSum_measure_iff]
  intro j hj
  refine ae_smul_dirac fun hc => ?_
  have hpos : η m * η l * κ m l j ≠ 0 := fun h0 => hc (by rw [h0, ENNReal.ofReal_zero])
  have hm' : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hl' : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  exact ⟨m, l, j, hm', hl', hj, left_ne_zero_of_mul (left_ne_zero_of_mul hpos),
    right_ne_zero_of_mul (left_ne_zero_of_mul hpos), right_ne_zero_of_mul hpos,
    hE.argmax m hm' l hl' j hj (right_ne_zero_of_mul hpos), rfl⟩

/-- The `(b,s)`-marginal of `Γ_n` is `η_n ⊗ η_n`. -/
theorem gridMeeting_marginal (hh : 0 < h) (hE : Grid.IsApproxEq P h N V η κ) :
    (gridMeeting h N η κ).map pairBS = (gridMeasure h N η).prod (gridMeasure h N η) := by
  have := gridMeasure_isProb hE.law
  have mP : Measurable pairBS := by unfold pairBS; fun_prop
  have hη0 := hE.law.nonneg
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  have hnn : 0 ≤ ∑ l ∈ range (N + 1), if (l : ℝ) * h ∈ s then η l else 0 :=
    Finset.sum_nonneg fun l _ => by
      split_ifs
      exacts [hη0 l, le_rfl]
  rw [Measure.map_apply mP (hs.prod ht), gridMeeting_apply hη0 hE.kernel.nonneg (mP (hs.prod ht)),
    gridMeasure_apply' hη0 hs, gridMeasure_apply' hη0 ht, ← ENNReal.ofReal_mul hnn,
    Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl => ?_
  have hmem : ∀ j : ℕ, (((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) ∈ pairBS ⁻¹' (s ×ˢ t)) ↔
      ((m : ℝ) * h ∈ s ∧ (l : ℝ) * h ∈ t) := fun j => Iff.rfl
  simp only [hmem]
  by_cases h1 : (m : ℝ) * h ∈ s <;> by_cases h2 : (l : ℝ) * h ∈ t <;>
    simp only [h1, h2, and_self, and_true, and_false, ↓reduceIte,
      Finset.sum_const_zero, mul_zero, zero_mul]
  exact sum_feas_mul_kernel hE.kernel hm hl _

/-- Stationarity in measure form: `η_n = ½ B_# Γ_n + ½ S_# Γ_n`. -/
theorem gridMeeting_stationary (hh : 0 < h) (hE : Grid.IsApproxEq P h N V η κ) :
    gridMeasure h N η = (2⁻¹ : ℝ≥0∞) • (gridMeeting h N η κ).map postB +
      (2⁻¹ : ℝ≥0∞) • (gridMeeting h N η κ).map postS := by
  have mB : Measurable postB := by unfold postB; fun_prop
  have mS : Measurable postS := by unfold postS; fun_prop
  have hη0 := hE.law.nonneg
  have hw : ∀ m l j, 0 ≤ η m * η l * κ m l j := fun m l j =>
    mul_nonneg (mul_nonneg (hη0 m) (hη0 l)) (hE.kernel.nonneg m l j)
  ext s hs
  have hnn : ∀ A : Set (ℝ × ℝ × ℝ), 0 ≤ ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1),
      ∑ j ∈ Grid.feas N m l,
        if ((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) ∈ A then η m * η l * κ m l j else 0 :=
    fun A => Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun j _ => by
        split_ifs
        exacts [hw m l j, le_rfl]
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.map_apply mB hs,
    Measure.map_apply mS hs, gridMeeting_apply hη0 hE.kernel.nonneg (mB hs),
    gridMeeting_apply hη0 hE.kernel.nonneg (mS hs), gridMeasure_apply' hη0 hs, smul_eq_mul,
    smul_eq_mul, h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (hnn _)) (mul_nonneg (by norm_num) (hnn _))]
  congr 1
  -- the real identity, via `η = Ψ_κ(η)`
  set w : ℕ → ℝ := fun k => if (k : ℝ) * h ∈ s then 1 else 0 with hwdef
  calc ∑ k ∈ range (N + 1), (if (k : ℝ) * h ∈ s then η k else 0)
      = ∑ k ∈ range (N + 1), Grid.gPsi N η κ k * w k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [← hE.stationary k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
        simp only [hwdef]
        split_ifs <;> simp
    _ = 2⁻¹ * ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), ∑ j ∈ Grid.feas N m l,
          η m * η l * κ m l j * (w (m - j) + w (l + j)) := by
        rw [Grid.sum_gPsi_mul]
        congr 1
        refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl =>
          Finset.sum_congr rfl fun j hj => ?_
        rw [Grid.landing_sum hm hl hj]
    _ = _ := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hm' : m ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
        have hl' : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
        have hjm : j ≤ m := ((Grid.mem_feas hm' hl').1 hj).1
        have eB : (((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) ∈ postB ⁻¹' s) ↔
            ((m - j : ℕ) : ℝ) * h ∈ s := by
          rw [Set.mem_preimage, Nat.cast_sub hjm, sub_mul]
          rfl
        have eS : (((m : ℝ) * h, (l : ℝ) * h, (j : ℝ) * h) ∈ postS ⁻¹' s) ↔
            ((l + j : ℕ) : ℝ) * h ∈ s := by
          rw [Set.mem_preimage, Nat.cast_add, add_mul]
          rfl
        simp only [hwdef, eB, eS]
        split_ifs <;> ring

end Molico
