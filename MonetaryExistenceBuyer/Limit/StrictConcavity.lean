import MonetaryExistenceBuyer.Limit.Deterministic

/-!
# Strict concavity of the value function (`prop:strictconcavity`)

Every equilibrium `(V, η, Γ)` in the sense of `def:eq` has a strictly concave value function.

The proof follows the manuscript. By `prop:deterministic`, `V` is strictly increasing. If `V`
were not strictly concave, concavity would force it to satisfy a midpoint identity
`V(a + h/2) = (V(a) + V(a+h))/2` on some interval of length `h > 0` (`exists_midpoint_eq`).
The set of such left endpoints `a` is closed, so it has a least element `a`. Comparing the
Bellman equation `eq:HT` at `a`, `a + h/2` and `a + h` (`midpoint_chain`) shows that, for
`η`-almost every seller, the optimal payments at `a` and `a + h` coincide and the midpoint
identity also holds on `[a - d, a + h - d]`; minimality forces `d = 0`, whence
`H_V(a+h, s) = V(a+h)` almost surely and `V(a+h) = β V(a+h)`, contradicting `V(a+h) > 0`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

section Helpers

variable (U : AdmissibleUtility) {V : ℝ → ℝ}

/-- A concave function on `[0,∞)` that touches a chord at an interior point satisfies a midpoint
identity on a subinterval. Case where the touching point lies in the left half, `b ≤ 1/2`. -/
private lemma exists_midpoint_eq_aux (hV : IsValueFn V) {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≠ y) (hb : 0 < b) (hab : a + b = 1) (hb2 : b ≤ 1 / 2)
    (heq : V (a * x + b * y) = a * V x + b * V y) :
    ∃ p q, 0 ≤ p ∧ 0 ≤ q ∧ p ≠ q ∧ V ((p + q) / 2) = (V p + V q) / 2 := by
  obtain rfl : a = 1 - b := by linarith
  set q := (1 - 2 * b) * x + 2 * b * y with hq_def
  have hq0 : 0 ≤ q := by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity
  have hq : (1 - 2 * b) * V x + 2 * b * V y ≤ V q := by
    have := hV.concaveOn.2 (show x ∈ Ici (0:ℝ) from hx) (show y ∈ Ici (0:ℝ) from hy)
      (show (0:ℝ) ≤ 1 - 2 * b by linarith) (show (0:ℝ) ≤ 2 * b by linarith) (by ring)
    simpa only [smul_eq_mul] using this
  have hp : (1 / 2 : ℝ) * V x + (1 / 2) * V q ≤ V ((1 - b) * x + b * y) := by
    have := hV.concaveOn.2 (show x ∈ Ici (0:ℝ) from hx) (show q ∈ Ici (0:ℝ) from hq0)
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : (1 / 2 : ℝ) * x + 1 / 2 * q = (1 - b) * x + b * y := by rw [hq_def]; ring
    rwa [e] at this
  refine ⟨x, q, hx, hq0, fun hxq => hxy ?_, ?_⟩
  · have : 2 * b * (y - x) = 0 := by rw [hq_def] at hxq; linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  · have e : (x + q) / 2 = (1 - b) * x + b * y := by rw [hq_def]; ring
    rw [e]
    linarith

/-- A concave function on `[0,∞)` that touches a chord at an interior point satisfies a midpoint
identity on a subinterval. -/
private lemma exists_midpoint_eq (hV : IsValueFn V) {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≠ y) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (heq : V (a * x + b * y) = a * V x + b * V y) :
    ∃ p q, 0 ≤ p ∧ 0 ≤ q ∧ p ≠ q ∧ V ((p + q) / 2) = (V p + V q) / 2 := by
  rcases le_or_gt b (1 / 2) with hb2 | hb2
  · exact exists_midpoint_eq_aux hV hx hy hxy hb hab hb2 heq
  · refine exists_midpoint_eq_aux hV hy hx hxy.symm ha (show b + a = 1 by linarith)
      (show a ≤ 1 / 2 by linarith) ?_
    rw [add_comm (b * y) (a * x), add_comm (b * V y) (a * V x)]
    exact heq

/-- A value function which is not strictly concave satisfies a nontrivial midpoint identity
`V(a + h/2) = (V(a) + V(a+h))/2` with `a ≥ 0`, `h > 0`. -/
private lemma exists_midpoint_of_not_strictConcave (hV : IsValueFn V)
    (hns : ¬ StrictConcaveOn ℝ (Ici 0) V) :
    ∃ a h, 0 ≤ a ∧ 0 < h ∧ V (a + h / 2) = (V a + V (a + h)) / 2 := by
  unfold StrictConcaveOn at hns
  push Not at hns
  obtain ⟨x, hx, y, hy, hxy, a, b, ha, hb, hab, hle⟩ := hns (convex_Ici 0)
  simp only [smul_eq_mul] at hle
  have hge := hV.concaveOn.2 hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hge
  have heq : V (a * x + b * y) = a * V x + b * V y := le_antisymm hle hge
  obtain ⟨p, q, hp, hq, hpq, hmid⟩ := exists_midpoint_eq hV hx hy hxy ha hb hab heq
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · refine ⟨p, q - p, hp, by linarith, ?_⟩
    have e1 : p + (q - p) / 2 = (p + q) / 2 := by ring
    have e2 : p + (q - p) = q := by ring
    rw [e1, e2, hmid]
  · refine ⟨q, p - q, hq, by linarith, ?_⟩
    have e1 : q + (p - q) / 2 = (p + q) / 2 := by ring
    have e2 : q + (p - q) = p := by ring
    rw [e1, e2, hmid, add_comm]

/-- The set of left endpoints `a ≥ 0` of intervals `[a, a+h]` on which the value function satisfies
the midpoint identity is closed (continuity of `V`), hence has a least element. -/
private lemma exists_min_midpoint (hV : IsValueFn V) {a₀ h : ℝ} (ha₀ : 0 ≤ a₀) (hh : 0 < h)
    (hmid : V (a₀ + h / 2) = (V a₀ + V (a₀ + h)) / 2) :
    ∃ a, 0 ≤ a ∧ V (a + h / 2) = (V a + V (a + h)) / 2 ∧
      ∀ x, 0 ≤ x → V (x + h / 2) = (V x + V (x + h)) / 2 → a ≤ x := by
  set A : Set ℝ :=
    Ici 0 ∩ {x | posPart V (x + h / 2) = (posPart V x + posPart V (x + h)) / 2} with hA_def
  have hmemA : ∀ x, 0 ≤ x → (x ∈ A ↔ V (x + h / 2) = (V x + V (x + h)) / 2) := by
    intro x hx
    rw [hA_def, mem_inter_iff, mem_Ici, mem_ofPred_eq, posPart_eq hx,
      posPart_eq (by linarith : 0 ≤ x + h / 2), posPart_eq (by linarith : 0 ≤ x + h)]
    exact and_iff_right hx
  have hAne : A.Nonempty := ⟨a₀, (hmemA a₀ ha₀).2 hmid⟩
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1⟩
  have hAcl : IsClosed A := by
    have hVt : Continuous (posPart V) := continuous_posPart hV.continuousOn
    have h1 : Continuous fun x : ℝ => posPart V (x + h / 2) := by fun_prop
    have h2 : Continuous fun x : ℝ => (posPart V x + posPart V (x + h)) / 2 := by fun_prop
    exact isClosed_Ici.inter (isClosed_eq h1 h2)
  have hmem := hAcl.csInf_mem hAne hAbdd
  exact ⟨sInf A, hmem.1, (hmemA _ hmem.1).1 hmem,
    fun x hx hxeq => csInf_le hAbdd ((hmemA x hx).2 hxeq)⟩

/-- Midpoint comparison of the Bellman objective (proof of `prop:strictconcavity`): for buyer
wealths `a` and `a + h` with feasible payments `da`, `db`, the average payment is feasible at the
midpoint wealth `a + h/2`, and concavity of `u`, of `d ↦ Δ_V(s,d)` and of `V` give the three
inequalities behind `H_V(a + h/2, s) ≥ ½ H_V(a, s) + ½ H_V(a + h, s)`. -/
private lemma midpoint_chain (hV : IsValueFn V) {a h s da db : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hs : 0 ≤ s) (hda : da ∈ Icc 0 a) (hdb : db ∈ Icc 0 (a + h)) :
    (1 / 2 : ℝ) * U.u (gain V s da) + (1 / 2) * U.u (gain V s db) ≤
        U.u ((1 / 2) * gain V s da + (1 / 2) * gain V s db) ∧
      U.u ((1 / 2) * gain V s da + (1 / 2) * gain V s db) ≤ U.u (gain V s ((da + db) / 2)) ∧
      (1 / 2 : ℝ) * V (a - da) + (1 / 2) * V (a + h - db) ≤ V (a + h / 2 - (da + db) / 2) ∧
      obj U.u V (a + h / 2) s ((da + db) / 2) ≤ bellH U.u V (a + h / 2) s := by
  have hga : 0 ≤ gain V s da := hV.gain_nonneg hs hda.1
  have hgb : 0 ≤ gain V s db := hV.gain_nonneg hs hdb.1
  have hdm : (da + db) / 2 ∈ Icc 0 (a + h / 2) :=
    ⟨by linarith [hda.1, hdb.1], by linarith [hda.2, hdb.2]⟩
  refine ⟨?_, ?_, ?_, obj_le_bellH U hV (by linarith) hs hdm⟩
  · have := U.concaveOn.2 (show gain V s da ∈ Ici (0:ℝ) from hga)
      (show gain V s db ∈ Ici (0:ℝ) from hgb) (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
    simpa only [smul_eq_mul] using this
  · apply U.monotoneOn (show (1 / 2) * gain V s da + (1 / 2) * gain V s db ∈ Ici (0:ℝ) by
        simp only [mem_Ici]; positivity)
      (show gain V s ((da + db) / 2) ∈ Ici (0:ℝ) from hV.gain_nonneg hs hdm.1)
    have := hV.concaveOn.2 (show s + da ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hda.1])
      (show s + db ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hdb.1])
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : (1 / 2 : ℝ) * (s + da) + 1 / 2 * (s + db) = s + (da + db) / 2 := by ring
    rw [e] at this
    simp only [gain]
    linarith
  · have := hV.concaveOn.2 (show a - da ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hda.2])
      (show a + h - db ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hdb.2])
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e : (1 / 2 : ℝ) * (a - da) + 1 / 2 * (a + h - db) = a + h / 2 - (da + db) / 2 := by
      ring
    rwa [e] at this

end Helpers

/-- `prop:strictconcavity`: every equilibrium `(V, η, Γ)` in the sense of `def:eq` has a strictly
concave value function. -/
theorem strictconcavity (U : AdmissibleUtility) {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {V : ℝ → ℝ} {η : Measure ℝ} {Γ : Measure (ℝ × ℝ × ℝ)} (h : IsEquilibrium U.u β M V η Γ) :
    StrictConcaveOn ℝ (Ici 0) V := by
  have hV := h.value
  have := h.isProb_η
  -- `prop:deterministic`: `V` is strictly increasing
  have hsm : StrictMonoOn V (Ici 0) := (deterministic U hβ0 hβ1 h).1
  by_contra hns
  -- a midpoint identity on an interval of length `h₀ > 0`, with least left endpoint `a`
  obtain ⟨a₀, h₀, ha₀, hh, hmid₀⟩ := exists_midpoint_of_not_strictConcave hV hns
  obtain ⟨a, ha0, hmid, hamin⟩ := exists_min_midpoint hV ha₀ hh hmid₀
  have hb0 : 0 ≤ a + h₀ := by linarith
  have hm0 : 0 ≤ a + h₀ / 2 := by linarith
  -- a continuous version of `H_V` and the Bellman equation
  obtain ⟨G, hG, hGb, hGeq⟩ := exists_continuous_bellH U hV
  have hint : ∀ m, Integrable (fun s => G (m, s)) η := fun m =>
    Integrable.of_bound
      (hG.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      (U.ubar + hV.sup) (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGb _).1]; exact (hGb _).2)
  have hbell : ∀ m, 0 ≤ m → V m = β * ∫ s, G (m, s) ∂η := by
    intro m hm
    rw [h.bellman m hm, bellT]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h.ae_η_nonneg] with s hs
    exact (hGeq m s hm hs).symm
  -- pointwise: `H_V(a + h₀/2, s) ≥ ½ H_V(a, s) + ½ H_V(a + h₀, s)`
  have hpt : ∀ s, 0 ≤ s →
      (1 / 2 : ℝ) * bellH U.u V a s + (1 / 2) * bellH U.u V (a + h₀) s ≤
        bellH U.u V (a + h₀ / 2) s := by
    intro s hs
    obtain ⟨da, hda, hdaeq⟩ := exists_bellH_eq U hV ha0 hs
    obtain ⟨db, hdb, hdbeq⟩ := exists_bellH_eq U hV hb0 hs
    obtain ⟨c1, c2, c3, c4⟩ := midpoint_chain U hV ha0 hh.le hs hda hdb
    unfold obj at hdaeq hdbeq c4
    linarith
  -- integrating against `η`, the Bellman equation and the midpoint identity give equality a.e.
  have hg2 : Integrable (fun s => 1 / 2 * G (a, s)) η := (hint a).const_mul _
  have hg3 : Integrable (fun s => 1 / 2 * G (a + h₀, s)) η := (hint (a + h₀)).const_mul _
  have hf1 : Integrable (fun s => G (a + h₀ / 2, s) - 1 / 2 * G (a, s)) η :=
    (hint (a + h₀ / 2)).sub hg2
  have hf2 : Integrable (fun s => G (a + h₀ / 2, s) - 1 / 2 * G (a, s) - 1 / 2 * G (a + h₀, s)) η :=
    hf1.sub hg3
  have hzero :
      ∫ s, (G (a + h₀ / 2, s) - 1 / 2 * G (a, s) - 1 / 2 * G (a + h₀, s)) ∂η = 0 := by
    rw [integral_sub hf1 hg3, integral_sub (hint _) hg2, integral_const_mul, integral_const_mul]
    have e1 := hbell (a + h₀ / 2) hm0
    have e2 := hbell a ha0
    have e3 := hbell (a + h₀) hb0
    have key : β * (∫ s, G (a + h₀ / 2, s) ∂η - 1 / 2 * ∫ s, G (a, s) ∂η -
        1 / 2 * ∫ s, G (a + h₀, s) ∂η) = 0 := by
      linear_combination (-1 : ℝ) * e1 + (1 / 2 : ℝ) * e2 + (1 / 2 : ℝ) * e3 + hmid
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hβ0.ne'
    · exact h'
  have hnn : 0 ≤ᵐ[η] fun s => G (a + h₀ / 2, s) - 1 / 2 * G (a, s) - 1 / 2 * G (a + h₀, s) := by
    filter_upwards [h.ae_η_nonneg] with s hs
    rw [hGeq _ _ hm0 hs, hGeq _ _ ha0 hs, hGeq _ _ hb0 hs]
    simp only [Pi.zero_apply]
    linarith [hpt s hs]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hf2).1 hzero
  -- for a.e. seller the optimal payment at `a + h₀` vanishes, so `H_V(a + h₀, s) = V(a + h₀)`
  have hHb : ∀ᵐ s ∂η, G (a + h₀, s) = V (a + h₀) := by
    filter_upwards [hae, h.ae_η_nonneg] with s hs hs0
    simp only [Pi.zero_apply] at hs
    rw [hGeq _ _ hm0 hs0, hGeq _ _ ha0 hs0, hGeq _ _ hb0 hs0] at hs
    rw [hGeq _ _ hb0 hs0]
    obtain ⟨da, hda, hdaeq⟩ := exists_bellH_eq U hV ha0 hs0
    obtain ⟨db, hdb, hdbeq⟩ := exists_bellH_eq U hV hb0 hs0
    obtain ⟨c1, c2, c3, c4⟩ := midpoint_chain U hV ha0 hh.le hs0 hda hdb
    unfold obj at hdaeq hdbeq c4
    -- equality throughout the chain
    have hu_eq : (1 / 2 : ℝ) * U.u (gain V s da) + (1 / 2) * U.u (gain V s db) =
        U.u ((1 / 2) * gain V s da + (1 / 2) * gain V s db) := by linarith
    have hV_eq : (1 / 2 : ℝ) * V (a - da) + (1 / 2) * V (a + h₀ - db) =
        V (a + h₀ / 2 - (da + db) / 2) := by linarith
    -- strict concavity of `u` and strict monotonicity of `V` force `da = db`
    have hga : gain V s da = gain V s db := by
      by_contra hne
      have := U.strictConcaveOn.2 (show gain V s da ∈ Ici (0:ℝ) from hV.gain_nonneg hs0 hda.1)
        (show gain V s db ∈ Ici (0:ℝ) from hV.gain_nonneg hs0 hdb.1) hne
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
      simp only [smul_eq_mul] at this
      linarith
    have hdd : da = db := by
      simp only [gain] at hga
      have h' : V (s + da) = V (s + db) := by linarith
      have := hsm.injOn (show s + da ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hda.1])
        (show s + db ∈ Ici (0:ℝ) by simp only [mem_Ici]; linarith [hdb.1]) h'
      linarith
    -- the midpoint identity holds on `[a - da, a - da + h₀]`, so minimality gives `da = 0`
    have hmid' : V (a - da + h₀ / 2) = (V (a - da) + V (a - da + h₀)) / 2 := by
      have e1 : a - da + h₀ / 2 = a + h₀ / 2 - (da + db) / 2 := by rw [← hdd]; ring
      have e2 : a - da + h₀ = a + h₀ - db := by rw [← hdd]; ring
      rw [e1, e2]
      linarith
    have hda0 : da = 0 := by
      have := hamin (a - da) (by linarith [hda.2]) hmid'
      linarith [hda.1]
    rw [← hdbeq, ← hdd, hda0]
    simp [gain, U.u_zero]
  -- the Bellman equation at `a + h₀` reads `V(a + h₀) = β V(a + h₀)`
  have hVb : V (a + h₀) = β * V (a + h₀) := by
    have e := hbell (a + h₀) hb0
    rw [integral_congr_ae hHb, integral_const] at e
    simpa using e
  have hpos : 0 < V (a + h₀) := by
    have := hsm self_mem_Ici (show a + h₀ ∈ Ici (0:ℝ) from hb0)
      (by linarith)
    rwa [hV.zero] at this
  have := mul_pos (sub_pos.2 hβ1) hpos
  linarith

end Molico
