import MonetaryExistenceBuyer.Grid.Bootstrap
import MonetaryExistenceBuyer.Prelim.Brouwer

/-!
# Existence at fixed `(h, R)` (`thm:approx`)

For every mesh `h > 0` and truncation `R = N h ≥ R_amp` there is an approximant equilibrium
`(V, η, κ)` with `ℓ₀ ≤ V(R) ≤ L_*`.

As in the manuscript, we use the continuation principle `Molico.continuation`
(`lem:continuation`, Brouwer + Urysohn), applied to the softened selector
`κ^ϑ` and the homotopy `Θ^ϑ_t(V, η) = (T_η V + (2tϱ/u₀(R)) u₀, Ψ_{κ^ϑ(V)}(η))`, followed by the
limit `ϑ → ∞` at fixed `(h, R)` (Steps 1–4 of the manuscript's proof).

Structure of the formal proof:
* `toSeq`, `toSeq3`: vectors on `{0,…,N}` (the finite-dimensional state space) as grid
  sequences, extended by zero;
* `stateSet`: the compact convex set `D = 𝒦_{h,R} × 𝒫_M(𝒳)` (`isCompact_stateSet`,
  `convex_stateSet`, `stateSet_nonempty`);
* `homot`: the homotopy `Θ^ϑ_t`, written with the continuous extension `uExt` of the utility
  (`continuous_homot`, `mapsTo_homot`);
* `exists_soft_fixed`: the continuation principle gives, for every `ϑ`, a fixed point of `Θ^ϑ_0`
  with `V(R) > ϱ`;
* `approx_aux` (hence `approx`): the limit `ϑ_i = i + 1 → ∞` along a convergent subsequence in
  `D × [0,1]^{(N+1)³}`; the limit kernel sits on the argmax since `κ^ϑ` puts weight
  `≤ exp(-ϑ γ)` on transfers with objective gap `γ` (`softSel_le_exp`). `V(R) ≥ ϱ > 0`
  survives the limit, so `cor:uniformfloor` gives `ℓ₀ ≤ V(R) ≤ L_*`.

The external inputs are `Molico.continuation` (from Brouwer's theorem) and
`Primitives.uniformfloor` / `Primitives.uniformfloor_fixed`.
-/

open Set Finset Filter Topology

noncomputable section

namespace Molico

namespace Grid

/-- The softened (logit) selector `κ^{𝒳,ϑ}_{m,s}(d) ∝ exp(ϑ φ_{V,m,s}(d))` on `F(m,s)`
(zero off `F(m,s)`). -/
def softSel (u : ℝ → ℝ) (N : ℕ) (ϑ : ℝ) (V : ℕ → ℝ) (m l j : ℕ) : ℝ :=
  if j ∈ feas N m l then
    Real.exp (ϑ * gobj u V m l j) / ∑ j' ∈ feas N m l, Real.exp (ϑ * gobj u V m l j')
  else 0

/-! ### Vectors on `{0,…,N}` as grid sequences -/

/-- A vector on `{0,…,N}` as a grid sequence, extended by zero. -/
def toSeq {N : ℕ} (v : Fin (N + 1) → ℝ) (i : ℕ) : ℝ :=
  if hi : i < N + 1 then v ⟨i, hi⟩ else 0

lemma toSeq_ofFun {N : ℕ} (f : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) :
    toSeq (fun k : Fin (N + 1) => f k) i = f i := by
  simp [toSeq, show i < N + 1 by omega]

lemma toSeq_fin {N : ℕ} (v : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : toSeq v i = v i := by
  simp [toSeq, i.2]

lemma toSeq_last {N : ℕ} (v : Fin (N + 1) → ℝ) : toSeq v N = v (Fin.last N) := by
  simp [toSeq, Fin.last]

lemma toSeq_nonneg {N : ℕ} {v : Fin (N + 1) → ℝ} (hv : ∀ i, 0 ≤ v i) (i : ℕ) :
    0 ≤ toSeq v i := by
  unfold toSeq; split_ifs
  exacts [hv _, le_rfl]

lemma toSeq_add_smul {N : ℕ} (v w : Fin (N + 1) → ℝ) (a b : ℝ) (i : ℕ) :
    toSeq (a • v + b • w) i = a * toSeq v i + b * toSeq w i := by
  unfold toSeq; split_ifs <;> simp

lemma continuous_toSeq_apply (N i : ℕ) : Continuous fun v : Fin (N + 1) → ℝ => toSeq v i := by
  by_cases hi : i < N + 1
  · simp only [toSeq, dite_eq_left hi]; exact continuous_apply _
  · simp only [toSeq, dite_eq_right hi]; exact continuous_const

/-- A kernel tensor on `{0,…,N}³` as a grid kernel, extended by zero. -/
def toSeq3 {N : ℕ} (κ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → ℝ) (m l j : ℕ) : ℝ :=
  if h : m < N + 1 ∧ l < N + 1 ∧ j < N + 1 then κ ⟨m, h.1⟩ ⟨l, h.2.1⟩ ⟨j, h.2.2⟩ else 0

lemma toSeq3_ofFun {N : ℕ} (f : ℕ → ℕ → ℕ → ℝ) {m l j : ℕ} (hm : m ≤ N) (hl : l ≤ N)
    (hj : j ≤ N) : toSeq3 (fun a b c : Fin (N + 1) => f a b c) m l j = f m l j := by
  simp [toSeq3, show m < N + 1 by omega, show l < N + 1 by omega, show j < N + 1 by omega]

lemma continuous_toSeq3_apply (N m l j : ℕ) :
    Continuous fun κ : Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → ℝ => toSeq3 κ m l j := by
  by_cases hc : m < N + 1 ∧ l < N + 1 ∧ j < N + 1
  · simp only [toSeq3, dite_eq_left hc]
    exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply _))
  · simp only [toSeq3, dite_eq_right hc]; exact continuous_const

/-! ### Cones and laws: congruence and convexity -/

lemma incrSeq_of_eq {f g : ℕ → ℝ} {N : ℕ} (hf : IncrSeq f N) (hfg : ∀ i ≤ N, f i = g i) :
    IncrSeq g N :=
  ⟨fun k hk => by
    rw [← hfg k (by omega), ← hfg (k + 1) (by omega)]; exact hf.mono k hk,
   fun k hk => by
    rw [← hfg k (by omega), ← hfg (k + 1) (by omega), ← hfg (k + 2) hk]; exact hf.concave k hk⟩

lemma incrSeq_add {f g : ℕ → ℝ} {N : ℕ} (hf : IncrSeq f N) (hg : IncrSeq g N) :
    IncrSeq (fun i => f i + g i) N :=
  ⟨fun k hk => by have := hf.mono k hk; have := hg.mono k hk; linarith,
   fun k hk => by have := hf.concave k hk; have := hg.concave k hk; linarith⟩

lemma incrSeq_smul {f : ℕ → ℝ} {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (hf : IncrSeq f N) :
    IncrSeq (fun i => a * f i) N :=
  ⟨fun k hk => mul_le_mul_of_nonneg_left (hf.mono k hk) ha,
   fun k hk => by
    have := mul_le_mul_of_nonneg_left (hf.concave k hk) ha
    simp only [mul_sub] at this ⊢; exact this⟩

lemma incrSeq_sum {ι : Type*} (s : Finset ι) {w : ι → ℝ} {f : ι → ℕ → ℝ} {N : ℕ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, IncrSeq (f i) N) :
    IncrSeq (fun m => ∑ i ∈ s, w i * f i m) N := by
  constructor
  · intro k hk
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ((hf i hi).mono k hk) (hw i hi)
  · intro k hk
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have := mul_le_mul_of_nonneg_left ((hf i hi).concave k hk) (hw i hi)
    simp only [mul_sub] at this; exact this

lemma inCone_of_eq {C : ℝ} {N : ℕ} {f g : ℕ → ℝ} (hf : InCone C N f)
    (hfg : ∀ i ≤ N, f i = g i) : InCone C N g :=
  ⟨by rw [← hfg 0 (Nat.zero_le _)]; exact hf.zero, incrSeq_of_eq hf.incr hfg,
   fun i hi => by rw [← hfg i hi]; exact hf.le i hi⟩

lemma isLaw_of_eq {h M : ℝ} {N : ℕ} {f g : ℕ → ℝ} (hf : IsLaw h M N f)
    (hfg : ∀ i ≤ N, f i = g i) (hg : ∀ i, 0 ≤ g i) : IsLaw h M N g :=
  ⟨hg, by
    rw [← hf.sum_one]
    exact Finset.sum_congr rfl fun i hi => (hfg i (by rw [Finset.mem_range] at hi; omega)).symm, by
    rw [← hf.mean]
    exact Finset.sum_congr rfl fun i hi => by rw [hfg i (by rw [Finset.mem_range] at hi; omega)]⟩

lemma inCone_convex {C : ℝ} {N : ℕ} {f g : ℕ → ℝ} (hf : InCone C N f) (hg : InCone C N g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    InCone C N (fun i => a * f i + b * g i) :=
  ⟨by simp [hf.zero, hg.zero], incrSeq_add (incrSeq_smul ha hf.incr) (incrSeq_smul hb hg.incr),
   fun i hi => by
    have h1 := mul_le_mul_of_nonneg_left (hf.le i hi) ha
    have h2 := mul_le_mul_of_nonneg_left (hg.le i hi) hb
    have : a * C + b * C = C := by rw [← add_mul, hab, one_mul]
    linarith⟩

lemma isLaw_convex {h M : ℝ} {N : ℕ} {f g : ℕ → ℝ} (hf : IsLaw h M N f) (hg : IsLaw h M N g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsLaw h M N (fun i => a * f i + b * g i) :=
  ⟨fun i => add_nonneg (mul_nonneg ha (hf.nonneg i)) (mul_nonneg hb (hg.nonneg i)), by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.sum_one, hg.sum_one]
    linarith, by
    simp_rw [add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hf.mean, hg.mean]
    rw [← add_mul, hab, one_mul]⟩

/-! ### The objective for a general utility -/

section General

variable {u : ℝ → ℝ} {N : ℕ} {V : ℕ → ℝ}

lemma gobj_eq_gen (m l j : ℕ) : gobj u V m l j = V (m - j) + sellerSeq u V l j := by
  simp [gobj, sellerSeq, add_comm]

lemma gobj_le_gH_gen {m l j : ℕ} (hj : j ∈ feas N m l) : gobj u V m l j ≤ gH u N V m l := by
  rw [gobj_eq_gen]; exact le_maxConv hj

lemma exists_gH_eq_gen {m l : ℕ} (hm : m ≤ N) (_hl : l ≤ N) :
    ∃ j ∈ feas N m l, gobj u V m l j = gH u N V m l := by
  obtain ⟨j, hj, hmax⟩ := exists_maxConv_eq (A := V) (B := sellerSeq u V l) (P := N)
    (Q := N - l) (i := m) (by omega)
  exact ⟨j, hj, by rw [gobj_eq_gen]; exact hmax⟩

/-- Changing the utility off `[0, ∞)` does not change `H_V` on the cone. -/
lemma gH_congr_u {u' : ℝ → ℝ} (huu : ∀ x, 0 ≤ x → u' x = u x) (hV : IncrSeq V N) {l : ℕ}
    (_hl : l ≤ N) (m : ℕ) : gH u' N V m l = gH u N V m l := by
  unfold gH maxConv
  split_ifs with hc
  · refine Finset.sup'_congr _ rfl fun j hj => ?_
    rw [mem_convSet] at hj
    simp only [sellerSeq]
    rw [huu _ (sub_nonneg.2 (hV.le_of_le (by omega) (by omega)))]
  · rfl

lemma gobj_congr_u {u' : ℝ → ℝ} (huu : ∀ x, 0 ≤ x → u' x = u x) (hV : IncrSeq V N)
    {m l j : ℕ} (hlj : l + j ≤ N) : gobj u' V m l j = gobj u V m l j := by
  simp only [gobj]
  rw [huu _ (sub_nonneg.2 (hV.le_of_le (by omega) hlj))]

lemma gT_congr_u {u' : ℝ → ℝ} (huu : ∀ x, 0 ≤ x → u' x = u x) (hV : IncrSeq V N) (β : ℝ)
    (η : ℕ → ℝ) (m : ℕ) : gT u' β N η V m = gT u β N η V m := by
  unfold gT
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [gH_congr_u huu hV (by rw [Finset.mem_range] at hl; omega)]

/-! ### The softened selector -/

lemma softSel_denom_pos {ϑ : ℝ} {m l : ℕ} (hne : (feas N m l).Nonempty) :
    0 < ∑ j' ∈ feas N m l, Real.exp (ϑ * gobj u V m l j') :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hne

lemma softSel_nonneg (ϑ : ℝ) (m l j : ℕ) : 0 ≤ softSel u N ϑ V m l j := by
  unfold softSel; split_ifs with hj
  · exact div_nonneg (Real.exp_pos _).le (softSel_denom_pos ⟨j, hj⟩).le
  · exact le_rfl

lemma softSel_le_one (ϑ : ℝ) (m l j : ℕ) : softSel u N ϑ V m l j ≤ 1 := by
  unfold softSel; split_ifs with hj
  · rw [div_le_one (softSel_denom_pos ⟨j, hj⟩)]
    exact Finset.single_le_sum (f := fun j' => Real.exp (ϑ * gobj u V m l j'))
      (fun _ _ => (Real.exp_pos _).le) hj
  · exact zero_le_one

lemma isKernel_softSel (ϑ : ℝ) : IsKernel N (softSel u N ϑ V) := by
  refine ⟨fun m l j => softSel_nonneg ϑ m l j, fun m hm l hl => ?_⟩
  have hpos := softSel_denom_pos (u := u) (ϑ := ϑ) (V := V) (feas_nonempty hm hl)
  calc ∑ j ∈ feas N m l, softSel u N ϑ V m l j
      = ∑ j ∈ feas N m l, Real.exp (ϑ * gobj u V m l j) /
          ∑ j' ∈ feas N m l, Real.exp (ϑ * gobj u V m l j') :=
        Finset.sum_congr rfl fun j hj => ite_eq_left hj
    _ = 1 := by rw [← Finset.sum_div, div_self hpos.ne']

/-- The softened selector puts exponentially small weight on non-maximisers. -/
lemma softSel_le_exp (ϑ : ℝ) {m l j : ℕ} (hm : m ≤ N) (hl : l ≤ N) (hj : j ∈ feas N m l) :
    softSel u N ϑ V m l j ≤ Real.exp (-(ϑ * (gH u N V m l - gobj u V m l j))) := by
  obtain ⟨j0, hj0, heq⟩ := exists_gH_eq_gen (u := u) (V := V) hm hl
  rw [softSel, ite_eq_left hj, div_le_iff₀ (softSel_denom_pos ⟨j, hj⟩)]
  have h1 : Real.exp (ϑ * gH u N V m l) ≤
      ∑ j' ∈ feas N m l, Real.exp (ϑ * gobj u V m l j') := by
    rw [← heq]
    exact Finset.single_le_sum (f := fun j' => Real.exp (ϑ * gobj u V m l j'))
      (fun _ _ => (Real.exp_pos _).le) hj0
  calc Real.exp (ϑ * gobj u V m l j)
      = Real.exp (-(ϑ * (gH u N V m l - gobj u V m l j))) * Real.exp (ϑ * gH u N V m l) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

end General

/-! ### Continuity -/

section Continuity

variable {X : Type*} [TopologicalSpace X] {u : ℝ → ℝ} {N : ℕ}

lemma continuous_gobj (hu : Continuous u) {A : X → ℕ → ℝ} (hA : ∀ i, Continuous fun x => A x i)
    (m l j : ℕ) : Continuous fun x => gobj u (A x) m l j :=
  (hu.comp ((hA _).sub (hA _))).add (hA _)

lemma continuous_gH (hu : Continuous u) {A : X → ℕ → ℝ} (hA : ∀ i, Continuous fun x => A x i)
    (m l : ℕ) : Continuous fun x => gH u N (A x) m l := by
  by_cases hc : m ≤ N + (N - l)
  · simp only [gH, maxConv, dite_eq_left hc]
    exact Continuous.finset_sup'_apply (f := fun j x => A x (m - j) + sellerSeq u (A x) l j) _
      fun j _ => (hA _).add (hu.comp ((hA _).sub (hA _)))
  · simp only [gH, maxConv, dite_eq_right hc]
    exact continuous_const

lemma continuous_gT (hu : Continuous u) {A B : X → ℕ → ℝ} (hA : ∀ i, Continuous fun x => A x i)
    (hB : ∀ i, Continuous fun x => B x i) (β : ℝ) (m : ℕ) :
    Continuous fun x => gT u β N (B x) (A x) m :=
  continuous_const.mul (continuous_finsetSum _ fun l _ => (hB l).mul (continuous_gH hu hA m l))

lemma continuous_softSel (hu : Continuous u) {A : X → ℕ → ℝ}
    (hA : ∀ i, Continuous fun x => A x i) (ϑ : ℝ) (m l j : ℕ) :
    Continuous fun x => softSel u N ϑ (A x) m l j := by
  by_cases hj : j ∈ feas N m l
  · simp only [softSel, ite_eq_left hj]
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_gobj hu hA m l j))).div
      (continuous_finsetSum _ fun j' _ =>
        Real.continuous_exp.comp (continuous_const.mul (continuous_gobj hu hA m l j')))
      fun x => (softSel_denom_pos ⟨j, hj⟩).ne'
  · simp only [softSel, ite_eq_right hj]; exact continuous_const

lemma continuous_gPsi {B : X → ℕ → ℝ} {K : X → ℕ → ℕ → ℕ → ℝ}
    (hB : ∀ i, Continuous fun x => B x i) (hK : ∀ m l j, Continuous fun x => K x m l j)
    (k : ℕ) : Continuous fun x => gPsi N (B x) (K x) k :=
  continuous_const.mul (continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun l _ =>
    continuous_finsetSum _ fun j _ => (((hB m).mul (hB l)).mul (hK m l j)).mul continuous_const)

end Continuity

/-! ### Laws, kernels and the stationarity map -/

lemma isLaw_gPsi {h M : ℝ} {N : ℕ} {η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ} (hη : IsLaw h M N η)
    (hκ : IsKernel N κ) : IsLaw h M N (gPsi N η κ) :=
  ⟨gPsi_nonneg hη.nonneg hκ, sum_gPsi hκ hη.sum_one, by
    rw [mean_gPsi hκ hη.sum_one]; exact hη.mean⟩

lemma gPsi_congr_κ {N : ℕ} {η : ℕ → ℝ} {κ κ' : ℕ → ℕ → ℕ → ℝ}
    (hκ : ∀ m ≤ N, ∀ l ≤ N, ∀ j ≤ N, κ m l j = κ' m l j) (k : ℕ) :
    gPsi N η κ k = gPsi N η κ' k := by
  unfold gPsi
  congr 1
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hm hl
  rw [mem_feas (by omega) (by omega)] at hj
  rw [hκ m (by omega) l (by omega) j (by omega)]

/-! ### Constants -/

/-- The level `ϱ = min(ℓ₀, β(ū - u(C_*)))/2` of the continuation argument. -/
def rho (P : Primitives) : ℝ := min P.ℓ0 (P.β * (P.U.ubar - P.U.u P.Cstar)) / 2

lemma rho_pos (P : Primitives) : 0 < rho P := by
  have h1 := P.uniformfloor.1
  have h2 : 0 < P.β * (P.U.ubar - P.U.u P.Cstar) :=
    mul_pos P.β_pos (sub_pos.2 (P.U.lt_ubar P.Cstar_pos.le))
  unfold rho; have := lt_min h1 h2; linarith

lemma rho_lt_ℓ0 (P : Primitives) : rho P < P.ℓ0 := by
  have h1 := P.uniformfloor.1
  unfold rho; have := min_le_left P.ℓ0 (P.β * (P.U.ubar - P.U.u P.Cstar)); linarith

lemma two_rho_le (P : Primitives) : 2 * rho P ≤ P.β * (P.U.ubar - P.U.u P.Cstar) := by
  unfold rho; have := min_le_right P.ℓ0 (P.β * (P.U.ubar - P.U.u P.Cstar)); linarith

lemma β_mul_ubar_add_Cstar (P : Primitives) : P.β * (P.U.ubar + P.Cstar) = P.Cstar := by
  have hσ := P.σ_pos
  have hβ := P.β_pos
  have e : P.β * (1 + P.σ) = 1 := by rw [P.one_add_σ]; field_simp
  unfold Primitives.Cstar
  rw [eq_div_iff hσ.ne']
  calc P.β * (P.U.ubar + P.U.ubar / P.σ) * P.σ = P.U.ubar * (P.β * (1 + P.σ)) := by
        field_simp; ring
    _ = P.U.ubar := by rw [e, mul_one]

lemma u0amp_mono (P : Primitives) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    P.u0amp x ≤ P.u0amp y :=
  P.uniformfloor.2.2.2.2.1.monotoneOn hx (show y ∈ Set.Ici (0:ℝ) from hx.trans hxy) hxy

lemma u0amp_pos (P : Primitives) {x : ℝ} (hx : 0 < x) : 0 < P.u0amp x := by
  have := P.uniformfloor.2.2.2.2.1 (Set.self_mem_Ici : (0:ℝ) ∈ Set.Ici 0)
    (show x ∈ Set.Ici (0:ℝ) from hx.le) hx
  rwa [P.uniformfloor.2.2.2.1] at this

lemma R_pos (P : Primitives) {h : ℝ} {N : ℕ} (hR : P.Ramp ≤ N * h) : 0 < (N : ℝ) * h :=
  P.M_pos.trans (P.uniformfloor.2.2.1.trans_le hR)

lemma incrSeq_u0amp (P : Primitives) {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    IncrSeq (fun m : ℕ => P.u0amp (m * h)) N := by
  have hc := P.uniformfloor.2.2.2.2.2.1
  constructor
  · intro k _
    show P.u0amp (k * h) ≤ P.u0amp (((k + 1 : ℕ) : ℝ) * h)
    apply u0amp_mono P (by positivity)
    push_cast; nlinarith
  · intro k _
    show P.u0amp (((k + 2 : ℕ) : ℝ) * h) - P.u0amp (((k + 1 : ℕ) : ℝ) * h) ≤
      P.u0amp (((k + 1 : ℕ) : ℝ) * h) - P.u0amp (k * h)
    have := Molico.concave_incr_anti hc (x := k * h) (y := (k + 1) * h) (t := h) (by positivity)
      (by nlinarith) hh
    rw [show ((k : ℝ) + 1) * h + h = ((k + 2 : ℕ) : ℝ) * h by push_cast; ring,
      show (k : ℝ) * h + h = ((k + 1 : ℕ) : ℝ) * h by push_cast; ring,
      show ((k : ℝ) + 1) * h = ((k + 1 : ℕ) : ℝ) * h by push_cast; ring] at this
    exact this

/-! ### The Bellman part of the homotopy preserves the cone -/

lemma gT_le_bound (P : Primitives) {N : ℕ} {V η : ℕ → ℝ} (hV : InCone P.Cstar N V)
    (hη0 : ∀ l, 0 ≤ η l) (hη1 : ∑ l ∈ range (N + 1), η l = 1) {m : ℕ} (hm : m ≤ N) :
    gT P.U.u P.β N η V m ≤ P.β * (P.U.u P.Cstar + P.Cstar) := by
  unfold gT
  refine mul_le_mul_of_nonneg_left ?_ P.β_pos.le
  have hVm0 := hV.incr.nonneg hV.zero hm
  have hVmC := hV.le m hm
  have hu := P.U.monotoneOn (show V m ∈ Set.Ici (0:ℝ) from hVm0)
    (show P.Cstar ∈ Set.Ici (0:ℝ) from P.Cstar_pos.le) hVmC
  calc ∑ l ∈ range (N + 1), η l * gH P.U.u N V m l
      ≤ ∑ l ∈ range (N + 1), η l * (P.U.u P.Cstar + P.Cstar) := by
        refine Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left ?_ (hη0 l)
        have := gH_le P.U hV.incr hV.zero hm (l := l) (by rw [Finset.mem_range] at hl; omega)
        linarith
    _ = P.U.u P.Cstar + P.Cstar := by rw [← Finset.sum_mul, hη1, one_mul]

lemma gT_nonneg (P : Primitives) {N : ℕ} {V η : ℕ → ℝ} (hV : InCone P.Cstar N V)
    (hη0 : ∀ l, 0 ≤ η l) {m : ℕ} (hm : m ≤ N) : 0 ≤ gT P.U.u P.β N η V m :=
  mul_nonneg P.β_pos.le (Finset.sum_nonneg fun l hl => mul_nonneg (hη0 l)
    (gH_nonneg P.U hV.incr hV.zero hm (by rw [Finset.mem_range] at hl; omega)))

lemma incrSeq_gT (P : Primitives) {N : ℕ} {V η : ℕ → ℝ} (hV : InCone P.Cstar N V)
    (hη0 : ∀ l, 0 ≤ η l) : IncrSeq (fun m => gT P.U.u P.β N η V m) N :=
  incrSeq_smul P.β_pos.le (incrSeq_sum _ (fun l _ => hη0 l) fun l hl =>
    ⟨fun _ hk => gH_mono P.U hV.incr hk (by rw [Finset.mem_range] at hl; omega),
     fun _ hk => gH_concave P.U hV.incr hk (by rw [Finset.mem_range] at hl; omega)⟩)

lemma bell_inCone (P : Primitives) {h : ℝ} (hh : 0 < h) {N : ℕ} {V η : ℕ → ℝ}
    (hV : InCone P.Cstar N V) (hη : IsLaw h P.M N η) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a * P.u0amp (N * h) ≤ P.β * (P.U.ubar - P.U.u P.Cstar)) :
    InCone P.Cstar N (fun m => gT P.U.u P.β N η V m + a * P.u0amp (m * h)) := by
  refine ⟨?_, incrSeq_add (incrSeq_gT P hV hη.nonneg) (incrSeq_smul ha0 (incrSeq_u0amp P hh.le N)),
    fun i hi => ?_⟩
  · show gT P.U.u P.β N η V 0 + a * P.u0amp (((0 : ℕ) : ℝ) * h) = 0
    have e : gT P.U.u P.β N η V 0 = 0 := by
      unfold gT
      rw [Finset.sum_eq_zero fun l hl => by
        rw [gH_zero P.U hV.zero (by rw [Finset.mem_range] at hl; omega), mul_zero], mul_zero]
    rw [e, Nat.cast_zero, zero_mul, P.uniformfloor.2.2.2.1, mul_zero, add_zero]
  · show gT P.U.u P.β N η V i + a * P.u0amp (i * h) ≤ P.Cstar
    have h1 := gT_le_bound P hV hη.nonneg hη.sum_one hi
    have h2 : a * P.u0amp (i * h) ≤ a * P.u0amp (N * h) :=
      mul_le_mul_of_nonneg_left (u0amp_mono P (by positivity)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh.le)) ha0
    calc gT P.U.u P.β N η V i + a * P.u0amp (i * h)
        ≤ P.β * (P.U.u P.Cstar + P.Cstar) + P.β * (P.U.ubar - P.U.u P.Cstar) := by linarith
      _ = P.β * (P.U.ubar + P.Cstar) := by ring
      _ = P.Cstar := β_mul_ubar_add_Cstar P

/-! ### The compact convex set `D = 𝒦_{h,R} × 𝒫_M(𝒳)` -/

/-- The state space `ℝ^{N+1} × ℝ^{N+1}` of pairs `(V, η)`. -/
abbrev St (N : ℕ) := (Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)

/-- Kernel tensors on `{0,…,N}³`. -/
abbrev KSp (N : ℕ) := Fin (N + 1) → Fin (N + 1) → Fin (N + 1) → ℝ

/-- The set `D = 𝒦_{h,R} × 𝒫_M(𝒳)`. -/
def stateSet (P : Primitives) (h : ℝ) (N : ℕ) : Set (St N) :=
  {p | InCone P.Cstar N (toSeq p.1) ∧ IsLaw h P.M N (toSeq p.2)}

lemma isClosed_stateSet (P : Primitives) (h : ℝ) (N : ℕ) : IsClosed (stateSet P h N) := by
  have c1 : ∀ i, Continuous fun p : St N => toSeq p.1 i := fun i =>
    (continuous_toSeq_apply N i).comp continuous_fst
  have c2 : ∀ i, Continuous fun p : St N => toSeq p.2 i := fun i =>
    (continuous_toSeq_apply N i).comp continuous_snd
  have e : stateSet P h N =
      {p | toSeq p.1 0 = 0} ∩ (⋂ k, ⋂ (_ : k < N), {p | toSeq p.1 k ≤ toSeq p.1 (k + 1)}) ∩
      (⋂ k, ⋂ (_ : k + 2 ≤ N), {p | toSeq p.1 (k + 2) - toSeq p.1 (k + 1) ≤
        toSeq p.1 (k + 1) - toSeq p.1 k}) ∩
      (⋂ i, ⋂ (_ : i ≤ N), {p | toSeq p.1 i ≤ P.Cstar}) ∩ (⋂ l, {p | 0 ≤ toSeq p.2 l}) ∩
      {p | ∑ l ∈ range (N + 1), toSeq p.2 l = 1} ∩
      {p | ∑ l ∈ range (N + 1), toSeq p.2 l * (l * h) = P.M} := by
    ext p
    simp only [stateSet, Set.mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨⟨h0, ⟨hmono, hconc⟩, hle⟩, ⟨hnn, hs, hmean⟩⟩
      exact ⟨⟨⟨⟨⟨⟨h0, hmono⟩, hconc⟩, hle⟩, hnn⟩, hs⟩, hmean⟩
    · rintro ⟨⟨⟨⟨⟨⟨h0, hmono⟩, hconc⟩, hle⟩, hnn⟩, hs⟩, hmean⟩
      exact ⟨⟨h0, ⟨hmono, hconc⟩, hle⟩, ⟨hnn, hs, hmean⟩⟩
  rw [e]
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter
    (IsClosed.inter ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact isClosed_eq (c1 0) continuous_const
  · exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_le (c1 k) (c1 (k + 1))
  · exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le ((c1 _).sub (c1 _)) ((c1 _).sub (c1 _))
  · exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_le (c1 i) continuous_const
  · exact isClosed_iInter fun l => isClosed_le continuous_const (c2 l)
  · exact isClosed_eq (continuous_finsetSum _ fun l _ => c2 l) continuous_const
  · exact isClosed_eq (continuous_finsetSum _ fun l _ => (c2 l).mul continuous_const)
      continuous_const

lemma isCompact_stateSet (P : Primitives) (h : ℝ) (N : ℕ) : IsCompact (stateSet P h N) := by
  have hK : IsCompact ((Set.pi univ fun _ : Fin (N + 1) => Icc (0:ℝ) P.Cstar) ×ˢ
      (Set.pi univ fun _ : Fin (N + 1) => Icc (0:ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  refine hK.of_isClosed_subset (isClosed_stateSet P h N) ?_
  rintro ⟨v, w⟩ ⟨hv, hw⟩
  refine ⟨fun i _ => ?_, fun i _ => ?_⟩
  · have h0 := hv.incr.nonneg hv.zero (Nat.le_of_lt_succ i.2)
    have h1 := hv.le i (Nat.le_of_lt_succ i.2)
    rw [toSeq_fin] at h0 h1
    exact ⟨h0, h1⟩
  · have h0 := hw.nonneg i
    have h1 : toSeq w i ≤ ∑ l ∈ range (N + 1), toSeq w l :=
      Finset.single_le_sum (f := fun l => toSeq w l) (fun l _ => hw.nonneg l)
        (Finset.mem_range.2 i.2)
    rw [hw.sum_one, toSeq_fin] at h1
    rw [toSeq_fin] at h0
    exact ⟨h0, h1⟩

lemma convex_stateSet (P : Primitives) (h : ℝ) (N : ℕ) : Convex ℝ (stateSet P h N) := by
  rintro ⟨v, w⟩ ⟨hv, hw⟩ ⟨v', w'⟩ ⟨hv', hw'⟩ a b ha hb hab
  refine ⟨inCone_of_eq (inCone_convex hv hv' ha hb hab) fun i _ => ?_,
    isLaw_of_eq (isLaw_convex hw hw' ha hb hab) (fun i _ => ?_) fun i => ?_⟩
  · simp [toSeq_add_smul]
  · simp [toSeq_add_smul]
  · have := (isLaw_convex hw hw' ha hb hab).nonneg i
    simpa [toSeq_add_smul] using this

/-- The law `(1 - M/R) δ₀ + (M/R) δ_R`. -/
def law0 (P : Primitives) (h : ℝ) (N : ℕ) (l : ℕ) : ℝ :=
  (1 - P.M / (N * h)) * (if l = 0 then 1 else 0) + P.M / (N * h) * (if l = N then 1 else 0)

lemma isLaw_law0 (P : Primitives) {h : ℝ} {N : ℕ} (hR : P.Ramp ≤ N * h) :
    IsLaw h P.M N (law0 P h N) := by
  have hMR : P.M < N * h := P.uniformfloor.2.2.1.trans_le hR
  have hR0 : 0 < (N : ℝ) * h := R_pos P hR
  have hq0 : 0 ≤ P.M / (N * h) := div_nonneg P.M_pos.le hR0.le
  have hq1 : P.M / (N * h) ≤ 1 := (div_le_one hR0).2 hMR.le
  refine ⟨fun l => ?_, ?_, ?_⟩
  · unfold law0; split_ifs <;> nlinarith
  · simp [law0, Finset.sum_add_distrib]
  · simp only [law0, add_mul, Finset.sum_add_distrib, mul_assoc, ite_mul, one_mul, zero_mul,
      ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_range]
    simp only [Nat.lt_succ_self, Nat.zero_lt_succ, ite_true, Nat.cast_zero, zero_mul, mul_zero,
      zero_add]
    exact div_mul_cancel₀ _ hR0.ne'

lemma stateSet_nonempty (P : Primitives) {h : ℝ} {N : ℕ} (hR : P.Ramp ≤ N * h) :
    (stateSet P h N).Nonempty := by
  refine ⟨(0, fun i => law0 P h N i), ?_, ?_⟩
  · refine inCone_of_eq (f := fun _ => 0)
      ⟨rfl, ⟨fun _ _ => le_rfl, fun _ _ => by simp⟩, fun _ _ => P.Cstar_pos.le⟩ fun i _ => ?_
    simp [toSeq]
  · exact isLaw_of_eq (isLaw_law0 P hR) (fun i hi => (toSeq_ofFun _ hi).symm)
      (toSeq_nonneg fun i => (isLaw_law0 P hR).nonneg i)

/-! ### The homotopy `Θ^ϑ_t` -/

/-- The continuous extension `x ↦ u(max x 0)` of the utility. -/
def uExt (P : Primitives) : ℝ → ℝ := Molico.posPart P.U.u

lemma continuous_uExt (P : Primitives) : Continuous (uExt P) :=
  continuous_posPart P.U.continuousOn

lemma uExt_eq (P : Primitives) {x : ℝ} (hx : 0 ≤ x) : uExt P x = P.U.u x := posPart_eq hx

/-- Bellman component of `Θ^ϑ_t`: `T_η V + (2tϱ/u₀(R)) u₀`. -/
def bellComp (P : Primitives) (h : ℝ) (N : ℕ) (t : ℝ) (p : St N) (m : ℕ) : ℝ :=
  gT (uExt P) P.β N (toSeq p.2) (toSeq p.1) m +
    2 * t * rho P / P.u0amp (N * h) * P.u0amp (m * h)

/-- Law component of `Θ^ϑ_t`: `Ψ_{κ^ϑ(V)}(η)`. -/
def lawComp (P : Primitives) (N : ℕ) (ϑ : ℝ) (p : St N) (k : ℕ) : ℝ :=
  gPsi N (toSeq p.2) (softSel (uExt P) N ϑ (toSeq p.1)) k

/-- The homotopy `Θ^ϑ_t`. -/
def homot (P : Primitives) (h : ℝ) (N : ℕ) (ϑ t : ℝ) (p : St N) : St N :=
  (fun m => bellComp P h N t p m, fun k => lawComp P N ϑ p k)

lemma continuous_homot (P : Primitives) (h : ℝ) (N : ℕ) (ϑ : ℝ) :
    Continuous fun q : ℝ × St N => homot P h N ϑ q.1 q.2 := by
  have cV : ∀ i, Continuous fun q : ℝ × St N => toSeq q.2.1 i := fun i =>
    (continuous_toSeq_apply N i).comp (continuous_fst.comp continuous_snd)
  have cη : ∀ i, Continuous fun q : ℝ × St N => toSeq q.2.2 i := fun i =>
    (continuous_toSeq_apply N i).comp (continuous_snd.comp continuous_snd)
  unfold homot bellComp lawComp
  refine Continuous.prodMk (continuous_pi fun m => ?_) (continuous_pi fun k => ?_)
  · exact (continuous_gT (continuous_uExt P) cV cη _ _).add (by fun_prop)
  · exact continuous_gPsi cη (fun m l j => continuous_softSel (continuous_uExt P) cV _ m l j) _

lemma mapsTo_homot (P : Primitives) {h : ℝ} (hh : 0 < h) {N : ℕ} (hR : P.Ramp ≤ N * h)
    (ϑ : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    MapsTo (homot P h N ϑ t) (stateSet P h N) (stateSet P h N) := by
  rintro p ⟨hV, hη⟩
  have hu0 := u0amp_pos P (R_pos P hR)
  have ha0 : 0 ≤ 2 * t * rho P / P.u0amp (N * h) :=
    div_nonneg (mul_nonneg (mul_nonneg zero_le_two ht.1) (rho_pos P).le) hu0.le
  have ha : 2 * t * rho P / P.u0amp (N * h) * P.u0amp (N * h) ≤
      P.β * (P.U.ubar - P.U.u P.Cstar) := by
    rw [div_mul_cancel₀ _ hu0.ne']
    have := two_rho_le P; have := rho_pos P; have := ht.2
    nlinarith
  have hκ : IsKernel N (softSel (uExt P) N ϑ (toSeq p.1)) := isKernel_softSel ϑ
  refine ⟨inCone_of_eq (bell_inCone P hh hV hη ha0 ha) fun i hi => ?_,
    isLaw_of_eq (isLaw_gPsi hη hκ) (fun i hi => ?_)
      (toSeq_nonneg fun k => gPsi_nonneg hη.nonneg hκ k)⟩
  · show _ = toSeq (fun m : Fin (N + 1) => bellComp P h N t p m) i
    rw [toSeq_ofFun _ hi, bellComp, gT_congr_u (fun x hx => uExt_eq P hx) hV.incr]
  · show _ = toSeq (fun k : Fin (N + 1) => lawComp P N ϑ p k) i
    rw [toSeq_ofFun _ hi, lawComp]

lemma homot_fix (P : Primitives) {h : ℝ} {N : ℕ} {ϑ t : ℝ} {p : St N}
    (hfix : homot P h N ϑ t p = p) (hV : IncrSeq (toSeq p.1) N) {m : ℕ} (hm : m ≤ N) :
    toSeq p.1 m = gT P.U.u P.β N (toSeq p.2) (toSeq p.1) m +
        2 * t * rho P / P.u0amp (N * h) * P.u0amp (m * h) ∧
      toSeq p.2 m = gPsi N (toSeq p.2) (softSel (uExt P) N ϑ (toSeq p.1)) m := by
  have e1 := congrArg (fun q : St N => toSeq q.1 m) hfix
  have e2 := congrArg (fun q : St N => toSeq q.2 m) hfix
  simp only [homot] at e1 e2
  rw [toSeq_ofFun _ hm, bellComp, gT_congr_u (fun x hx => uExt_eq P hx) hV] at e1
  rw [toSeq_ofFun _ hm, lawComp] at e2
  exact ⟨e1.symm, e2.symm⟩

/-- Step 2: for every `ϑ`, the continuation principle gives a fixed point of `Θ^ϑ_0` in `D`
with `V(R) > ϱ`. -/
lemma exists_soft_fixed (P : Primitives) {h : ℝ} (hh : 0 < h) {N : ℕ} (hR : P.Ramp ≤ N * h)
    (ϑ : ℝ) :
    ∃ p ∈ stateSet P h N,
      (∀ m ≤ N, toSeq p.1 m = gT (uExt P) P.β N (toSeq p.2) (toSeq p.1) m) ∧
      (∀ k ≤ N, toSeq p.2 k = gPsi N (toSeq p.2) (softSel (uExt P) N ϑ (toSeq p.1)) k) ∧
      rho P < p.1 (Fin.last N) := by
  have hu0 := u0amp_pos P (R_pos P hR)
  -- admissibility: no fixed point on the level set `V(R) = ϱ`
  have hadm : ∀ t ∈ Icc (0:ℝ) 1, ∀ p ∈ stateSet P h N, homot P h N ϑ t p = p →
      p.1 (Fin.last N) ≠ rho P := by
    rintro t ht p ⟨hV, hη⟩ hfix hg
    have hτ : 0 ≤ 2 * t * rho P / P.u0amp (N * h) :=
      div_nonneg (mul_nonneg (mul_nonneg zero_le_two ht.1) (rho_pos P).le) hu0.le
    rcases P.uniformfloor.2.2.2.2.2.2.2 hh hR hη hτ hV (fun m hm => by
      linarith [(homot_fix P hfix hV.incr hm).1]) with h0 | h0
    · have := h0.1 N le_rfl
      rw [toSeq_last] at this
      have := rho_pos P; linarith
    · rw [toSeq_last] at h0
      have := rho_lt_ℓ0 P; linarith
  -- `Θ^ϑ_1` has no fixed point with `V(R) ≤ ϱ`
  have hone : ∀ p ∈ stateSet P h N, homot P h N ϑ 1 p = p → rho P < p.1 (Fin.last N) := by
    rintro p ⟨hV, hη⟩ hfix
    have h1 := (homot_fix P hfix hV.incr le_rfl).1
    rw [div_mul_cancel₀ _ hu0.ne', toSeq_last] at h1
    have := gT_nonneg P hV hη.nonneg (le_refl N)
    have := rho_pos P
    linarith
  obtain ⟨p, hpD, hfix, hgt⟩ := continuation (isCompact_stateSet P h N) (convex_stateSet P h N)
    (stateSet_nonempty P hR) (continuous_homot P h N ϑ).continuousOn
    (fun t ht => mapsTo_homot P hh hR ϑ ht) (g := fun p : St N => p.1 (Fin.last N))
    ((continuous_apply _).comp continuous_fst).continuousOn (ϱ := rho P) hadm hone
  refine ⟨p, hpD, fun m hm => ?_, fun k hk => (homot_fix P hfix hpD.1.incr hk).2, hgt⟩
  have := (homot_fix P hfix hpD.1.incr hm).1
  rw [gT_congr_u (fun x hx => uExt_eq P hx) hpD.1.incr]
  simpa using this

/-! ### The limit `ϑ → ∞` -/

/-- Kernel tensors with entries in `[0,1]`. -/
def kernelBox (N : ℕ) : Set (KSp N) := {κ | ∀ a b c, κ a b c ∈ Icc (0:ℝ) 1}

lemma isCompact_kernelBox (N : ℕ) : IsCompact (kernelBox N) := by
  have e : kernelBox N =
      Set.pi univ fun _ => Set.pi univ fun _ => Set.pi univ fun _ => Icc (0:ℝ) 1 := by
    ext κ
    exact ⟨fun h a _ b _ c _ => h a b c,
      fun h a b c => h a (mem_univ _) b (mem_univ _) c (mem_univ _)⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_Icc

/-- The softened selector as a kernel tensor on `{0,…,N}³`. -/
def softTensor (P : Primitives) (N : ℕ) (ϑ : ℝ) (v : Fin (N + 1) → ℝ) : KSp N :=
  fun a b c => softSel (uExt P) N ϑ (toSeq v) a b c

lemma toSeq3_softTensor (P : Primitives) {N : ℕ} (ϑ : ℝ) (v : Fin (N + 1) → ℝ) {m l j : ℕ}
    (hm : m ≤ N) (hl : l ≤ N) (hj : j ≤ N) :
    toSeq3 (softTensor P N ϑ v) m l j = softSel (uExt P) N ϑ (toSeq v) m l j :=
  toSeq3_ofFun _ hm hl hj

lemma lim_eq {X : Type*} [TopologicalSpace X] {y : ℕ → X} {a : X} (hy : Tendsto y atTop (𝓝 a))
    {F G : X → ℝ} (hF : Continuous F) (hG : Continuous G) (h : ∀ i, F (y i) = G (y i)) :
    F a = G a := by
  have h1 := (hF.tendsto a).comp hy
  have h2 := (hG.tendsto a).comp hy
  have e : F ∘ y = G ∘ y := funext h
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

lemma lim_le {X : Type*} [TopologicalSpace X] {y : ℕ → X} {a : X} (hy : Tendsto y atTop (𝓝 a))
    {F G : X → ℝ} (hF : Continuous F) (hG : Continuous G) (h : ∀ i, F (y i) ≤ G (y i)) :
    F a ≤ G a :=
  le_of_tendsto_of_tendsto' ((hF.tendsto a).comp hy) ((hG.tendsto a).comp hy) h

/-- Steps 3–4: the limit `ϑ → ∞` of the soft fixed points is an approximant equilibrium with
`V(R) ≥ ϱ > 0`, hence `ℓ₀ ≤ V(R) ≤ L_*` by `cor:uniformfloor`. -/
theorem approx_aux (P : Primitives) {h : ℝ} (hh : 0 < h) {N : ℕ} (hR : P.Ramp ≤ N * h) :
    ∃ V η : ℕ → ℝ, ∃ κ : ℕ → ℕ → ℕ → ℝ,
      IsApproxEq P h N V η κ ∧ P.ℓ0 ≤ V N ∧ V N ≤ P.Lstar := by
  choose p hpD hbell hstat hgt using fun i : ℕ => exists_soft_fixed P hh hR ((i : ℝ) + 1)
  have hxS : ∀ i, (p i, softTensor P N ((i : ℝ) + 1) (p i).1) ∈ stateSet P h N ×ˢ kernelBox N :=
    fun i => ⟨hpD i, fun _ _ _ => ⟨softSel_nonneg _ _ _ _, softSel_le_one _ _ _ _⟩⟩
  obtain ⟨⟨q, κ⟩, hqκ, φ, hφ, hlim⟩ :=
    ((isCompact_stateSet P h N).prod (isCompact_kernelBox N)).tendsto_subseq hxS
  have hqD : q ∈ stateSet P h N := hqκ.1
  have hκK : κ ∈ kernelBox N := hqκ.2
  have hu := continuous_uExt P
  have huu : ∀ x, 0 ≤ x → uExt P x = P.U.u x := fun x hx => uExt_eq P hx
  have cV : ∀ i, Continuous fun z : St N × KSp N => toSeq z.1.1 i := fun i =>
    (continuous_toSeq_apply N i).comp (continuous_fst.comp continuous_fst)
  have cη : ∀ i, Continuous fun z : St N × KSp N => toSeq z.1.2 i := fun i =>
    (continuous_toSeq_apply N i).comp (continuous_snd.comp continuous_fst)
  have cκ : ∀ m l j, Continuous fun z : St N × KSp N => toSeq3 z.2 m l j := fun m l j =>
    (continuous_toSeq3_apply N m l j).comp continuous_snd
  have hqV : InCone P.Cstar N (toSeq q.1) := hqD.1
  have hqη : IsLaw h P.M N (toSeq q.2) := hqD.2
  -- the Bellman equation in the limit
  have hbellq : ∀ m ≤ N, toSeq q.1 m = gT P.U.u P.β N (toSeq q.2) (toSeq q.1) m := by
    intro m hm
    rw [← gT_congr_u huu hqV.incr]
    exact lim_eq hlim (F := fun z : St N × KSp N => toSeq z.1.1 m)
      (G := fun z => gT (uExt P) P.β N (toSeq z.1.2) (toSeq z.1.1) m) (cV m)
      (continuous_gT hu cV cη _ _) fun i => hbell (φ i) m hm
  -- stationarity in the limit
  have hstatq : ∀ k ≤ N, toSeq q.2 k = gPsi N (toSeq q.2) (toSeq3 κ) k := by
    intro k hk
    refine lim_eq hlim (F := fun z : St N × KSp N => toSeq z.1.2 k)
      (G := fun z => gPsi N (toSeq z.1.2) (toSeq3 z.2) k) (cη k) (continuous_gPsi cη cκ k)
      fun i => ?_
    show toSeq (p (φ i)).2 k =
      gPsi N (toSeq (p (φ i)).2) (toSeq3 (softTensor P N ((φ i : ℝ) + 1) (p (φ i)).1)) k
    rw [hstat (φ i) k hk]
    exact gPsi_congr_κ (fun m hm l hl j hj => (toSeq3_softTensor P _ _ hm hl hj).symm) k
  -- the kernel property in the limit
  have hκnn : ∀ m l j, 0 ≤ toSeq3 κ m l j := by
    intro m l j
    unfold toSeq3
    split_ifs with hc
    · exact (hκK _ _ _).1
    · exact le_rfl
  have hsum : ∀ m ≤ N, ∀ l ≤ N, ∑ j ∈ feas N m l, toSeq3 κ m l j = 1 := by
    intro m hm l hl
    refine lim_eq hlim (F := fun z : St N × KSp N => ∑ j ∈ feas N m l, toSeq3 z.2 m l j)
      (G := fun _ => 1) (continuous_finsetSum _ fun j _ => cκ m l j) continuous_const
      fun i => ?_
    show ∑ j ∈ feas N m l, toSeq3 (softTensor P N ((φ i : ℝ) + 1) (p (φ i)).1) m l j = 1
    rw [Finset.sum_congr rfl fun j hj => toSeq3_softTensor P _ _ hm hl
      (by have := ((mem_feas hm hl).1 hj).2; omega)]
    exact (isKernel_softSel _).sum_one m hm l hl
  -- the amplitude in the limit
  have hVN : rho P ≤ toSeq q.1 N := by
    refine lim_le hlim (F := fun _ => rho P) (G := fun z : St N × KSp N => toSeq z.1.1 N)
      continuous_const (cV N) fun i => ?_
    show rho P ≤ toSeq (p (φ i)).1 N
    rw [toSeq_last]; exact (hgt (φ i)).le
  -- the limit kernel is supported on maximisers
  have hargmax : OnArgmax P.U.u N (toSeq q.1) (toSeq3 κ) := by
    intro m hm l hl j hj hne
    have hlj : l + j ≤ N := ((mem_feas hm hl).1 hj).2
    rw [← gobj_congr_u huu hqV.incr hlj, ← gH_congr_u huu hqV.incr hl]
    by_contra hneq
    have hlt : gobj (uExt P) (toSeq q.1) m l j < gH (uExt P) N (toSeq q.1) m l :=
      lt_of_le_of_ne (gobj_le_gH_gen hj) hneq
    set γ := gH (uExt P) N (toSeq q.1) m l - gobj (uExt P) (toSeq q.1) m l j with hγ
    have hγ0 : 0 < γ := sub_pos.2 hlt
    have hFc : Continuous fun z : St N × KSp N =>
        gH (uExt P) N (toSeq z.1.1) m l - gobj (uExt P) (toSeq z.1.1) m l j :=
      (continuous_gH hu cV m l).sub (continuous_gobj hu cV m l j)
    have hev : ∀ᶠ i in atTop, γ / 2 <
        gH (uExt P) N (toSeq (p (φ i)).1) m l - gobj (uExt P) (toSeq (p (φ i)).1) m l j :=
      ((hFc.tendsto _).comp hlim).eventually (lt_mem_nhds (show γ / 2 < γ by linarith))
    have hub : Tendsto (fun i => Real.exp (-(((φ i : ℝ) + 1) * (γ / 2)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i => (φ i : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
      exact Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (h1.atTop_mul_const (by linarith)))
    have hle : toSeq3 κ m l j ≤ 0 := by
      refine le_of_tendsto_of_tendsto (((cκ m l j).tendsto _).comp hlim) hub ?_
      filter_upwards [hev] with i hi
      show toSeq3 (softTensor P N ((φ i : ℝ) + 1) (p (φ i)).1) m l j ≤ _
      rw [toSeq3_softTensor P _ _ hm hl (by omega)]
      refine (softSel_le_exp _ hm hl hj).trans (Real.exp_le_exp.2 ?_)
      have hφ0 : (0:ℝ) ≤ (φ i : ℝ) + 1 := by positivity
      have := mul_le_mul_of_nonneg_left hi.le hφ0
      linarith
    exact hne (le_antisymm hle (hκnn m l j))
  have hEq : IsApproxEq P h N (toSeq q.1) (toSeq q.2) (toSeq3 κ) :=
    ⟨hqV, hqη, ⟨hκnn, hsum⟩, hargmax, hbellq, hstatq⟩
  have hne : ∃ i ≤ N, toSeq q.1 i ≠ 0 := ⟨N, le_rfl, (lt_of_lt_of_le (rho_pos P) hVN).ne'⟩
  obtain ⟨h1, h2⟩ := P.uniformfloor_fixed hh hR hqη hqV hbellq hne
  exact ⟨_, _, _, hEq, h1, h2⟩

end Grid

/-- `thm:approx`: existence of an approximant equilibrium at fixed `(h, R)` with the amplitude
floor `eq:floor`, `ℓ₀ ≤ V(R) ≤ L_*`. -/
theorem approx (P : Primitives) {h : ℝ} (hh : 0 < h) {N : ℕ} (hR : P.Ramp ≤ N * h) :
    ∃ V η : ℕ → ℝ, ∃ κ : ℕ → ℕ → ℕ → ℝ,
      Grid.IsApproxEq P h N V η κ ∧ P.ℓ0 ≤ V N ∧ V N ≤ P.Lstar :=
  Grid.approx_aux P hh hR

end Molico
