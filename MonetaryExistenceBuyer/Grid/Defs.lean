import MonetaryExistenceBuyer.Utility
import MonetaryExistenceBuyer.Prelim.Incr

/-!
# The finite approximant (`def:approx`)

The grid is `𝒳 = {0, h, …, R}` with `R = N h`. Everything is written in *index form*: a grid
value function is `V : ℕ → ℝ` with `V i` the value at wealth `i h` (only `i ≤ N` matters). A
seller of wealth `s = l h` and a buyer of wealth `m h` can trade a grid transfer `j h` with
`j ≤ m` and `l + j ≤ N` (the fixed finite set `F(m,s)`).

In index form the Bellman operator of `eq:bellman` does not depend on the mesh `h`. The mesh only
enters through the mean constraint of the laws in `𝒫_M(𝒳)`.

Formalized here:
* `feas`, `gobj`, `gH`, `gT`: `F(m,s)`, the grid objective, `H_V`, `T_η V` (`eq:bellman`);
* `InCone`: the cone `𝒦_{h,R}`; `IsLaw`: `𝒫_M(𝒳)`; `IsKernel`, `OnArgmax`: `𝒬(V)`;
* `gPsi`: the stationarity map `Ψ_κ` (`eq:push`) and its mass/mean preservation;
* `IsApproxEq`: approximant equilibria;
* concavity preservation of `H_V(·,s)` via `lem:incr` (Step 1 of `thm:approx`).
-/

open Finset

noncomputable section

namespace Molico

namespace Grid

/-- Feasible transfer indices `F(m,s)` for buyer index `m ≤ N` and seller index `l ≤ N`:
`{j : j ≤ m, l + j ≤ N}` (written as the split set of `lem:incr`). -/
def feas (N m l : ℕ) : Finset ℕ := convSet N (N - l) m

lemma mem_feas {N m l j : ℕ} (hm : m ≤ N) (hl : l ≤ N) : j ∈ feas N m l ↔ j ≤ m ∧ l + j ≤ N := by
  rw [feas, mem_convSet]; omega

lemma zero_mem_feas {N m l : ℕ} (hm : m ≤ N) (hl : l ≤ N) : 0 ∈ feas N m l := by
  rw [mem_feas hm hl]; omega

lemma feas_nonempty {N m l : ℕ} (hm : m ≤ N) (hl : l ≤ N) : (feas N m l).Nonempty :=
  ⟨0, zero_mem_feas hm hl⟩

/-- The grid objective `φ_{V,m,s}(j) = u(V(l+j) - V(l)) + V(m-j)`. -/
def gobj (u : ℝ → ℝ) (V : ℕ → ℝ) (m l j : ℕ) : ℝ := u (V (l + j) - V l) + V (m - j)

/-- The seller-side cumulative sequence `j ↦ u(V(l+j) - V(l))`. -/
def sellerSeq (u : ℝ → ℝ) (V : ℕ → ℝ) (l : ℕ) (j : ℕ) : ℝ := u (V (l + j) - V l)

/-- `eq:bellman`: the grid maximized payoff `H_V(m,s)`, the max-plus convolution of `V` with the
seller sequence. -/
def gH (u : ℝ → ℝ) (N : ℕ) (V : ℕ → ℝ) (m l : ℕ) : ℝ :=
  maxConv V (sellerSeq u V l) N (N - l) m

/-- `eq:bellman`: `(T_η V)(m) = β ∑_l η_l H_V(m, l)`. -/
def gT (u : ℝ → ℝ) (β : ℝ) (N : ℕ) (η V : ℕ → ℝ) (m : ℕ) : ℝ :=
  β * ∑ l ∈ range (N + 1), η l * gH u N V m l

/-- The cone `𝒦_{h,R}`: nondecreasing discretely concave `V` with `V(0) = 0` and `V ≤ C`. -/
structure InCone (C : ℝ) (N : ℕ) (V : ℕ → ℝ) : Prop where
  zero : V 0 = 0
  incr : IncrSeq V N
  le : ∀ i ≤ N, V i ≤ C

/-- `𝒫_M(𝒳)`: laws on the grid of mean exactly `M` (weights `η l` at wealth `l h`). -/
structure IsLaw (h M : ℝ) (N : ℕ) (η : ℕ → ℝ) : Prop where
  nonneg : ∀ l, 0 ≤ η l
  sum_one : ∑ l ∈ range (N + 1), η l = 1
  mean : ∑ l ∈ range (N + 1), η l * (l * h) = M

/-- Transfer kernels: `κ m l` is a probability vector on `F(m,s)`. -/
structure IsKernel (N : ℕ) (κ : ℕ → ℕ → ℕ → ℝ) : Prop where
  nonneg : ∀ m l j, 0 ≤ κ m l j
  sum_one : ∀ m ≤ N, ∀ l ≤ N, ∑ j ∈ feas N m l, κ m l j = 1

/-- `𝒬(V)`: the kernel is supported on maximisers of `eq:bellman`. -/
def OnArgmax (u : ℝ → ℝ) (N : ℕ) (V : ℕ → ℝ) (κ : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ m ≤ N, ∀ l ≤ N, ∀ j ∈ feas N m l, κ m l j ≠ 0 → gobj u V m l j = gH u N V m l

/-- `eq:push`: `Ψ_κ(η) = ½ B_# Γ + ½ S_# Γ`, with `Γ(b,s,d) = η(b) η(s) κ_{b,s}(d)`;
the buyer lands at `m - j`, the seller at `l + j`. -/
def gPsi (N : ℕ) (η : ℕ → ℝ) (κ : ℕ → ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  2⁻¹ * ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), ∑ j ∈ feas N m l,
    η m * η l * κ m l j * ((if m - j = k then 1 else 0) + (if l + j = k then 1 else 0))

/-- `def:approx`: an approximant equilibrium `(V, η, κ) ∈ 𝒦_{h,R} × 𝒫_M(𝒳) × 𝒬(V)` with
`V = T_η V` and `η = Ψ_κ(η)`. -/
structure IsApproxEq (P : Primitives) (h : ℝ) (N : ℕ) (V η : ℕ → ℝ)
    (κ : ℕ → ℕ → ℕ → ℝ) : Prop where
  cone : InCone P.Cstar N V
  law : IsLaw h P.M N η
  kernel : IsKernel N κ
  argmax : OnArgmax P.U.u N V κ
  bellman : ∀ m ≤ N, V m = gT P.U.u P.β N η V m
  stationary : ∀ k ≤ N, η k = gPsi N η κ k

/-! ### Discrete concavity -/

section IncrSeq

variable {V : ℕ → ℝ} {N : ℕ}

lemma _root_.Molico.IncrSeq.le_of_le (hV : IncrSeq V N) {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ N) : V x ≤ V y := by
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ n hxn ih => exact (ih (by omega)).trans (hV.mono n (by omega))

/-- Increments of a discretely concave sequence are nonincreasing. -/
lemma _root_.Molico.IncrSeq.step_anti (hV : IncrSeq V N) {x y : ℕ} (hxy : x ≤ y) (hy : y + 1 ≤ N) :
    V (y + 1) - V y ≤ V (x + 1) - V x := by
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ n hxn ih =>
    have := hV.concave n (by omega)
    linarith [ih (by omega)]

/-- Increments over a fixed step `t` decrease with the base point. -/
lemma _root_.Molico.IncrSeq.incr_anti (hV : IncrSeq V N) {x y t : ℕ} (hxy : x ≤ y) (hyt : y + t ≤ N) :
    V (y + t) - V y ≤ V (x + t) - V x := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := ih (by omega)
    have h2 := hV.step_anti (x := x + t) (y := y + t) (by omega) (by omega)
    rw [← add_assoc, ← add_assoc]
    linarith

/-- Concavity through the origin on the grid: `V(l+j) - V(l) ≤ V(j)` when `V 0 = 0`. -/
lemma _root_.Molico.IncrSeq.gain_le (hV : IncrSeq V N) (h0 : V 0 = 0) {l j : ℕ} (hlj : l + j ≤ N) :
    V (l + j) - V l ≤ V j := by
  have := hV.incr_anti (x := 0) (y := l) (t := j) (Nat.zero_le l) hlj
  simpa [h0] using this

lemma _root_.Molico.IncrSeq.nonneg (hV : IncrSeq V N) (h0 : V 0 = 0) {i : ℕ} (hi : i ≤ N) : 0 ≤ V i := by
  have := hV.le_of_le (Nat.zero_le i) hi; rwa [h0] at this

end IncrSeq

/-! ### Elementary properties of the grid Bellman objective -/

section Bellman

variable (U : AdmissibleUtility) {N : ℕ} {V : ℕ → ℝ}

lemma gobj_eq (m l j : ℕ) : gobj U.u V m l j = V (m - j) + sellerSeq U.u V l j := by
  simp [gobj, sellerSeq, add_comm]

lemma gobj_le_gH {m l j : ℕ} (hm : m ≤ N) (hl : l ≤ N) (hj : j ∈ feas N m l) :
    gobj U.u V m l j ≤ gH U.u N V m l := by
  rw [gobj_eq]; exact le_maxConv hj

lemma exists_gH_eq {m l : ℕ} (hm : m ≤ N) (hl : l ≤ N) :
    ∃ j ∈ feas N m l, gobj U.u V m l j = gH U.u N V m l := by
  obtain ⟨j, hj, hmax⟩ := exists_maxConv_eq (A := V) (B := sellerSeq U.u V l) (P := N)
    (Q := N - l) (i := m) (by omega)
  exact ⟨j, hj, by rw [gobj_eq]; exact hmax⟩

lemma gobj_zero (hV0 : V 0 = 0) (m l : ℕ) : gobj U.u V m l 0 = V m := by
  simp [gobj, U.u_zero]

lemma le_gH (hV0 : V 0 = 0) {m l : ℕ} (hm : m ≤ N) (hl : l ≤ N) : V m ≤ gH U.u N V m l := by
  have := gobj_le_gH U hm hl (zero_mem_feas hm hl) (V := V)
  rwa [gobj_zero U hV0] at this

/-- The seller sequence `j ↦ u(V(l+j) - V(l))` is nondecreasing and discretely concave
on `{0, …, N - l}`. -/
lemma sellerSeq_incr (hV : IncrSeq V N) {l : ℕ} (hl : l ≤ N) :
    IncrSeq (sellerSeq U.u V l) (N - l) := by
  constructor
  · intro k hk
    simp only [sellerSeq]
    apply U.monotoneOn
    · show 0 ≤ V (l + k) - V l
      linarith [hV.le_of_le (show l ≤ l + k by omega) (by omega)]
    · show 0 ≤ V (l + (k + 1)) - V l
      linarith [hV.le_of_le (show l ≤ l + (k + 1) by omega) (by omega)]
    · have := hV.mono (l + k) (by omega)
      rw [← add_assoc]; linarith
  · intro k hk
    simp only [sellerSeq]
    set a := V (l + k) - V l
    set b := V (l + (k + 1)) - V l
    set c := V (l + (k + 2)) - V l
    have ha : 0 ≤ a := by linarith [hV.le_of_le (show l ≤ l + k by omega) (by omega)]
    have hab : a ≤ b := by
      have := hV.mono (l + k) (by omega); simp only [a, b]; rw [← add_assoc]; linarith
    have hbc : b ≤ c := by
      have := hV.mono (l + (k + 1)) (by omega); simp only [b, c]
      rw [show l + (k + 2) = l + (k + 1) + 1 by omega]; linarith
    have hconc : c - b ≤ b - a := by
      have := hV.concave (l + k) (by omega)
      simp only [a, b, c]
      rw [show l + (k + 2) = l + k + 2 by omega, show l + (k + 1) = l + k + 1 by omega]
      linarith
    -- u(c) - u(b) ≤ u(a + (c - b)) - u(a) ≤ u(b) - u(a)
    have h1 := U.incr_anti ha hab (show 0 ≤ c - b by linarith)
    rw [show b + (c - b) = c by ring] at h1
    have h2 := U.monotoneOn (show a + (c - b) ∈ Set.Ici (0:ℝ) by
        simp only [Set.mem_Ici]; linarith)
      (show b ∈ Set.Ici (0:ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
    linarith

lemma gH_mono (hV : IncrSeq V N) {m l : ℕ} (hm : m < N) (hl : l ≤ N) :
    gH U.u N V m l ≤ gH U.u N V (m + 1) l :=
  maxConv_mono hV (sellerSeq_incr U hV hl) (by omega)

lemma gH_mono' (hV : IncrSeq V N) {m m' l : ℕ} (hmm' : m ≤ m') (hm' : m' ≤ N) (hl : l ≤ N) :
    gH U.u N V m l ≤ gH U.u N V m' l := by
  induction m', hmm' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact (ih (by omega)).trans (gH_mono U hV (by omega) hl)

lemma gH_concave (hV : IncrSeq V N) {m l : ℕ} (hm : m + 2 ≤ N) (hl : l ≤ N) :
    gH U.u N V (m + 2) l - gH U.u N V (m + 1) l ≤ gH U.u N V (m + 1) l - gH U.u N V m l :=
  maxConv_concave hV (sellerSeq_incr U hV hl) (by omega)

lemma gH_zero (hV0 : V 0 = 0) {l : ℕ} (hl : l ≤ N) : gH U.u N V 0 l = 0 := by
  unfold gH
  rw [maxConv_zero]
  simp [sellerSeq, hV0, U.u_zero]

/-- `H_V(m,s) ≤ u(V(m)) + V(m)` on the grid (proof of `lem:gauge`). -/
lemma gH_le (hV : IncrSeq V N) (hV0 : V 0 = 0) {m l : ℕ} (hm : m ≤ N) (hl : l ≤ N) :
    gH U.u N V m l ≤ U.u (V m) + V m := by
  obtain ⟨j, hj, hjeq⟩ := exists_gH_eq U (V := V) hm hl
  rw [← hjeq, gobj]
  rw [mem_feas hm hl] at hj
  have hg := hV.gain_le hV0 hj.2
  have hjm := hV.le_of_le hj.1 hm
  have hg0 : 0 ≤ V (l + j) - V l := by
    linarith [hV.le_of_le (show l ≤ l + j by omega) hj.2]
  have h1 := U.monotoneOn (show V (l + j) - V l ∈ Set.Ici (0:ℝ) from hg0)
    (show V m ∈ Set.Ici (0:ℝ) from hV.nonneg hV0 hm) (hg.trans hjm)
  have h2 := hV.le_of_le (show m - j ≤ m by omega) hm
  linarith

lemma gH_nonneg (hV : IncrSeq V N) (hV0 : V 0 = 0) {m l : ℕ} (hm : m ≤ N) (hl : l ≤ N) :
    0 ≤ gH U.u N V m l := (hV.nonneg hV0 hm).trans (le_gH U hV0 hm hl)

end Bellman

/-! ### The stationarity map preserves `𝒫_M(𝒳)` -/

section Psi

variable {N : ℕ} {η : ℕ → ℝ} {κ : ℕ → ℕ → ℕ → ℝ}

lemma gPsi_nonneg (hη : ∀ l, 0 ≤ η l) (hκ : IsKernel N κ) (k : ℕ) : 0 ≤ gPsi N η κ k := by
  unfold gPsi
  refine mul_nonneg (by norm_num) (sum_nonneg fun m _ => sum_nonneg fun l _ => sum_nonneg
    fun j _ => mul_nonneg (mul_nonneg (mul_nonneg (hη m) (hη l)) (hκ.nonneg m l j)) ?_)
  positivity

/-- Swapping the landing index `k` inside the meeting sums. -/
lemma sum_gPsi_mul (w : ℕ → ℝ) :
    ∑ k ∈ range (N + 1), gPsi N η κ k * w k =
      2⁻¹ * ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), ∑ j ∈ feas N m l,
        η m * η l * κ m l j * (∑ k ∈ range (N + 1),
          ((if m - j = k then (1:ℝ) else 0) + (if l + j = k then 1 else 0)) * w k) := by
  unfold gPsi
  simp_rw [mul_assoc (2⁻¹ : ℝ), ← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma landing_sum {m l j : ℕ} (hm : m ∈ range (N + 1)) (hl : l ∈ range (N + 1))
    (hj : j ∈ feas N m l) (w : ℕ → ℝ) :
    ∑ k ∈ range (N + 1), ((if m - j = k then (1:ℝ) else 0) + (if l + j = k then 1 else 0)) * w k
      = w (m - j) + w (l + j) := by
  rw [mem_range] at hm hl
  rw [mem_feas (by omega) (by omega)] at hj
  simp_rw [add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
    if_pos (mem_range.2 (by omega)), if_pos (mem_range.2 (by omega))]

lemma sum_gPsi (hκ : IsKernel N κ) (hsum : ∑ l ∈ range (N + 1), η l = 1) :
    ∑ k ∈ range (N + 1), gPsi N η κ k = 1 := by
  have h := sum_gPsi_mul (N := N) (η := η) (κ := κ) (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  have : ∀ m ∈ range (N + 1), ∀ l ∈ range (N + 1),
      ∑ j ∈ feas N m l, η m * η l * κ m l j * (∑ k ∈ range (N + 1),
        ((if m - j = k then (1:ℝ) else 0) + (if l + j = k then 1 else 0))) = 2 * (η m * η l) := by
    intro m hm l hl
    have e : ∀ j ∈ feas N m l, η m * η l * κ m l j * (∑ k ∈ range (N + 1),
        ((if m - j = k then (1:ℝ) else 0) + (if l + j = k then 1 else 0))) =
        2 * (η m * η l) * κ m l j := by
      intro j hj
      have := landing_sum hm hl hj (fun _ => (1:ℝ))
      simp only [mul_one] at this
      rw [this]; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum,
      hκ.sum_one m (by rw [mem_range] at hm; omega) l (by rw [mem_range] at hl; omega), mul_one]
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl => this m hm l hl]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, hsum]
  norm_num

lemma mean_gPsi (hκ : IsKernel N κ) (hsum : ∑ l ∈ range (N + 1), η l = 1) (h : ℝ) :
    ∑ k ∈ range (N + 1), gPsi N η κ k * (k * h) = ∑ l ∈ range (N + 1), η l * (l * h) := by
  rw [sum_gPsi_mul]
  have : ∀ m ∈ range (N + 1), ∀ l ∈ range (N + 1),
      ∑ j ∈ feas N m l, η m * η l * κ m l j * (∑ k ∈ range (N + 1),
        ((if m - j = k then (1:ℝ) else 0) + (if l + j = k then 1 else 0)) * (k * h)) =
        η m * η l * (m * h + l * h) := by
    intro m hm l hl
    have e : ∀ j ∈ feas N m l, η m * η l * κ m l j * (∑ k ∈ range (N + 1),
        ((if m - j = k then (1:ℝ) else 0) + (if l + j = k then 1 else 0)) * (k * h)) =
        η m * η l * (m * h + l * h) * κ m l j := by
      intro j hj
      rw [landing_sum hm hl hj (fun k => (k:ℝ) * h)]
      have hj' := hj
      rw [mem_range] at hm hl
      rw [mem_feas (by omega) (by omega)] at hj'
      push_cast [hj'.1]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum,
      hκ.sum_one m (by rw [mem_range] at hm; omega) l (by rw [mem_range] at hl; omega), mul_one]
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun l hl => this m hm l hl]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have e1 : ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), η m * η l * (m * h) =
      ∑ m ∈ range (N + 1), η m * (m * h) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum]; ring
  have e2 : ∑ m ∈ range (N + 1), ∑ l ∈ range (N + 1), η m * η l * (l * h) =
      ∑ l ∈ range (N + 1), η l * (l * h) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]; ring
  rw [e1, e2]; ring

end Psi

end Grid

end Molico
