import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Increment aggregation (`lem:incr`)

`lem:incr` of `existence-theorem.tex` concerns the max-plus convolution
`𝔥_i = max_{max(0,i-P) ≤ j ≤ min(i,Q)} (∑_{k ≤ i-j} v_k + ∑_{k ≤ j} a_k)`
of two nonincreasing nonnegative increment tuples `(v_k)_{k=1}^P` and `(a_k)_{k=1}^Q`.

We formalize it in terms of the *cumulative* sequences `A i = ∑_{k ≤ i} v_k` and
`B j = ∑_{k ≤ j} a_k`. These are nondecreasing and discretely concave, i.e. they have
nonnegative, nonincreasing increments. Then `𝔥_i = maxConv A B P Q i`.

Proved here, as used in the manuscript:
* `maxConv_mono` and `maxConv_concave`: `(𝔥_i)` is nondecreasing and discretely concave
  ("in particular" clause);
* `maxConv_merge`: the merge inequalities `eq:merge` at every maximiser.

The identification of `𝔥_i` with the sum of the `i` largest merged increments is the
intermediate step of the manuscript's (omitted) proof. It is not needed downstream and is not
formalized.
-/

open Finset

namespace Molico

/-- Feasible split indices `max(0, i-P) ≤ j ≤ min(i, Q)` (natural subtraction is truncated). -/
def convSet (P Q i : ℕ) : Finset ℕ := Icc (i - P) (min i Q)

lemma convSet_nonempty {P Q i : ℕ} (h : i ≤ P + Q) : (convSet P Q i).Nonempty :=
  nonempty_Icc.2 (le_min (Nat.sub_le i P) (by omega))

lemma mem_convSet {P Q i j : ℕ} : j ∈ convSet P Q i ↔ i - P ≤ j ∧ j ≤ i ∧ j ≤ Q := by
  simp [convSet, le_min_iff]

/-- The max-plus convolution `𝔥_i = max_j A(i - j) + B(j)` of `lem:incr` (and `0` if `i > P + Q`,
where it is not used). -/
noncomputable def maxConv (A B : ℕ → ℝ) (P Q i : ℕ) : ℝ :=
  if h : i ≤ P + Q then (convSet P Q i).sup' (convSet_nonempty h) (fun j => A (i - j) + B j)
  else 0

/-- A sequence `A` is *nondecreasing and discretely concave on `{0,…,P}`*: its increments
`A (k+1) - A k`, `k < P`, are nonnegative and nonincreasing. -/
structure IncrSeq (A : ℕ → ℝ) (P : ℕ) : Prop where
  mono : ∀ k, k < P → A k ≤ A (k + 1)
  concave : ∀ k, k + 2 ≤ P → A (k + 2) - A (k + 1) ≤ A (k + 1) - A k

variable {A B : ℕ → ℝ} {P Q : ℕ}

lemma le_maxConv {i j : ℕ} (hj : j ∈ convSet P Q i) : A (i - j) + B j ≤ maxConv A B P Q i := by
  have hi : i ≤ P + Q := by rw [mem_convSet] at hj; omega
  rw [maxConv, dif_pos hi]
  exact le_sup' (fun j => A (i - j) + B j) hj

lemma exists_maxConv_eq {i : ℕ} (hi : i ≤ P + Q) :
    ∃ j ∈ convSet P Q i, A (i - j) + B j = maxConv A B P Q i := by
  rw [maxConv, dif_pos hi]
  obtain ⟨j, hj, hmax⟩ := exists_mem_eq_sup' (convSet_nonempty hi) (fun j => A (i - j) + B j)
  exact ⟨j, hj, hmax.symm⟩

/-- Increments of a discretely concave sequence are nonincreasing: for `x ≤ y` with
`y + 1 ≤ N`, `f (y+1) - f y ≤ f (x+1) - f x`. -/
private lemma incr_anti {f : ℕ → ℝ} {N : ℕ} (hf : IncrSeq f N) {x y : ℕ} (hxy : x ≤ y)
    (hy : y + 1 ≤ N) : f (y + 1) - f y ≤ f (x + 1) - f x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
  clear hxy
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := hf.concave (x + d) (by omega)
    have h2 := ih (by omega)
    have e1 : x + (d + 1) + 1 = x + d + 2 := by omega
    have e2 : x + (d + 1) = x + d + 1 := by omega
    rw [e1, e2]
    linarith

lemma maxConv_zero : maxConv A B P Q 0 = A 0 + B 0 := by
  obtain ⟨j, hj, h⟩ := exists_maxConv_eq (A := A) (B := B) (P := P) (Q := Q) (i := 0)
    (Nat.zero_le _)
  obtain ⟨_, hj2, _⟩ := mem_convSet.1 hj
  have hj0 : j = 0 := by omega
  subst hj0
  rw [← h, Nat.sub_zero]

/-- `lem:incr`: `𝔥` is nondecreasing. -/
theorem maxConv_mono (hA : IncrSeq A P) (hB : IncrSeq B Q) {i : ℕ} (hi : i < P + Q) :
    maxConv A B P Q i ≤ maxConv A B P Q (i + 1) := by
  obtain ⟨j, hj, hmax⟩ := exists_maxConv_eq (A := A) (B := B) hi.le
  obtain ⟨hj1, hj2, hj3⟩ := mem_convSet.1 hj
  rw [← hmax]
  by_cases hP : i - j < P
  · have hm : j ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm
    have h2 := hA.mono (i - j) hP
    have e : i + 1 - j = i - j + 1 := by omega
    rw [e] at h1
    linarith
  · have hQ : j < Q := by omega
    have hm : j + 1 ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm
    have h2 := hB.mono j hQ
    have e : i + 1 - (j + 1) = i - j := by omega
    rw [e] at h1
    linarith

/-- `lem:incr`: `𝔥` is discretely concave. -/
theorem maxConv_concave (hA : IncrSeq A P) (hB : IncrSeq B Q) {i : ℕ} (hi : i + 2 ≤ P + Q) :
    maxConv A B P Q (i + 2) - maxConv A B P Q (i + 1) ≤
      maxConv A B P Q (i + 1) - maxConv A B P Q i := by
  obtain ⟨j1, hj1, hmax1⟩ := exists_maxConv_eq (A := A) (B := B) hi
  obtain ⟨j2, hj2, hmax2⟩ := exists_maxConv_eq (A := A) (B := B) (P := P) (Q := Q) (i := i)
    (by omega)
  obtain ⟨hj1a, hj1b, hj1c⟩ := mem_convSet.1 hj1
  obtain ⟨hj2a, hj2b, hj2c⟩ := mem_convSet.1 hj2
  rw [← hmax1, ← hmax2]
  rcases le_or_gt j1 j2 with h12 | h12
  · -- keep the `B`-arguments, balance the `A`-arguments
    have hm1 : j1 ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have hm2 : j2 ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm1
    have h2 := le_maxConv (A := A) (B := B) hm2
    have h3 := incr_anti hA (x := i - j2) (y := i + 1 - j1) (by omega) (by omega)
    have e1 : i + 1 - j1 + 1 = i + 2 - j1 := by omega
    have e2 : i - j2 + 1 = i + 1 - j2 := by omega
    rw [e1, e2] at h3
    linarith
  · -- keep the `A`-arguments, balance the `B`-arguments
    have hm1 : j1 - 1 ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have hm2 : j2 + 1 ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm1
    have h2 := le_maxConv (A := A) (B := B) hm2
    have h3 := incr_anti hB (x := j2) (y := j1 - 1) (by omega) (by omega)
    have e1 : i + 1 - (j1 - 1) = i + 2 - j1 := by omega
    have e2 : i + 1 - (j2 + 1) = i - j2 := by omega
    have e3 : j1 - 1 + 1 = j1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h3
    linarith

/-- `lem:incr`, eq. `eq:merge`: bounds on the increment `p_i = 𝔥_i - 𝔥_{i-1}` at any maximiser
`j` of `𝔥_i`. In increment notation `v_k = A k - A (k-1)`, `a_k = B k - B (k-1)` these read
`p_i ≤ v_{i-j}` (if `i-j ≥ 1`), `p_i ≤ a_j` (if `j ≥ 1`), `p_i ≥ v_{i-j+1}` (if `i-j < P`),
`p_i ≥ a_{j+1}` (if `j < Q`). -/
theorem maxConv_merge (hA : IncrSeq A P) (hB : IncrSeq B Q) {i j : ℕ} (hi1 : 1 ≤ i)
    (hi : i ≤ P + Q) (hj : j ∈ convSet P Q i) (hmax : A (i - j) + B j = maxConv A B P Q i) :
    (1 ≤ i - j →
      maxConv A B P Q i - maxConv A B P Q (i - 1) ≤ A (i - j) - A (i - j - 1)) ∧
    (1 ≤ j → maxConv A B P Q i - maxConv A B P Q (i - 1) ≤ B j - B (j - 1)) ∧
    (i - j < P →
      A (i - j + 1) - A (i - j) ≤ maxConv A B P Q i - maxConv A B P Q (i - 1)) ∧
    (j < Q → B (j + 1) - B j ≤ maxConv A B P Q i - maxConv A B P Q (i - 1)) := by
  obtain ⟨hj1, hj2, hj3⟩ := mem_convSet.1 hj
  -- concavity of `𝔥` at the middle index `i`
  have hconc : i + 1 ≤ P + Q →
      maxConv A B P Q (i + 1) - maxConv A B P Q i ≤
        maxConv A B P Q i - maxConv A B P Q (i - 1) := by
    intro h
    have hc := maxConv_concave hA hB (i := i - 1) (by omega)
    have e1 : i - 1 + 2 = i + 1 := by omega
    have e2 : i - 1 + 1 = i := by omega
    rw [e1, e2] at hc
    exact hc
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hm : j ∈ convSet P Q (i - 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm
    have e : i - 1 - j = i - j - 1 := by omega
    rw [e] at h1
    linarith
  · have hm : j - 1 ∈ convSet P Q (i - 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm
    have e : i - 1 - (j - 1) = i - j := by omega
    rw [e] at h1
    linarith
  · have hm : j ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm
    have e : i + 1 - j = i - j + 1 := by omega
    rw [e] at h1
    have h2 := hconc (by omega)
    linarith
  · have hm : j + 1 ∈ convSet P Q (i + 1) := mem_convSet.2 ⟨by omega, by omega, by omega⟩
    have h1 := le_maxConv (A := A) (B := B) hm
    have e : i + 1 - (j + 1) = i - j := by omega
    rw [e] at h1
    have h2 := hconc (by omega)
    linarith

end Molico
