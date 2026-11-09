import MonetaryExistenceBuyer.Rescaling.Flow
import MonetaryExistenceBuyer.Limit.TailSeller

/-!
# Passage of the Bellman equations (`prop:passage`)

Structure of the proof:
* grid facts (`V_eq_Wn`, `Wn_add_eq`, ...) and elementary properties of `W`, `W̄`, `L`, `J'`;
* `EvLe f A` (`limsup f ≤ A`) and its calculus;
* convergence of `W_n` along converging normalized wealths (`tendsto_Wn`, `evLe_Wn`), along an
  arbitrary subsequence `ψ` of the normalizing subsequence;
* convergence of maximized payoffs (`conv`), split into finite and infinite normalized wealth;
* limits of normalized grid states lie in `ℰ_W` (`mem_EW`);
* continuity of `ℋ(m; ·)` on `ℰ_W` (`contOn`), the bounds `eq:normalizedbounds` (`Hc_bounds`);
* the normalized Bellman equation (`bellman`), via a Tietze extension of `ℋ(m; ·)|_{ℰ_W}` and
  uniform convergence of the maximized payoffs over all grid sellers (`unif`).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Molico

variable {P : Primitives}

namespace NormalizedLimit

variable {S : SelectedSeq P} {a : ℝ}

/-! ### Grid facts -/

private lemma V_mem (S : SelectedSeq P) (n : ℕ) {i : ℕ} (hi : i ≤ S.N n) :
    0 ≤ S.V n i ∧ S.V n i ≤ P.Lstar := by
  have hE := S.isApproxEq n
  exact ⟨hE.cone.incr.nonneg hE.cone.zero hi,
    (hE.cone.incr.le_of_le hi le_rfl).trans (S.floor n).2⟩

private lemma Vn_mem (S : SelectedSeq P) (n : ℕ) (x : ℝ) :
    0 ≤ S.Vn n x ∧ S.Vn n x ≤ P.Lstar := by
  have hE := S.isApproxEq n
  have h := interp_mem_Icc (S.h_pos n) hE.cone.incr x
  rw [hE.cone.zero] at h
  exact ⟨h.1, h.2.trans (S.floor n).2⟩

private lemma scale_nonneg (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.scale a n :=
  mul_nonneg (S.h_pos n).le (Nat.cast_nonneg _)

private lemma δn_nonneg (S : SelectedSeq P) (a : ℝ) (n : ℕ) : 0 ≤ S.δn a n :=
  div_nonneg (S.h_pos n).le (scale_nonneg S a n)

private lemma Wn_monotoneOn (S : SelectedSeq P) (a : ℝ) (n : ℕ) :
    MonotoneOn (S.Wn a n) (Ici 0) := by
  intro x _ y _ hxy
  exact interp_monotone (S.h_pos n) (S.isApproxEq n).cone.incr
    (mul_le_mul_of_nonneg_left hxy (scale_nonneg S a n))

private lemma Wn_concaveOn (S : SelectedSeq P) (a : ℝ) (n : ℕ) :
    ConcaveOn ℝ (Ici 0) (S.Wn a n) := by
  have hc := interp_concaveOn (S.h_pos n) (S.isApproxEq n).cone.incr
  refine ⟨convex_Ici 0, fun x hx y hy s t hs ht hst => ?_⟩
  have hx' : S.scale a n * x ∈ Ici (0 : ℝ) := mul_nonneg (scale_nonneg S a n) hx
  have hy' : S.scale a n * y ∈ Ici (0 : ℝ) := mul_nonneg (scale_nonneg S a n) hy
  have key := hc.2 hx' hy' hs ht hst
  simp only [smul_eq_mul] at key ⊢
  unfold SelectedSeq.Wn SelectedSeq.Vn
  convert key using 2
  ring

private lemma Wn_mem (S : SelectedSeq P) (a : ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ S.Wn a n x ∧ S.Wn a n x ≤ P.Lstar :=
  Vn_mem S n _

private lemma Vn_natCast (S : SelectedSeq P) {n i : ℕ} (hi : i ≤ S.N n) :
    S.Vn n ((i : ℝ) * S.h n) = S.V n i :=
  interp_natCast (S.h_pos n) hi

/-- Grid values are normalized values at normalized grid points. -/
private lemma V_eq_Wn (S : SelectedSeq P) {n i : ℕ} (hi : i ≤ S.N n) (he : S.scale a n ≠ 0) :
    S.V n i = S.Wn a n ((i : ℝ) * S.δn a n) := by
  unfold SelectedSeq.Wn SelectedSeq.δn
  rw [show S.scale a n * ((i : ℝ) * (S.h n / S.scale a n)) = (i : ℝ) * S.h n by field_simp]
  exact (Vn_natCast S hi).symm

private lemma Wn_add_eq (S : SelectedSeq P) {n l j : ℕ} (hlj : l + j ≤ S.N n)
    (he : S.scale a n ≠ 0) :
    S.Wn a n ((l : ℝ) * S.δn a n + (j : ℝ) * S.δn a n) = S.V n (l + j) := by
  rw [V_eq_Wn S hlj he]; push_cast; ring_nf

private lemma Wn_sub_eq (S : SelectedSeq P) {n i j : ℕ} (hji : j ≤ i) (hi : i ≤ S.N n)
    (he : S.scale a n ≠ 0) :
    S.Wn a n ((i : ℝ) * S.δn a n - (j : ℝ) * S.δn a n) = S.V n (i - j) := by
  rw [V_eq_Wn S (show i - j ≤ S.N n by omega) he, Nat.cast_sub hji, sub_mul]

private lemma gobj_eq_Wn (S : SelectedSeq P) {n i l j : ℕ} (he : S.scale a n ≠ 0) (hji : j ≤ i)
    (hiN : i ≤ S.N n) (hlj : l + j ≤ S.N n) :
    Grid.gobj P.U.u (S.V n) i l j =
      P.U.u (S.Wn a n ((l : ℝ) * S.δn a n + (j : ℝ) * S.δn a n) - S.V n l) +
        S.Wn a n ((i : ℝ) * S.δn a n - (j : ℝ) * S.δn a n) := by
  rw [Wn_add_eq S hlj he, Wn_sub_eq S hji hiN he]
  rfl

private lemma continuous_ι (S : SelectedSeq P) (a : ℝ) (n : ℕ) : Continuous (S.ι a n) := by
  unfold SelectedSeq.ι SelectedSeq.Vn
  exact (ENNReal.continuous_ofReal.comp (continuous_id.div_const _)).prodMk
    (continuous_interp (S.h_pos n))


/-! ### `limsup f ≤ A`, in elementary form -/

/-- `EvLe f A`: for every `ε > 0`, eventually `f k ≤ A + ε` (i.e. `limsup f ≤ A`). -/
private def EvLe (f : ℕ → ℝ) (A : ℝ) : Prop := ∀ ε > 0, ∀ᶠ k in atTop, f k ≤ A + ε

private lemma evLe_of_tendsto {f : ℕ → ℝ} {A : ℝ} (hf : Tendsto f atTop (𝓝 A)) : EvLe f A :=
  fun _ hε => (hf.eventually_lt_const (lt_add_of_pos_right A hε)).mono fun _ hk => hk.le

private lemma EvLe.add {f g : ℕ → ℝ} {A B : ℝ} (hf : EvLe f A) (hg : EvLe g B) :
    EvLe (fun k => f k + g k) (A + B) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity)] with k h1 h2
  linarith

private lemma EvLe.sub_tendsto {f g : ℕ → ℝ} {A B : ℝ} (hf : EvLe f A)
    (hg : Tendsto g atTop (𝓝 B)) : EvLe (fun k => f k - g k) (A - B) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity),
    hg.eventually_const_lt (show B - ε / 2 < B by linarith)] with k h1 h2
  linarith

private lemma EvLe.mono_ev {f g : ℕ → ℝ} {A : ℝ} (hg : EvLe g A)
    (hfg : ∀ᶠ k in atTop, f k ≤ g k) : EvLe f A := by
  intro ε hε
  filter_upwards [hg ε hε, hfg] with k h1 h2
  linarith

private lemma EvLe.trans_le {f : ℕ → ℝ} {A B : ℝ} (hf : EvLe f A) (hAB : A ≤ B) : EvLe f B := by
  intro ε hε
  filter_upwards [hf ε hε] with k h1
  linarith

private lemma EvLe.le_lim {f : ℕ → ℝ} {A y : ℝ} (hf : EvLe f A)
    (hy : Tendsto f atTop (𝓝 y)) : y ≤ A := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact _root_.le_of_tendsto hy (hf ε hε)

private lemma tendsto_of_evLe {f : ℕ → ℝ} {A : ℝ} (h1 : EvLe f A)
    (h2 : ∀ ε > 0, ∀ᶠ k in atTop, A - ε ≤ f k) : Tendsto f atTop (𝓝 A) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [h2 ((A - b) / 2) (by linarith)] with k hk
    linarith
  · filter_upwards [h1 ((b - A) / 2) (by linarith)] with k hk
    linarith

/-- The subsequence principle for `EvLe`. -/
private lemma evLe_of_subseq {f : ℕ → ℝ} {A : ℝ}
    (h : ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧
      EvLe (fun k => f (ns (ms k))) A) : EvLe f A := by
  intro ε hε
  by_contra hc
  rw [not_eventually] at hc
  obtain ⟨ns, hns, hns'⟩ := extraction_of_frequently_atTop hc
  obtain ⟨ms, -, hms⟩ := h ns hns
  obtain ⟨k, hk⟩ := (hms ε hε).exists
  exact hns' (ms k) hk

/-- `u` passes `limsup` bounds (continuity and monotonicity on `[0, ∞)`). -/
private lemma evLe_u {xs : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hxs0 : ∀ᶠ k in atTop, 0 ≤ xs k)
    (hxs : EvLe xs t) : EvLe (fun k => P.U.u (xs k)) (P.U.u t) := by
  intro ε hε
  have hc := P.U.continuousOn t ht
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨η, hη, hη'⟩ := hc ε hε
  have h1 : P.U.u (t + η / 2) < P.U.u t + ε := by
    have := hη' (show t + η / 2 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  filter_upwards [hxs0, hxs (η / 2) (by positivity)] with k hk0 hk1
  exact (P.U.monotoneOn hk0 (show t + η / 2 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
    hk1).trans h1.le

private lemma tendsto_u {xs : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hxs0 : ∀ᶠ k in atTop, 0 ≤ xs k)
    (hxs : Tendsto xs atTop (𝓝 t)) : Tendsto (fun k => P.U.u (xs k)) atTop (𝓝 (P.U.u t)) :=
  (P.U.continuousOn t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxs, hxs0⟩)

/-- Discreteness: if `n_k δ → x` with `δ > 0`, then `x ∈ δ ℕ` and `n_k` is eventually constant. -/
private lemma nat_mul_tendsto {δ x : ℝ} (hδ : 0 < δ) {n : ℕ → ℕ}
    (h : Tendsto (fun k => (n k : ℝ) * δ) atTop (𝓝 x)) :
    ∃ j : ℕ, x = j * δ ∧ ∀ᶠ k in atTop, n k = j := by
  have h' : Tendsto (fun k => (n k : ℝ)) atTop (𝓝 (x / δ)) := by
    have := h.div_const δ
    simpa only [mul_div_cancel_right₀ _ hδ.ne'] using this
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 h' (1 / 2) (by norm_num)
  have hconst : ∀ k ≥ K, n k = n K := by
    intro k hk
    have h1 := hK k hk
    have h2 := hK K le_rfl
    rw [Real.dist_eq] at h1 h2
    have h3 : |(n k : ℝ) - n K| < 1 := by
      calc |(n k : ℝ) - n K| = |((n k : ℝ) - x / δ) - ((n K : ℝ) - x / δ)| := by ring_nf
        _ ≤ |(n k : ℝ) - x / δ| + |(n K : ℝ) - x / δ| := abs_sub _ _
        _ < 1 := by linarith
    rw [abs_lt] at h3
    rcases lt_trichotomy (n k) (n K) with hlt | heq | hgt
    · have : ((n k : ℕ) : ℝ) + 1 ≤ n K := by exact_mod_cast hlt
      linarith [h3.1]
    · exact heq
    · have : ((n K : ℕ) : ℝ) + 1 ≤ n k := by exact_mod_cast hgt
      linarith [h3.2]
  have hev : ∀ᶠ k in atTop, n k = n K := eventually_atTop.2 ⟨K, hconst⟩
  refine ⟨n K, ?_, hev⟩
  have h2 : Tendsto (fun k => (n k : ℝ)) atTop (𝓝 (n K : ℝ)) :=
    tendsto_const_nhds.congr' (hev.mono fun k hk => by simp only [hk])
  have := tendsto_nhds_unique h' h2
  field_simp at this
  linarith

/-- If `ofReal x_k → ∞` then `x_k → ∞`. -/
private lemma tendsto_atTop_of_ofReal {xs : ℕ → ℝ}
    (h : Tendsto (fun k => ENNReal.ofReal (xs k)) atTop (𝓝 ⊤)) : Tendsto xs atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [h.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top : ENNReal.ofReal b < ⊤))]
    with k hk
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 hk).1.le

/-! ### Elementary properties of the normalized limit -/

variable (NL : NormalizedLimit S a)

private lemma Wbar_pos {x : ℝ} (hx : 0 < x) : NL.Wbar x = NL.W x := by
  unfold Wbar; rw [ite_eq_right hx.ne']

private lemma Wbar_zero : NL.Wbar 0 = NL.J' := by
  unfold Wbar; rw [ite_eq_left rfl]

private lemma W_mem (ha : 0 < a) (haJ : a < S.jump) {x : ℝ} (hx : 0 < x) :
    0 ≤ NL.W x ∧ NL.W x ≤ P.Lstar :=
  (NL.props ha haJ).2.2.2.2.2.1 x hx

private lemma bddAbove_W (ha : 0 < a) (haJ : a < S.jump) : BddAbove (NL.W '' Ioi 0) := by
  refine ⟨P.Lstar, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (NL.W_mem ha haJ hx).2

private lemma bddBelow_W (ha : 0 < a) (haJ : a < S.jump) : BddBelow (NL.W '' Ioi 0) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (NL.W_mem ha haJ hx).1

private lemma W_image_nonempty : (NL.W '' Ioi 0).Nonempty := ⟨_, 1, mem_Ioi.2 one_pos, rfl⟩

private lemma W_le_Lsup (ha : 0 < a) (haJ : a < S.jump) {x : ℝ} (hx : 0 < x) :
    NL.W x ≤ NL.Lsup :=
  le_csSup (NL.bddAbove_W ha haJ) ⟨x, hx, rfl⟩

private lemma J'_le_W (ha : 0 < a) (haJ : a < S.jump) {x : ℝ} (hx : 0 < x) : NL.J' ≤ NL.W x :=
  csInf_le (NL.bddBelow_W ha haJ) ⟨x, hx, rfl⟩

private lemma J'_nonneg (ha : 0 < a) (haJ : a < S.jump) : 0 ≤ NL.J' :=
  le_csInf NL.W_image_nonempty (by rintro _ ⟨x, hx, rfl⟩; exact (NL.W_mem ha haJ hx).1)

private lemma Lsup_le_Lstar (ha : 0 < a) (haJ : a < S.jump) : NL.Lsup ≤ P.Lstar :=
  csSup_le NL.W_image_nonempty (by rintro _ ⟨x, hx, rfl⟩; exact (NL.W_mem ha haJ hx).2)

private lemma Wbar_mono (ha : 0 < a) (haJ : a < S.jump) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    NL.Wbar x ≤ NL.Wbar y :=
  (NL.props ha haJ).2.2.2.1 hx (hx.trans hxy) hxy

private lemma Wbar_le_Lsup (ha : 0 < a) (haJ : a < S.jump) {x : ℝ} (hx : 0 ≤ x) :
    NL.Wbar x ≤ NL.Lsup := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Wbar_zero]
    exact (NL.J'_le_W ha haJ one_pos).trans (NL.W_le_Lsup ha haJ one_pos)
  · rw [Wbar_pos NL hx]; exact NL.W_le_Lsup ha haJ hx

private lemma Wbar_nonneg (ha : 0 < a) (haJ : a < S.jump) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ NL.Wbar x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Wbar_zero]; exact NL.J'_nonneg ha haJ
  · rw [Wbar_pos NL hx]; exact (NL.W_mem ha haJ hx).1

private lemma lattice_J' (ha : 0 < a) (haJ : a < S.jump) (hδ : 0 < NL.δ) : NL.J' = 0 :=
  ((NL.props ha haJ).2.2.2.2.2.2.2.2.2.2 hδ).1

private lemma pos_of_mem_Xplus {m : ℝ} (hm : m ∈ NL.Xplus) : 0 < m := by
  unfold Xplus at hm
  split_ifs at hm with hδ
  · exact hm
  · obtain ⟨k, hk, rfl⟩ := hm
    have hδpos : 0 < NL.δ := by
      rcases NL.lattice with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hδ
      · exact h
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity

private lemma zero_mem_A {m : ℝ} (hm : 0 ≤ m) : (0 : ℝ) ∈ NL.A m :=
  ⟨⟨le_rfl, hm⟩, Or.inr rfl⟩

private lemma A_subset (m : ℝ) : NL.A m ⊆ Icc 0 m := inter_subset_left


/-! ### Convergence of the normalized profiles along subsequences -/

private lemma W_conv_comp {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    TendstoLocallyUniformlyOn (fun k => S.Wn a (NL.φ (ψ k))) NL.W atTop (Ioi 0) :=
  fun u hu x hx => by
    obtain ⟨t, ht, hev⟩ := NL.W_conv u hu x hx
    exact ⟨t, ht, hψ.eventually hev⟩

private lemma tendsto_Wn_pos {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) {xs : ℕ → ℝ} {x : ℝ}
    (hx : 0 < x) (hxs : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun k => S.Wn a (NL.φ (ψ k)) (xs k)) atTop (𝓝 (NL.W x)) :=
  tendsto_comp_of_concave (B := P.Lstar) (fun _ => Wn_monotoneOn S a _)
    (fun _ => Wn_concaveOn S a _) (fun _ x _ => Wn_mem S a _ x) (NL.W_conv_comp hψ) hx hxs

/-- Upper limits of `W_n(x_n)` for `x_n → x ≥ 0`: `limsup W_n(x_n) ≤ W̄(x)` (local convergence
for `x > 0`, monotonicity for `x = 0`). -/
private lemma evLe_Wn {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) {xs : ℕ → ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hxs0 : ∀ᶠ k in atTop, 0 ≤ xs k) (hxs : Tendsto xs atTop (𝓝 x)) :
    EvLe (fun k => S.Wn a (NL.φ (ψ k)) (xs k)) (NL.Wbar x) := by
  rcases hx.eq_or_lt with rfl | hx
  · intro ε hε
    rw [Wbar_zero]
    obtain ⟨_, ⟨x', hx', rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (s := NL.W '' Ioi 0)
      NL.W_image_nonempty (show NL.J' < NL.J' + ε / 2 by linarith)
    have h1 := (NL.tendsto_Wn_pos hψ hx' tendsto_const_nhds).eventually_lt_const
      (show NL.W x' < NL.J' + ε by linarith)
    filter_upwards [hxs0, hxs.eventually (gt_mem_nhds (mem_Ioi.1 hx')), h1] with k hk0 hk1 hk2
    exact ((Wn_monotoneOn S a _) hk0 (mem_Ici.2 (le_of_lt hx')) hk1.le).trans hk2.le
  · rw [Wbar_pos NL hx]
    exact evLe_of_tendsto (NL.tendsto_Wn_pos hψ hx hxs)

/-- Convergence `W_n(x_n) → W̄(x)` for `x > 0`, or for `x = 0` when `J' = 0`. -/
private lemma tendsto_Wn {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) {xs : ℕ → ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hxs0 : ∀ᶠ k in atTop, 0 ≤ xs k) (hxs : Tendsto xs atTop (𝓝 x))
    (hJ : 0 < x ∨ NL.J' = 0) :
    Tendsto (fun k => S.Wn a (NL.φ (ψ k)) (xs k)) atTop (𝓝 (NL.Wbar x)) := by
  rcases hJ with hx' | hJ
  · rw [Wbar_pos NL hx']; exact NL.tendsto_Wn_pos hψ hx' hxs
  · rcases hx.eq_or_lt with rfl | hx'
    · refine tendsto_of_evLe (NL.evLe_Wn hψ le_rfl hxs0 hxs) fun ε hε => ?_
      refine Eventually.of_forall fun k => ?_
      rw [Wbar_zero, hJ]
      linarith [(Wn_mem S a (NL.φ (ψ k)) (xs k)).1]
    · rw [Wbar_pos NL hx']; exact NL.tendsto_Wn_pos hψ hx' hxs

/-- The normalization scale is eventually positive (`W_n(1) → W(1) ≥ a > 0`). -/
private lemma eventually_scale_pos (ha : 0 < a) (haJ : a < S.jump) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) : ∀ᶠ k in atTop, 0 < S.scale a (NL.φ (ψ k)) := by
  have h1 := (NL.W_conv_comp hψ).tendsto_at (show (1 : ℝ) ∈ Ioi 0 from mem_Ioi.2 one_pos)
  have h2 : 0 < NL.W 1 := ha.trans_le (NL.props ha haJ).2.1
  filter_upwards [h1.eventually_const_lt h2] with k hk
  rcases (scale_nonneg S a (NL.φ (ψ k))).eq_or_lt with h0 | h0
  · exfalso
    have h3 : S.Wn a (NL.φ (ψ k)) 1 = 0 := by
      unfold SelectedSeq.Wn SelectedSeq.Vn
      rw [← h0, zero_mul, interp_of_nonpos (S.h_pos _) le_rfl, (S.isApproxEq _).cone.zero]
    linarith
  · exact h0

/-- `N_n δ_n = R_n / e_n → ∞`. -/
private lemma tendsto_Nδ (ha : 0 < a) (haJ : a < S.jump) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) :
    Tendsto (fun k => (S.N (NL.φ (ψ k)) : ℝ) * S.δn a (NL.φ (ψ k))) atTop atTop := by
  have hρ : Tendsto (fun k => NL.φ (ψ k)) atTop atTop := NL.φ_mono.tendsto_atTop.comp hψ
  have hR := S.R_tendsto.comp hρ
  have he := (NL.props ha haJ).1.comp hψ
  refine tendsto_atTop_mono' atTop ?_ hR
  filter_upwards [NL.eventually_scale_pos ha haJ hψ, he.eventually (eventually_le_nhds one_pos),
    hR.eventually_ge_atTop 0] with k hk1 hk2 hk3
  simp only [Function.comp, SelectedSeq.δn] at hk2 hk3 ⊢
  rw [← mul_div_assoc, le_div_iff₀ hk1]
  exact mul_le_of_le_one_right hk3 hk2

/-- Feasibility of seller landings: if `(l_k + j_k) δ_k` converges, then eventually
`l_k + j_k ≤ N_k`. -/
private lemma ev_add_le_N (ha : 0 < a) (haJ : a < S.jump) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {l j : ℕ → ℕ} {c : ℝ}
    (h : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k)) + (j k : ℝ) * S.δn a (NL.φ (ψ k)))
      atTop (𝓝 c)) : ∀ᶠ k in atTop, l k + j k ≤ S.N (NL.φ (ψ k)) := by
  filter_upwards [h.eventually_lt_const (lt_add_one c),
    (NL.tendsto_Nδ ha haJ hψ).eventually_gt_atTop (c + 1)] with k h1 h2
  have h3 : ((l k + j k : ℕ) : ℝ) * S.δn a (NL.φ (ψ k)) <
      (S.N (NL.φ (ψ k)) : ℝ) * S.δn a (NL.φ (ψ k)) := by
    push_cast; linarith
  have := lt_of_mul_lt_mul_right h3 (δn_nonneg S a _)
  exact_mod_cast this.le


/-! ### The normalized objective -/

/-- Finite compatible states: `0 ≤ y ≤ W̄(z)`. -/
private lemma finite_EW (ha : 0 < a) (haJ : a < S.jump) {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW)
    (hp1 : p.1 ≠ ⊤) : 0 ≤ p.2 ∧ p.2 ≤ NL.Wbar p.1.toReal := by
  rcases hp with (⟨h1, h2⟩ | ⟨z, hz, rfl⟩) | ⟨h1, _⟩
  · rw [mem_singleton_iff] at h1
    rw [h1, ENNReal.toReal_zero, Wbar_zero]
    exact h2
  · have hz0 := NL.pos_of_mem_Xplus hz
    simp only [ENNReal.toReal_ofReal hz0.le, Wbar_pos NL hz0]
    exact ⟨(NL.W_mem ha haJ hz0).1, le_rfl⟩
  · exact absurd (mem_singleton_iff.1 h1) hp1

/-- The objective `d ↦ u(W̄(z + d) - y) + W̄(m - d)` of `eq:normalizedobjective`. -/
private def Fobj (m z y d : ℝ) : ℝ := P.U.u (NL.Wbar (z + d) - y) + NL.Wbar (m - d)

private lemma Hc_eq (m : ℝ) {p : ℝ≥0∞ × ℝ} (hp : p.1 ≠ ⊤) :
    NL.Hc m p = sSup (NL.Fobj m p.1.toReal p.2 '' NL.A m) := by
  unfold Hc; rw [ite_eq_right hp]; rfl

private lemma Hc_top (m : ℝ) {p : ℝ≥0∞ × ℝ} (hp : p.1 = ⊤) : NL.Hc m p = NL.W m := by
  unfold Hc; rw [ite_eq_left hp]

/-- Per-transfer bounds: the utility argument is nonnegative and
`F(d) ≤ u(L - y) + W(m)`. -/
private lemma Fobj_bounds (ha : 0 < a) (haJ : a < S.jump) {m z y d : ℝ} (hm : 0 < m)
    (hz : 0 ≤ z) (hy : y ≤ NL.Wbar z) (hd : d ∈ Icc 0 m) :
    0 ≤ NL.Wbar (z + d) - y ∧ NL.Fobj m z y d ≤ P.U.u (NL.Lsup - y) + NL.W m := by
  have h1 : NL.Wbar z ≤ NL.Wbar (z + d) := NL.Wbar_mono ha haJ hz (by linarith [hd.1])
  have h2 : NL.Wbar (z + d) ≤ NL.Lsup := NL.Wbar_le_Lsup ha haJ (by linarith [hd.1])
  have h3 : NL.Wbar (m - d) ≤ NL.Wbar m := NL.Wbar_mono ha haJ (by linarith [hd.2]) (by linarith [hd.1])
  refine ⟨by linarith, ?_⟩
  unfold Fobj
  rw [Wbar_pos NL hm] at h3
  have h4 := P.U.monotoneOn (show NL.Wbar (z + d) - y ∈ Ici (0 : ℝ) from by
    simp only [mem_Ici]; linarith) (show NL.Lsup - y ∈ Ici (0 : ℝ) from by
    simp only [mem_Ici]; linarith) (by linarith)
  linarith

private lemma Fobj_zero {m z y : ℝ} (hm : 0 < m)
    (hy : y ≤ NL.Wbar z) : NL.W m ≤ NL.Fobj m z y 0 := by
  unfold Fobj
  rw [add_zero, sub_zero, Wbar_pos NL hm]
  linarith [P.U.nonneg (show 0 ≤ NL.Wbar z - y by linarith)]

private lemma bddAbove_Fobj (ha : 0 < a) (haJ : a < S.jump) {m z y : ℝ} (hm : 0 < m)
    (hz : 0 ≤ z) (hy : y ≤ NL.Wbar z) : BddAbove (NL.Fobj m z y '' NL.A m) := by
  refine ⟨P.U.u (NL.Lsup - y) + NL.W m, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  exact (NL.Fobj_bounds ha haJ hm hz hy (NL.A_subset m hd)).2

/-- `eq:normalizedbounds`. -/
private lemma Hc_bounds (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus)
    {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW) (hp1 : p.1 ≠ ⊤) :
    NL.W m ≤ NL.Hc m p ∧ NL.Hc m p ≤ P.U.u (NL.Lsup - p.2) + NL.W m := by
  have hm0 := NL.pos_of_mem_Xplus hm
  obtain ⟨-, hy⟩ := NL.finite_EW ha haJ hp hp1
  have hz : 0 ≤ p.1.toReal := ENNReal.toReal_nonneg
  rw [NL.Hc_eq m hp1]
  refine ⟨(NL.Fobj_zero hm0 hy).trans
    (le_csSup (NL.bddAbove_Fobj ha haJ hm0 hz hy) ⟨0, NL.zero_mem_A hm0.le, rfl⟩), ?_⟩
  refine csSup_le ⟨_, 0, NL.zero_mem_A hm0.le, rfl⟩ ?_
  rintro _ ⟨d, hd, rfl⟩
  exact (NL.Fobj_bounds ha haJ hm0 hz hy (NL.A_subset m hd)).2

/-! ### Convergence of the grid objective -/

/-- Lower bound ingredient: along feasible grid transfers with `j_k δ_k → d`, the grid objective
converges to `F(d)` (when the landing points stay away from `0` or `J' = 0`). -/
private lemma tendsto_gobj {ψ : ℕ → ℕ} (ha : 0 < a) (haJ : a < S.jump)
    (hψ : Tendsto ψ atTop atTop) {i l j : ℕ → ℕ} {m z y d : ℝ}
    (hiN : ∀ k, i k ≤ S.N (NL.φ (ψ k)))
    (hfeas : ∀ᶠ k in atTop, j k ≤ i k ∧ l k + j k ≤ S.N (NL.φ (ψ k)))
    (him : Tendsto (fun k => (i k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 m))
    (hlz : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 z))
    (hVl : Tendsto (fun k => S.V (NL.φ (ψ k)) (l k)) atTop (𝓝 y))
    (hjd : Tendsto (fun k => (j k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 d))
    (hz : 0 ≤ z) (hd : 0 ≤ d) (hdm : d ≤ m) (hy : y ≤ NL.Wbar (z + d))
    (hzd : 0 < z + d ∨ NL.J' = 0) (hmd : 0 < m - d ∨ NL.J' = 0) :
    Tendsto (fun k => Grid.gobj P.U.u (S.V (NL.φ (ψ k))) (i k) (l k) (j k)) atTop
      (𝓝 (NL.Fobj m z y d)) := by
  have he := NL.eventually_scale_pos ha haJ hψ
  have hδ0 := fun k => δn_nonneg S a (NL.φ (ψ k))
  have h1 := NL.tendsto_Wn hψ (by linarith) (Eventually.of_forall fun k =>
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hδ0 k)) (mul_nonneg (Nat.cast_nonneg _) (hδ0 k)))
    (hlz.add hjd) hzd
  have h2 := NL.tendsto_Wn hψ (sub_nonneg.2 hdm)
    (hfeas.mono fun k hk => sub_nonneg.2 (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hk.1) (hδ0 k))) (him.sub hjd) hmd
  have h3 := tendsto_u (P := P) (sub_nonneg.2 hy) (by
    filter_upwards [he, hfeas] with k hk1 hk2
    rw [Wn_add_eq S hk2.2 hk1.ne']
    exact sub_nonneg.2 ((S.isApproxEq _).cone.incr.le_of_le (Nat.le_add_right _ _) hk2.2))
    (h1.sub hVl)
  refine (h3.add h2).congr' ?_
  filter_upwards [he, hfeas] with k hk1 hk2
  exact (gobj_eq_Wn S hk1.ne' hk2.1 (hiN k) hk2.2).symm

/-- Upper bound ingredient: along feasible grid transfers with `j_k δ_k → d`,
`limsup` of the grid objective is at most `F(d)`. -/
private lemma evLe_gobj {ψ : ℕ → ℕ} (ha : 0 < a) (haJ : a < S.jump)
    (hψ : Tendsto ψ atTop atTop) {i l j : ℕ → ℕ} {m z y d : ℝ}
    (hiN : ∀ k, i k ≤ S.N (NL.φ (ψ k)))
    (hfeas : ∀ᶠ k in atTop, j k ≤ i k ∧ l k + j k ≤ S.N (NL.φ (ψ k)))
    (him : Tendsto (fun k => (i k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 m))
    (hlz : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 z))
    (hVl : Tendsto (fun k => S.V (NL.φ (ψ k)) (l k)) atTop (𝓝 y))
    (hjd : Tendsto (fun k => (j k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 d))
    (hz : 0 ≤ z) (hd : 0 ≤ d) (hdm : d ≤ m) (hy : y ≤ NL.Wbar (z + d)) :
    EvLe (fun k => Grid.gobj P.U.u (S.V (NL.φ (ψ k))) (i k) (l k) (j k)) (NL.Fobj m z y d) := by
  have he := NL.eventually_scale_pos ha haJ hψ
  have hδ0 := fun k => δn_nonneg S a (NL.φ (ψ k))
  have h1 := NL.evLe_Wn hψ (by linarith) (Eventually.of_forall fun k =>
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hδ0 k)) (mul_nonneg (Nat.cast_nonneg _) (hδ0 k)))
    (hlz.add hjd)
  have h2 := NL.evLe_Wn hψ (sub_nonneg.2 hdm)
    (hfeas.mono fun k hk => sub_nonneg.2 (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hk.1) (hδ0 k))) (him.sub hjd)
  have h3 := evLe_u (P := P) (sub_nonneg.2 hy) (by
    filter_upwards [he, hfeas] with k hk1 hk2
    rw [Wn_add_eq S hk2.2 hk1.ne']
    exact sub_nonneg.2 ((S.isApproxEq _).cone.incr.le_of_le (Nat.le_add_right _ _) hk2.2))
    (h1.sub_tendsto hVl)
  refine (h3.add h2).mono_ev ?_
  filter_upwards [he, hfeas] with k hk1 hk2
  exact (gobj_eq_Wn S hk1.ne' hk2.1 (hiN k) hk2.2).le


/-! ### Convergence of maximized payoffs (`prop:passage`, first claim) -/

/-- Limits of normalized grid transfers are admissible transfers. -/
private lemma mem_A_of_tendsto {ψ : ℕ → ℕ} {js : ℕ → ℕ} {m d : ℝ} (hd : d ∈ Icc 0 m)
    (hjd : Tendsto (fun k => (js k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 d)) : d ∈ NL.A m := by
  refine ⟨hd, ?_⟩
  rcases NL.lattice with ⟨hδ, -⟩ | ⟨hδ, hδeq⟩
  · rcases hd.1.eq_or_lt with h | h
    · exact Or.inr (mem_singleton_iff.2 h.symm)
    · left; unfold Xplus; rw [ite_eq_left hδ]; exact h
  · simp only [hδeq] at hjd
    obtain ⟨j, rfl, -⟩ := nat_mul_tendsto hδ hjd
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · right; simp
    · left; unfold Xplus; rw [ite_eq_right hδ.ne']; exact ⟨j, hj, rfl⟩

/-- Lower bound: for every admissible transfer `d₀`, eventually `F(d₀) - ε ≤ H_{V_n}`. -/
private lemma ev_ge_gH (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {i l : ℕ → ℕ} {z y : ℝ} (hz : 0 ≤ z) (hyz : y ≤ NL.Wbar z)
    (hiN : ∀ k, i k ≤ S.N (NL.φ (ψ k))) (hlN : ∀ k, l k ≤ S.N (NL.φ (ψ k)))
    (him : Tendsto (fun k => (i k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 m))
    (hlz : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 z))
    (hVl : Tendsto (fun k => S.V (NL.φ (ψ k)) (l k)) atTop (𝓝 y)) {d0 : ℝ} (hd0 : d0 ∈ NL.A m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, NL.Fobj m z y d0 - ε ≤
      Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k) := by
  have hm0 := NL.pos_of_mem_Xplus hm
  have key : ∀ (j : ℕ → ℕ) (d : ℝ),
      (∀ᶠ k in atTop, j k ≤ i k ∧ l k + j k ≤ S.N (NL.φ (ψ k))) →
      Tendsto (fun k => Grid.gobj P.U.u (S.V (NL.φ (ψ k))) (i k) (l k) (j k)) atTop
        (𝓝 (NL.Fobj m z y d)) →
      NL.Fobj m z y d0 - ε < NL.Fobj m z y d →
      ∀ᶠ k in atTop, NL.Fobj m z y d0 - ε ≤
        Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k) := by
    intro j d hfeas hconv hlt
    filter_upwards [hfeas, hconv.eventually_const_lt hlt] with k hk1 hk2
    exact hk2.le.trans (Grid.gobj_le_gH P.U (hiN k) (hlN k) ((Grid.mem_feas (hiN k) (hlN k)).2 hk1))
  rcases NL.lattice with ⟨hδ, hδt⟩ | ⟨hδ, hδeq⟩
  · -- non-lattice: approximate `d₀` from inside `(0, m)`
    have hδt' : Tendsto (fun k => S.δn a (NL.φ (ψ k))) atTop (𝓝 0) := hδt.comp hψ
    have hW := (NL.props ha haJ).2.2.1
    have hFc : ContinuousOn (NL.Fobj m z y) (Icc 0 m) := by
      unfold Fobj
      refine ContinuousOn.add ?_ ?_
      · show ContinuousOn (fun d => P.U.u (NL.Wbar (z + d) - y)) (Icc 0 m)
        refine P.U.continuousOn.comp
          ((hW.comp (continuousOn_const.add continuousOn_id) ?_).sub continuousOn_const) ?_
        · intro d hd; simp only [mem_Ici, Pi.add_apply, id]; linarith [hd.1]
        · intro d hd; exact (NL.Fobj_bounds ha haJ hm0 hz hyz hd).1
      · show ContinuousOn (fun d => NL.Wbar (m - d)) (Icc 0 m)
        refine hW.comp (continuousOn_const.sub continuousOn_id) ?_
        intro d hd; simp only [mem_Ici]; linarith [hd.2]
    obtain ⟨d', hd', hlt⟩ : ∃ d' ∈ Ioo 0 m, NL.Fobj m z y d0 - ε < NL.Fobj m z y d' := by
      have h1 : NL.Fobj m z y d0 ∈ closure (NL.Fobj m z y '' Ioo 0 m) :=
        ((hFc d0 (NL.A_subset m hd0)).mono Ioo_subset_Icc_self).mem_closure_image
          (by rw [closure_Ioo hm0.ne]; exact NL.A_subset m hd0)
      obtain ⟨_, ⟨d', hd', rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 h1 ε hε
      refine ⟨d', hd', ?_⟩
      rw [Real.dist_eq, abs_lt] at hdist
      linarith [hdist.2]
    set j : ℕ → ℕ := fun k => ⌊d' / S.δn a (NL.φ (ψ k))⌋₊ with hj_def
    have hδpos : ∀ᶠ k in atTop, 0 < S.δn a (NL.φ (ψ k)) :=
      (NL.eventually_scale_pos ha haJ hψ).mono fun k hk => div_pos (S.h_pos _) hk
    have hjle : ∀ k, (j k : ℝ) * S.δn a (NL.φ (ψ k)) ≤ d' := by
      intro k
      rcases (δn_nonneg S a (NL.φ (ψ k))).eq_or_lt with h0 | h0
      · rw [← h0, mul_zero]; exact hd'.1.le
      · have := Nat.floor_le (div_nonneg hd'.1.le h0.le)
        calc (j k : ℝ) * S.δn a (NL.φ (ψ k)) ≤ d' / S.δn a (NL.φ (ψ k)) * S.δn a (NL.φ (ψ k)) :=
              mul_le_mul_of_nonneg_right this h0.le
          _ = d' := div_mul_cancel₀ _ h0.ne'
    have hjgt : ∀ᶠ k in atTop, d' - S.δn a (NL.φ (ψ k)) ≤ (j k : ℝ) * S.δn a (NL.φ (ψ k)) := by
      filter_upwards [hδpos] with k hk
      have h1 := Nat.lt_floor_add_one (d' / S.δn a (NL.φ (ψ k)))
      have h2 : d' < ((j k : ℝ) + 1) * S.δn a (NL.φ (ψ k)) := by
        rw [← div_lt_iff₀ hk]; exact h1
      linarith
    have hjd : Tendsto (fun k => (j k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 d') := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds hjgt
        (Eventually.of_forall hjle)
      simpa using (tendsto_const_nhds (x := d')).sub hδt'
    have hfeas : ∀ᶠ k in atTop, j k ≤ i k ∧ l k + j k ≤ S.N (NL.φ (ψ k)) := by
      filter_upwards [hδpos, him.eventually_const_lt hd'.2,
        NL.ev_add_le_N ha haJ hψ (hlz.add hjd)] with k hk1 hk2 hk3
      refine ⟨?_, hk3⟩
      have : (j k : ℝ) * S.δn a (NL.φ (ψ k)) < (i k : ℝ) * S.δn a (NL.φ (ψ k)) :=
        (hjle k).trans_lt hk2
      exact_mod_cast (lt_of_mul_lt_mul_right this hk1.le).le
    exact key j d' hfeas (NL.tendsto_gobj ha haJ hψ hiN hfeas him hlz hVl hjd hz hd'.1.le
      hd'.2.le (hyz.trans (NL.Wbar_mono ha haJ hz (by linarith [hd'.1])))
      (Or.inl (by linarith [hd'.1])) (Or.inl (by linarith [hd'.2]))) hlt
  · -- lattice: `d₀ = j₀ δ` is itself a grid transfer
    have hJ := NL.lattice_J' ha haJ hδ
    obtain ⟨hd0m, hd0X⟩ := hd0
    obtain ⟨j0, hj0⟩ : ∃ j0 : ℕ, d0 = j0 * NL.δ := by
      rcases hd0X with hX | h0
      · unfold Xplus at hX; rw [ite_eq_right hδ.ne'] at hX
        obtain ⟨k, -, hk⟩ := hX
        exact ⟨k, hk⟩
      · exact ⟨0, by rw [mem_singleton_iff.1 h0]; simp⟩
    have him' : Tendsto (fun k => (i k : ℝ) * NL.δ) atTop (𝓝 m) := by
      simpa only [hδeq] using him
    obtain ⟨km, hkm, hikm⟩ := nat_mul_tendsto hδ him'
    have hj0km : j0 ≤ km := by
      have : (j0 : ℝ) * NL.δ ≤ km * NL.δ := by rw [← hj0, ← hkm]; exact hd0m.2
      exact_mod_cast le_of_mul_le_mul_right this hδ
    have hjd : Tendsto (fun k => ((fun _ : ℕ => j0) k : ℝ) * S.δn a (NL.φ (ψ k))) atTop
        (𝓝 d0) := by
      simp only [hδeq, hj0]; exact tendsto_const_nhds
    have hfeas : ∀ᶠ k in atTop, (fun _ : ℕ => j0) k ≤ i k ∧
        l k + (fun _ : ℕ => j0) k ≤ S.N (NL.φ (ψ k)) := by
      filter_upwards [hikm, NL.ev_add_le_N ha haJ hψ (hlz.add hjd)] with k hk1 hk2
      exact ⟨hk1 ▸ hj0km, hk2⟩
    exact key (fun _ => j0) d0 hfeas (NL.tendsto_gobj ha haJ hψ hiN hfeas him hlz hVl hjd hz
      hd0m.1 hd0m.2 (hyz.trans (NL.Wbar_mono ha haJ hz (by linarith [hd0m.1])))
      (Or.inr hJ) (Or.inr hJ)) (by linarith)

/-- Convergence of maximized payoffs at a finite normalized state. -/
private lemma conv_finite (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus)
    {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) {i l : ℕ → ℕ} {z y : ℝ} (hz : 0 ≤ z)
    (hyz : y ≤ NL.Wbar z)
    (hiN : ∀ k, i k ≤ S.N (NL.φ (ψ k))) (hlN : ∀ k, l k ≤ S.N (NL.φ (ψ k)))
    (him : Tendsto (fun k => (i k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 m))
    (hlz : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 z))
    (hVl : Tendsto (fun k => S.V (NL.φ (ψ k)) (l k)) atTop (𝓝 y)) :
    Tendsto (fun k => Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k)) atTop
      (𝓝 (sSup (NL.Fobj m z y '' NL.A m))) := by
  have hm0 := NL.pos_of_mem_Xplus hm
  have hbdd := NL.bddAbove_Fobj ha haJ hm0 hz hyz
  have hne : (NL.Fobj m z y '' NL.A m).Nonempty := ⟨_, 0, NL.zero_mem_A hm0.le, rfl⟩
  refine tendsto_of_evLe ?_ ?_
  · -- upper bound: optimal transfers along a further subsequence
    refine evLe_of_subseq fun ns hns => ?_
    have hns' := hns.tendsto_atTop
    have hψn : Tendsto (fun k => ψ (ns k)) atTop atTop := hψ.comp hns'
    choose js hjs hjeq using fun k => Grid.exists_gH_eq P.U (V := S.V (NL.φ (ψ (ns k))))
      (hiN (ns k)) (hlN (ns k))
    have hjs' := fun k => (Grid.mem_feas (hiN (ns k)) (hlN (ns k))).1 (hjs k)
    have himn := him.comp hns'
    have hfreq : ∃ᶠ k in atTop,
        (js k : ℝ) * S.δn a (NL.φ (ψ (ns k))) ∈ Icc 0 (m + 1) := by
      refine Eventually.frequently ?_
      filter_upwards [himn.eventually_lt_const (lt_add_one m)] with k hk
      exact ⟨mul_nonneg (Nat.cast_nonneg _) (δn_nonneg S a _),
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (hjs' k).1) (δn_nonneg S a _)).trans hk.le⟩
    obtain ⟨d, hd, ms, hms, hjd⟩ := isCompact_Icc.tendsto_subseq' hfreq
    have hms' := hms.tendsto_atTop
    have hψnm : Tendsto (fun k => ψ (ns (ms k))) atTop atTop := hψn.comp hms'
    have hdm : d ≤ m := le_of_tendsto_of_tendsto' hjd (himn.comp hms') fun k =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast (hjs' (ms k)).1) (δn_nonneg S a _)
    have hdA : d ∈ NL.A m := NL.mem_A_of_tendsto (ψ := fun k => ψ (ns (ms k))) ⟨hd.1, hdm⟩ hjd
    refine ⟨ms, hms, ?_⟩
    have key := NL.evLe_gobj (ψ := fun k => ψ (ns (ms k))) (i := fun k => i (ns (ms k)))
      (l := fun k => l (ns (ms k))) (j := fun k => js (ms k)) ha haJ hψnm (fun k => hiN _)
      (Eventually.of_forall fun k => hjs' (ms k)) (him.comp (hns'.comp hms'))
      (hlz.comp (hns'.comp hms')) (hVl.comp (hns'.comp hms')) hjd hz hd.1 hdm
      (hyz.trans (NL.Wbar_mono ha haJ hz (by linarith [hd.1])))
    exact (key.mono_ev (Eventually.of_forall fun k => (hjeq (ms k)).ge)).trans_le
      (le_csSup hbdd ⟨d, hdA, rfl⟩)
  · -- lower bound
    intro ε hε
    obtain ⟨_, ⟨d0, hd0, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne
      (show sSup (NL.Fobj m z y '' NL.A m) - ε / 2 < sSup (NL.Fobj m z y '' NL.A m) by linarith)
    filter_upwards [NL.ev_ge_gH ha haJ hm hψ hz hyz hiN hlN him hlz hVl hd0 (half_pos hε)]
      with k hk
    linarith

/-- Convergence of maximized payoffs for sellers escaping to infinity (grid tail-seller
estimate). -/
private lemma conv_top (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus)
    {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) {i l : ℕ → ℕ}
    (hiN : ∀ k, i k ≤ S.N (NL.φ (ψ k))) (hlN : ∀ k, l k ≤ S.N (NL.φ (ψ k)))
    (him : Tendsto (fun k => (i k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 m))
    (hlz : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k))) atTop atTop) :
    Tendsto (fun k => Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k)) atTop
      (𝓝 (NL.W m)) := by
  have hm0 := NL.pos_of_mem_Xplus hm
  have he := NL.eventually_scale_pos ha haJ hψ
  have hVi : Tendsto (fun k => S.V (NL.φ (ψ k)) (i k)) atTop (𝓝 (NL.W m)) := by
    refine (NL.tendsto_Wn_pos hψ hm0 him).congr' ?_
    filter_upwards [he] with k hk
    exact (V_eq_Wn S (hiN k) hk.ne').symm
  have hbound : Tendsto (fun k => P.U.c0 * P.Lstar * ((i k : ℝ) * S.δn a (NL.φ (ψ k))) *
      ((l k : ℝ) * S.δn a (NL.φ (ψ k)))⁻¹) atTop (𝓝 0) := by
    have := (him.const_mul (P.U.c0 * P.Lstar)).mul (tendsto_inv_atTop_zero.comp hlz)
    simpa using this
  have hdiff : Tendsto (fun k => Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k) -
      S.V (NL.φ (ψ k)) (i k)) atTop (𝓝 0) := by
    have hts : ∀ᶠ k in atTop, 0 ≤ Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k) -
        S.V (NL.φ (ψ k)) (i k) ∧
        Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k) -
          S.V (NL.φ (ψ k)) (i k) ≤ P.U.c0 * P.Lstar * ((i k : ℝ) * S.δn a (NL.φ (ψ k))) *
            ((l k : ℝ) * S.δn a (NL.φ (ψ k)))⁻¹ := by
      filter_upwards [he, hlz.eventually_gt_atTop 0] with k hk1 hk2
      have hδ : 0 < S.δn a (NL.φ (ψ k)) := div_pos (S.h_pos _) hk1
      have hl0 : (0 : ℝ) < l k := pos_of_mul_pos_left hk2 hδ.le
      have hl1 : 1 ≤ l k := by exact_mod_cast hl0
      have hE := S.isApproxEq (NL.φ (ψ k))
      have hts := tailseller_grid P.U hE.cone.incr hE.cone.zero (L := P.Lstar)
        (fun i hi => (V_mem S _ hi).2) (hiN k) hl1 (hlN k)
      refine ⟨hts.1, ?_⟩
      have : P.U.c0 * (i k : ℝ) * P.Lstar / (l k : ℝ) = P.U.c0 * P.Lstar *
          ((i k : ℝ) * S.δn a (NL.φ (ψ k))) * ((l k : ℝ) * S.δn a (NL.φ (ψ k)))⁻¹ := by
        field_simp
      linarith [hts.2.1, hts.2.2.1, hts.2.2.2]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (hts.mono fun k hk => hk.1) (hts.mono fun k hk => hk.2)
  simpa using hdiff.add hVi

/-- `prop:passage`, first claim, along an arbitrary subsequence `ψ` of the normalizing
subsequence. -/
private lemma conv (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) (i l : ℕ → ℕ) {z : ℝ≥0∞} {y : ℝ} (hzy : (z, y) ∈ NL.EW)
    (hiN : ∀ k, i k ≤ S.N (NL.φ (ψ k))) (hlN : ∀ k, l k ≤ S.N (NL.φ (ψ k)))
    (him : Tendsto (fun k => (i k : ℝ) * S.h (NL.φ (ψ k)) / S.scale a (NL.φ (ψ k))) atTop
      (𝓝 m))
    (hil : Tendsto (fun k => S.ι a (NL.φ (ψ k)) ((l k : ℝ) * S.h (NL.φ (ψ k)))) atTop
      (𝓝 (z, y))) :
    Tendsto (fun k => Grid.gH P.U.u (S.N (NL.φ (ψ k))) (S.V (NL.φ (ψ k))) (i k) (l k)) atTop
      (𝓝 (NL.Hc m (z, y))) := by
  have him' : Tendsto (fun k => (i k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 m) := by
    simpa only [SelectedSeq.δn, mul_div_assoc] using him
  have hfst : Tendsto (fun k => ENNReal.ofReal ((l k : ℝ) * S.δn a (NL.φ (ψ k)))) atTop
      (𝓝 z) := by
    have := hil.fst_nhds
    simpa only [SelectedSeq.ι, SelectedSeq.δn, mul_div_assoc] using this
  have hVl : Tendsto (fun k => S.V (NL.φ (ψ k)) (l k)) atTop (𝓝 y) := by
    have := hil.snd_nhds
    simp only [SelectedSeq.ι] at this
    exact this.congr fun k => Vn_natCast S (hlN k)
  by_cases hz : z = ⊤
  · subst hz
    rw [NL.Hc_top m rfl]
    exact NL.conv_top ha haJ hm hψ hiN hlN him' (tendsto_atTop_of_ofReal hfst)
  · rw [NL.Hc_eq m hz]
    obtain ⟨-, hyz⟩ := NL.finite_EW ha haJ hzy hz
    have hlz : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 z.toReal) := by
      have := (ENNReal.tendsto_toReal hz).comp hfst
      refine this.congr fun k => ?_
      simp only [Function.comp,
        ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (δn_nonneg S a _))]
    exact NL.conv_finite ha haJ hm hψ ENNReal.toReal_nonneg hyz hiN hlN him' hlz hVl


/-! ### Limits of normalized grid states are compatible -/

/-- Limits of normalized grid states `ι_n(l_n h_n)` lie in `ℰ_W` (the pointwise content of
`eq:compatiblestates`). -/
private lemma mem_EW (ha : 0 < a) (haJ : a < S.jump) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop)
    (l : ℕ → ℕ) (hlN : ∀ k, l k ≤ S.N (NL.φ (ψ k))) {p : ℝ≥0∞ × ℝ}
    (hp : Tendsto (fun k => S.ι a (NL.φ (ψ k)) ((l k : ℝ) * S.h (NL.φ (ψ k)))) atTop (𝓝 p)) :
    p ∈ NL.EW := by
  obtain ⟨z, y⟩ := p
  have he := NL.eventually_scale_pos ha haJ hψ
  have hfst : Tendsto (fun k => ENNReal.ofReal ((l k : ℝ) * S.δn a (NL.φ (ψ k)))) atTop
      (𝓝 z) := by
    have := hp.fst_nhds
    simpa only [SelectedSeq.ι, SelectedSeq.δn, mul_div_assoc] using this
  have hVl : Tendsto (fun k => S.V (NL.φ (ψ k)) (l k)) atTop (𝓝 y) := by
    have := hp.snd_nhds
    simp only [SelectedSeq.ι] at this
    exact this.congr fun k => Vn_natCast S (hlN k)
  have hWl : ∀ᶠ k in atTop, S.Wn a (NL.φ (ψ k)) ((l k : ℝ) * S.δn a (NL.φ (ψ k))) =
      S.V (NL.φ (ψ k)) (l k) := by
    filter_upwards [he] with k hk
    exact (V_eq_Wn S (hlN k) hk.ne').symm
  have hy0 : 0 ≤ y := ge_of_tendsto' hVl fun k => (V_mem S _ (hlN k)).1
  have hyL : y ≤ P.Lstar := le_of_tendsto' hVl fun k => (V_mem S _ (hlN k)).2
  have hδ0 := fun k => δn_nonneg S a (NL.φ (ψ k))
  unfold NormalizedLimit.EW
  by_cases hz : z = ⊤
  · subst hz
    refine Or.inr ⟨mem_singleton _, ?_, hyL⟩
    have hlz := tendsto_atTop_of_ofReal hfst
    refine csSup_le NL.W_image_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := eventually_ge_of_tendsto_atTop (B := P.Lstar) (fun k => Wn_monotoneOn S a _)
      (fun k => Wn_concaveOn S a _) (fun k x _ => Wn_mem S a _ x) (NL.W_conv_comp hψ) hlz hx hε
    have : NL.W x - ε ≤ y := ge_of_tendsto hVl (by
      filter_upwards [h1, hWl] with k hk1 hk2
      rw [← hk2]; exact hk1)
    linarith
  · have hlz : Tendsto (fun k => (l k : ℝ) * S.δn a (NL.φ (ψ k))) atTop (𝓝 z.toReal) := by
      have := (ENNReal.tendsto_toReal hz).comp hfst
      refine this.congr fun k => ?_
      simp only [Function.comp,
        ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (δn_nonneg S a _))]
    rcases (ENNReal.toReal_nonneg (a := z)).eq_or_lt with h0 | h0
    · have hz0 : z = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff z).1 h0.symm with h | h
        · exact h
        · exact absurd h hz
      subst hz0
      rw [ENNReal.toReal_zero] at hlz
      refine Or.inl (Or.inl ⟨mem_singleton _, hy0, ?_⟩)
      have h1 := NL.evLe_Wn hψ le_rfl
        (Eventually.of_forall fun k => mul_nonneg (Nat.cast_nonneg _) (hδ0 k)) hlz
      rw [Wbar_zero] at h1
      exact (h1.mono_ev (hWl.mono fun k hk => hk.ge)).le_lim hVl
    · have hyW : y = NL.W z.toReal :=
        tendsto_nhds_unique hVl ((NL.tendsto_Wn_pos hψ h0 hlz).congr' hWl)
      refine Or.inl (Or.inr ⟨z.toReal, ?_, ?_⟩)
      · rcases NL.lattice with ⟨hδ, -⟩ | ⟨hδ, hδeq⟩
        · unfold Xplus; rw [ite_eq_left hδ]; exact h0
        · simp only [hδeq] at hlz
          obtain ⟨j, hj, -⟩ := nat_mul_tendsto hδ hlz
          unfold Xplus; rw [ite_eq_right hδ.ne']
          refine ⟨j, ?_, hj⟩
          rcases Nat.eq_zero_or_pos j with rfl | hj'
          · rw [Nat.cast_zero, zero_mul] at hj; linarith
          · exact hj'
      · rw [ENNReal.ofReal_toReal hz, hyW]

/-! ### Continuity of `ℋ(m; ·)` on `ℰ_W` -/

private lemma isCompact_A (m : ℝ) : IsCompact (NL.A m) := by
  rcases NL.lattice with ⟨hδ, -⟩ | ⟨hδ, -⟩
  · have : NL.A m = Icc 0 m := by
      ext d
      refine ⟨fun hd => hd.1, fun hd => ⟨hd, ?_⟩⟩
      rcases hd.1.eq_or_lt with h | h
      · exact Or.inr h.symm
      · left; unfold Xplus; rw [ite_eq_left hδ]; exact h
    rw [this]; exact isCompact_Icc
  · refine Set.Finite.isCompact ?_
    refine ((Finset.range (⌊m / NL.δ⌋₊ + 1)).finite_toSet.image
      (fun k : ℕ => (k : ℝ) * NL.δ)).subset ?_
    rintro d ⟨hd, hdX⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d = k * NL.δ := by
      rcases hdX with hX | h0
      · unfold Xplus at hX; rw [ite_eq_right hδ.ne'] at hX
        obtain ⟨k, -, hk⟩ := hX
        exact ⟨k, hk⟩
      · exact ⟨0, by rw [mem_singleton_iff.1 h0]; simp⟩
    refine ⟨k, ?_, hk.symm⟩
    simp only [Finset.coe_range, mem_Iio]
    have : (k : ℝ) ≤ m / NL.δ := by rw [le_div_iff₀ hδ, ← hk]; exact hd.2
    exact Nat.lt_succ_of_le (Nat.le_floor this)

private lemma contOn (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus) :
    ContinuousOn (NL.Hc m) NL.EW := by
  have hm0 := NL.pos_of_mem_Xplus hm
  have hW := (NL.props ha haJ).2.2.1
  intro p0 hp0
  by_cases hp1 : p0.1 = ⊤
  · -- the infinite fiber: `0 ≤ ℋ(m; z, W z) - W(m) ≤ c₀ (L - W(z)) → 0` as `z → ∞`
    rw [ContinuousWithinAt, NL.Hc_top m hp1, Metric.tendsto_nhds]
    intro ε hε
    have hc0 := P.U.c0_pos
    obtain ⟨_, ⟨Z, hZ, rfl⟩, hZlt⟩ := exists_lt_of_lt_csSup NL.W_image_nonempty
      (show NL.Lsup - ε / P.U.c0 < NL.Lsup by have := div_pos hε hc0; linarith)
    have hopen : IsOpen {p : ℝ≥0∞ × ℝ | ENNReal.ofReal Z < p.1} :=
      isOpen_lt continuous_const continuous_fst
    have hmem : p0 ∈ {p : ℝ≥0∞ × ℝ | ENNReal.ofReal Z < p.1} := by
      show ENNReal.ofReal Z < p0.1
      rw [hp1]; exact ENNReal.ofReal_lt_top
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)]
      with p hpE hpZ
    by_cases hpt : p.1 = ⊤
    · rw [NL.Hc_top m hpt, dist_self]; exact hε
    · have hb := NL.Hc_bounds ha haJ hm hpE hpt
      rcases hpE with (⟨h1, -⟩ | ⟨z', hz', rfl⟩) | ⟨h1, -⟩
      · exfalso
        rw [mem_singleton_iff] at h1
        have h2 : ENNReal.ofReal Z < p.1 := hpZ
        rw [h1] at h2
        exact not_lt_zero h2
      · have hz'0 := NL.pos_of_mem_Xplus hz'
        have hpZ' : ENNReal.ofReal Z < ENNReal.ofReal z' := hpZ
        have hZz : Z < z' := (ENNReal.ofReal_lt_ofReal_iff'.1 hpZ').1
        have hWZ : NL.W Z ≤ NL.W z' := by
          have := NL.Wbar_mono ha haJ (le_of_lt hZ) hZz.le
          rwa [Wbar_pos NL hZ, Wbar_pos NL hz'0] at this
        have hLW : 0 ≤ NL.Lsup - NL.W z' := sub_nonneg.2 (NL.W_le_Lsup ha haJ hz'0)
        have hu := P.U.le_c0_mul hLW
        have h1 : NL.Lsup - NL.W z' < ε / P.U.c0 := by linarith
        have h2 : P.U.c0 * (NL.Lsup - NL.W z') < ε := by
          calc P.U.c0 * (NL.Lsup - NL.W z') < P.U.c0 * (ε / P.U.c0) :=
                mul_lt_mul_of_pos_left h1 hc0
            _ = ε := mul_div_cancel₀ _ hc0.ne'
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hb.1, hb.2]
      · exact absurd (mem_singleton_iff.1 h1) hpt
  · -- finite states: a maximum of a continuous function over the fixed compact set `𝒜_m`
    have hAc : IsCompact (NL.A m) := NL.isCompact_A m
    set Wt : ℝ → ℝ := fun x => NL.Wbar (max x 0) with hWt_def
    have hWt : Continuous Wt :=
      hW.comp_continuous (continuous_id.max continuous_const) fun x => le_max_right x 0
    set ut : ℝ → ℝ := fun x => P.U.u (max x 0) with hut_def
    have hut : Continuous ut :=
      P.U.continuousOn.comp_continuous (continuous_id.max continuous_const)
        fun x => le_max_right x 0
    set f : ℝ × ℝ → ℝ → ℝ := fun q d => ut (Wt (q.1 + d) - q.2) + Wt (m - d) with hf_def
    have hf : Continuous ↿f := by
      show Continuous (fun x : (ℝ × ℝ) × ℝ => ut (Wt (x.1.1 + x.2) - x.1.2) + Wt (m - x.2))
      fun_prop
    have hG := hAc.continuous_sSup hf
    have hg : ContinuousAt (fun p : ℝ≥0∞ × ℝ => (p.1.toReal, p.2)) p0 :=
      ((ENNReal.tendsto_toReal hp1).comp continuous_fst.continuousAt).prodMk_nhds
        continuous_snd.continuousAt
    have heq : ∀ p ∈ NL.EW, p.1 ≠ ⊤ → NL.Hc m p = sSup (f (p.1.toReal, p.2) '' NL.A m) := by
      intro p hp hpt
      rw [NL.Hc_eq m hpt]
      obtain ⟨-, hy⟩ := NL.finite_EW ha haJ hp hpt
      refine congrArg sSup (Set.image_congr fun d hd => ?_)
      have hd' := NL.A_subset m hd
      have hz : 0 ≤ p.1.toReal := ENNReal.toReal_nonneg
      have ht := (NL.Fobj_bounds ha haJ hm0 hz hy hd').1
      simp only [Fobj, hf_def, hut_def, hWt_def]
      rw [max_eq_left (by linarith [hd'.1] : 0 ≤ p.1.toReal + d), max_eq_left ht,
        max_eq_left (by linarith [hd'.2] : 0 ≤ m - d)]
    have hcont : ContinuousAt (fun p : ℝ≥0∞ × ℝ => sSup (f (p.1.toReal, p.2) '' NL.A m)) p0 :=
      hG.continuousAt.comp hg
    refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (heq p0 hp0 hp1)
    have hopen : IsOpen {p : ℝ≥0∞ × ℝ | p.1 ≠ ⊤} := isOpen_ne_fun continuous_fst continuous_const
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hp1)]
      with p hpE hpt
    exact heq p hpE hpt

private lemma Hc_abs_le (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus)
    {p : ℝ≥0∞ × ℝ} (hp : p ∈ NL.EW) : |NL.Hc m p| ≤ P.U.u P.Lstar + P.Lstar := by
  have hm0 := NL.pos_of_mem_Xplus hm
  have hWm := NL.W_mem ha haJ hm0
  have hu0 := P.U.nonneg P.Lstar_pos.le
  by_cases hp1 : p.1 = ⊤
  · rw [NL.Hc_top m hp1, abs_le]; constructor <;> linarith [hWm.1, hWm.2]
  · obtain ⟨hy0, hy⟩ := NL.finite_EW ha haJ hp hp1
    have hb := NL.Hc_bounds ha haJ hm hp hp1
    have hL := NL.Lsup_le_Lstar ha haJ
    have hyL : p.2 ≤ NL.Lsup := hy.trans (NL.Wbar_le_Lsup ha haJ ENNReal.toReal_nonneg)
    have hu := P.U.monotoneOn (show NL.Lsup - p.2 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
      (show P.Lstar ∈ Ici (0 : ℝ) from P.Lstar_pos.le) (by linarith)
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2, hWm.1, hWm.2]

/-! ### The normalized Bellman equation -/

/-- Uniform convergence of the maximized payoffs over all grid sellers, against a continuous
extension `H` of `ℋ(m; ·)|_{ℰ_W}`. -/
private lemma unif (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus) {i : ℕ → ℕ}
    (hiN : ∀ n, i n ≤ S.N (NL.φ n))
    (him : Tendsto (fun n => (i n : ℝ) * S.h (NL.φ n) / S.scale a (NL.φ n)) atTop (𝓝 m))
    {H : ℝ≥0∞ × ℝ → ℝ} (hH : Continuous H) (hHE : ∀ p ∈ NL.EW, H p = NL.Hc m p) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ l ≤ S.N (NL.φ n),
      |Grid.gH P.U.u (S.N (NL.φ n)) (S.V (NL.φ n)) (i n) l -
        H (S.ι a (NL.φ n) ((l : ℝ) * S.h (NL.φ n)))| < ε := by
  by_contra hc
  rw [not_eventually] at hc
  obtain ⟨ψ, hψ, hψ'⟩ := extraction_of_frequently_atTop hc
  simp only [not_forall, not_lt] at hψ'
  choose ls hls hls' using hψ'
  have hK : ∀ k, S.ι a (NL.φ (ψ k)) ((ls k : ℝ) * S.h (NL.φ (ψ k))) ∈
      (univ ×ˢ Icc (0 : ℝ) P.Lstar : Set (ℝ≥0∞ × ℝ)) := fun k => ⟨mem_univ _, Vn_mem S _ _⟩
  obtain ⟨⟨z, y⟩, -, ψ', hψ'', hp⟩ := (isCompact_univ.prod isCompact_Icc).tendsto_subseq hK
  have hψψ : Tendsto (fun k => ψ (ψ' k)) atTop atTop :=
    hψ.tendsto_atTop.comp hψ''.tendsto_atTop
  have hpE : (z, y) ∈ NL.EW :=
    NL.mem_EW ha haJ hψψ (fun k => ls (ψ' k)) (fun k => hls (ψ' k)) hp
  have hconv := NL.conv ha haJ hm hψψ (fun k => i (ψ (ψ' k))) (fun k => ls (ψ' k)) hpE
    (fun k => hiN _) (fun k => hls _) (him.comp hψψ) hp
  have hH' := (hH.tendsto (z, y)).comp hp
  have h0 := (hconv.sub hH').abs
  rw [hHE _ hpE, sub_self, abs_zero] at h0
  obtain ⟨k, hk⟩ := (h0.eventually_lt_const hε).exists
  exact absurd (hls' (ψ' k)) (not_le.2 hk)

private lemma bellman (ha : 0 < a) (haJ : a < S.jump) {m : ℝ} (hm : m ∈ NL.Xplus) :
    NL.W m = P.β * ∫ p, NL.Hc m p ∂NL.α := by
  have hm0 := NL.pos_of_mem_Xplus hm
  have hEc : IsClosed NL.EW := (NL.props ha haJ).2.2.2.2.2.2.1
  have hαE : NL.α NL.EWᶜ = 0 := (NL.props ha haJ).2.2.2.2.2.2.2.1
  -- a bounded continuous (Tietze) extension `H` of `ℋ(m; ·)|_{ℰ_W}`
  let F : BoundedContinuousFunction NL.EW ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (NL.EW.domRestrict (NL.Hc m))
      (NL.contOn ha haJ hm).domRestrict (P.U.u P.Lstar + P.Lstar)
      (fun x => by rw [Real.norm_eq_abs]; exact NL.Hc_abs_le ha haJ hm x.2)
  obtain ⟨H, -, hH⟩ := BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed F hEc
  have hHE : ∀ p ∈ NL.EW, H p = NL.Hc m p := fun p hp => by
    exact congrArg (fun G : BoundedContinuousFunction NL.EW ℝ => G ⟨p, hp⟩) hH
  -- grid buyers `i_n = ⌊m / δ_n⌋` (eventually below `N_n`)
  set i : ℕ → ℕ := fun n => min ⌊m / S.δn a (NL.φ n)⌋₊ (S.N (NL.φ n)) with hi_def
  have hiN : ∀ n, i n ≤ S.N (NL.φ n) := fun n => min_le_right _ _
  have hNδ := NL.tendsto_Nδ ha haJ (ψ := id) tendsto_id
  have hfl : ∀ᶠ n in atTop, i n = ⌊m / S.δn a (NL.φ n)⌋₊ ∧ 0 < S.δn a (NL.φ n) := by
    filter_upwards [hNδ.eventually_ge_atTop m] with n hn
    have hδ : 0 < S.δn a (NL.φ n) := by
      rcases (δn_nonneg S a (NL.φ n)).eq_or_lt with h | h
      · simp only [id, ← h, mul_zero] at hn; linarith
      · exact h
    refine ⟨min_eq_left (Nat.floor_le_of_le ?_), hδ⟩
    rw [div_le_iff₀ hδ]; exact hn
  have him : Tendsto (fun n => (i n : ℝ) * S.δn a (NL.φ n)) atTop (𝓝 m) := by
    rcases NL.lattice with ⟨hδ, hδt⟩ | ⟨hδ, hδeq⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n => m - S.δn a (NL.φ n))
        (h := fun _ => m) ?_ tendsto_const_nhds ?_ ?_
      · simpa using (tendsto_const_nhds (x := m)).sub hδt
      · filter_upwards [hfl] with n hn
        rw [hn.1]
        have h1 := Nat.lt_floor_add_one (m / S.δn a (NL.φ n))
        have h2 : m < ((⌊m / S.δn a (NL.φ n)⌋₊ : ℝ) + 1) * S.δn a (NL.φ n) := by
          rwa [← div_lt_iff₀ hn.2]
        linarith
      · filter_upwards [hfl] with n hn
        rw [hn.1]
        calc (⌊m / S.δn a (NL.φ n)⌋₊ : ℝ) * S.δn a (NL.φ n)
            ≤ m / S.δn a (NL.φ n) * S.δn a (NL.φ n) :=
              mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hm0.le hn.2.le)) hn.2.le
          _ = m := div_mul_cancel₀ _ hn.2.ne'
    · have hmX := hm
      unfold Xplus at hmX; rw [ite_eq_right hδ.ne'] at hmX
      obtain ⟨k, -, hk⟩ := hmX
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hfl] with n hn
      rw [hn.1, hδeq, hk, mul_div_cancel_right₀ _ hδ.ne', Nat.floor_natCast]
  have him' : Tendsto (fun n => (i n : ℝ) * S.h (NL.φ n) / S.scale a (NL.φ n)) atTop (𝓝 m) := by
    simpa only [SelectedSeq.δn, mul_div_assoc] using him
  -- the buyers' values converge to `W(m)`
  have hVi : Tendsto (fun n => S.V (NL.φ n) (i n)) atTop (𝓝 (NL.W m)) := by
    refine (NL.tendsto_Wn_pos (ψ := id) tendsto_id hm0 him).congr' ?_
    filter_upwards [NL.eventually_scale_pos ha haJ (ψ := id) tendsto_id] with n hn
    exact (V_eq_Wn S (hiN n) hn.ne').symm
  -- the exact grid Bellman equation
  set A : ℕ → ℝ := fun n => ∑ l ∈ Finset.range (S.N (NL.φ n) + 1),
    S.η (NL.φ n) l * Grid.gH P.U.u (S.N (NL.φ n)) (S.V (NL.φ n)) (i n) l with hA_def
  have hbell : ∀ n, S.V (NL.φ n) (i n) = P.β * A n := fun n => by
    rw [(S.isApproxEq _).bellman _ (hiN n)]; rfl
  -- integrals against `α_n` are sums over the grid
  have hint : ∀ n, ∫ p, H p ∂(S.αn a (NL.φ n)) = ∑ l ∈ Finset.range (S.N (NL.φ n) + 1),
      S.η (NL.φ n) l * H (S.ι a (NL.φ n) ((l : ℝ) * S.h (NL.φ n))) := by
    intro n
    unfold SelectedSeq.αn SelectedSeq.ηn
    rw [integral_map (continuous_ι S a _).measurable.aemeasurable
      H.continuous.aestronglyMeasurable]
    exact integral_gridMeasure (S.isApproxEq _).law.nonneg _
  have hconvH : Tendsto (fun n => ∫ p, H p ∂(S.αn a (NL.φ n))) atTop (𝓝 (∫ p, H p ∂NL.α)) :=
    NL.α_conv H
  have hdiff : Tendsto (fun n => A n - ∫ p, H p ∂(S.αn a (NL.φ n))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [NL.unif ha haJ hm hiN him' H.continuous hHE (half_pos hε)] with n hn
    rw [Real.dist_eq, sub_zero, hint n]
    have hlaw := (S.isApproxEq (NL.φ n)).law
    calc |A n - ∑ l ∈ Finset.range (S.N (NL.φ n) + 1),
          S.η (NL.φ n) l * H (S.ι a (NL.φ n) ((l : ℝ) * S.h (NL.φ n)))|
        = |∑ l ∈ Finset.range (S.N (NL.φ n) + 1), S.η (NL.φ n) l *
            (Grid.gH P.U.u (S.N (NL.φ n)) (S.V (NL.φ n)) (i n) l -
              H (S.ι a (NL.φ n) ((l : ℝ) * S.h (NL.φ n))))| := by
          rw [hA_def]; simp only [mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ l ∈ Finset.range (S.N (NL.φ n) + 1), |S.η (NL.φ n) l *
            (Grid.gH P.U.u (S.N (NL.φ n)) (S.V (NL.φ n)) (i n) l -
              H (S.ι a (NL.φ n) ((l : ℝ) * S.h (NL.φ n))))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ Finset.range (S.N (NL.φ n) + 1), S.η (NL.φ n) l * (ε / 2) := by
          refine Finset.sum_le_sum fun l hl => ?_
          rw [abs_mul, abs_of_nonneg (hlaw.nonneg l)]
          exact mul_le_mul_of_nonneg_left
            (hn l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))).le (hlaw.nonneg l)
      _ = ε / 2 := by rw [← Finset.sum_mul, hlaw.sum_one, one_mul]
      _ < ε := half_lt_self hε
  have hA : Tendsto A atTop (𝓝 (∫ p, H p ∂NL.α)) := by
    simpa using hdiff.add hconvH
  have h1 : Tendsto (fun n => P.β * A n) atTop (𝓝 (P.β * ∫ p, H p ∂NL.α)) := hA.const_mul _
  have h2 : Tendsto (fun n => P.β * A n) atTop (𝓝 (NL.W m)) := hVi.congr hbell
  rw [tendsto_nhds_unique h2 h1]
  congr 1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ p ∂NL.α, p ∈ NL.EW := mem_ae_iff.2 hαE
  filter_upwards [hae] with p hp using hHE p hp

end NormalizedLimit

/-- `prop:passage` (passage of the Bellman equations): for `m ∈ 𝒳₊` and grid states with
`m_n / e_n → m` and `ι_n(s_n) → (z, y) ∈ ℰ_W`, the maximized payoffs converge,
`H_{V_n}(m_n, s_n) → ℋ(m; z, y)`; `ℋ(m; ·)` is continuous on `ℰ_W`; the normalized Bellman
equation `eq:normalizedbellman` holds; and on finite normalized states
`W(m) ≤ ℋ(m; z, y) ≤ u(L - y) + W(m)` (`eq:normalizedbounds`). -/
theorem NormalizedLimit.passage {S : SelectedSeq P} {a : ℝ} (NL : NormalizedLimit S a)
    (ha : 0 < a) (haJ : a < S.jump) :
    (∀ m ∈ NL.Xplus, ∀ (i l : ℕ → ℕ) (z : ℝ≥0∞) (y : ℝ), (z, y) ∈ NL.EW →
      (∀ n, i n ≤ S.N (NL.φ n)) → (∀ n, l n ≤ S.N (NL.φ n)) →
      Tendsto (fun n => (i n : ℝ) * S.h (NL.φ n) / S.scale a (NL.φ n)) atTop (𝓝 m) →
      Tendsto (fun n => S.ι a (NL.φ n) ((l n : ℝ) * S.h (NL.φ n))) atTop (𝓝 (z, y)) →
      Tendsto (fun n => Grid.gH P.U.u (S.N (NL.φ n)) (S.V (NL.φ n)) (i n) (l n)) atTop
        (𝓝 (NL.Hc m (z, y)))) ∧
    (∀ m ∈ NL.Xplus, ContinuousOn (NL.Hc m) NL.EW) ∧
    (∀ m ∈ NL.Xplus, NL.W m = P.β * ∫ p, NL.Hc m p ∂NL.α) ∧
    (∀ m ∈ NL.Xplus, ∀ p ∈ NL.EW, p.1 ≠ ⊤ →
      NL.W m ≤ NL.Hc m p ∧ NL.Hc m p ≤ P.U.u (NL.Lsup - p.2) + NL.W m) :=
  ⟨fun _ hm i l _ _ hzy hi hl him hil =>
      NL.conv ha haJ hm (ψ := id) tendsto_id i l hzy hi hl him hil,
    fun _ hm => NL.contOn ha haJ hm, fun _ hm => NL.bellman ha haJ hm,
    fun _ hm _ hp hp1 => NL.Hc_bounds ha haJ hm hp hp1⟩

end Molico
