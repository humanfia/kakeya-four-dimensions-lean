/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactParents.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.ContactTransfer

/-!
# Contact parents give the frozen result

`ContactParent p a r k C c₁ e₀'` is the per-index input of the contact end: a
parent label at depth `r`, a row normalization `(B, λ)`, a dense retained set `G`
on which the normalized contact equation holds, and a base correction `Gb` of
the native polynomial with `|P - Gb(base)| ≤ C a_r` on the retained lines over
the parent block and `‖Gb‖ ≤ N^c₁`.

`result_of_contact_parents`: if contact parents exist frequently (fixed `r < U`,
`e₀'`, `c₁`, one subpolynomial constant `C`), the contact principle gives the
original `Result`. The slow choices (grid levels, step, pruning threshold,
witness scale, diagonal atlas range, zoomed constant) are made by
`exists_slow_diag` at levels `n_m → ∞`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter Topology MvPolynomial
open scoped ENNReal
open PreparedModel
open Submission.Lib.K4ContactNormalization (point baseCalibratedTest)
open Submission.Lib.K4ChartLifting (coeffL1)

noncomputable section

/-- **Slow diagonal.** If a property holds eventually in `k` at every level `n`, and
`k_m → ∞`, then levels `n_m → ∞` exist along which it holds eventually. -/
theorem exists_slow_diag {P : ℕ → ℕ → Prop} (hP : ∀ n, ∀ᶠ k in atTop, P n k)
    {kseq : ℕ → ℕ} (hk : Tendsto kseq atTop atTop) :
    ∃ nseq : ℕ → ℕ, Tendsto nseq atTop atTop ∧ ∀ᶠ m in atTop, P (nseq m) (kseq m) := by
  classical
  have h0 : ∀ n, ∃ a, ∀ b ≥ a, P n b := fun n => eventually_atTop.mp (hP n)
  choose K₀ hK₀ using h0
  set K₁ : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup K₀ with hK₁
  have hK₁ge : ∀ n, K₀ n ≤ K₁ n := fun n =>
    Finset.le_sup (f := K₀) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  set nseq : ℕ → ℕ := fun m => Nat.findGreatest (fun n => K₁ n ≤ kseq m) m with hnseq
  refine ⟨nseq, ?_, ?_⟩
  · rw [tendsto_atTop_atTop]
    intro N
    obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp (hk.eventually_ge_atTop (K₁ N))
    refine ⟨max N m₁, fun m hm => ?_⟩
    exact Nat.le_findGreatest (le_trans (le_max_left _ _) hm) (hm₁ m (le_trans (le_max_right _ _) hm))
  · filter_upwards [hk.eventually_ge_atTop (K₁ 0)] with m hm
    have hspec : K₁ (nseq m) ≤ kseq m :=
      Nat.findGreatest_spec (P := fun n => K₁ n ≤ kseq m) (Nat.zero_le m) hm
    exact hK₀ _ _ ((hK₁ge _).trans hspec)

/-- Grid count at level `n`. -/
def levM (U' : ℝ) (n : ℕ) : ℕ := ⌈U' * ((n : ℝ) + 1)⌉₊ + 1

/-- Grid step at level `n`: exactly `U'/(M+1)`. -/
def levδ (U' : ℝ) (n : ℕ) : ℝ := U' / ((levM U' n : ℝ) + 1)

theorem levδ_pos {U' : ℝ} (hU : 0 < U') (n : ℕ) : 0 < levδ U' n := by
  unfold levδ; positivity

theorem levδ_mul (U' : ℝ) (n : ℕ) : ((levM U' n : ℝ) + 1) * levδ U' n = U' := by
  unfold levδ; field_simp

theorem levδ_le {U' : ℝ} (hU : 0 < U') (n : ℕ) : levδ U' n ≤ 1 / ((n : ℝ) + 1) := by
  unfold levδ levM
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : U' * ((n : ℝ) + 1) ≤ (⌈U' * ((n : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_div_iff₀ (by positivity) hn]
  push_cast
  nlinarith

theorem levM_pos (U' : ℝ) (n : ℕ) : 0 < levM U' n := by unfold levM; omega

theorem tendsto_levδ {U' : ℝ} (hU : 0 < U') {nseq : ℕ → ℕ} (hn : Tendsto nseq atTop atTop) :
    Tendsto (fun m => levδ U' (nseq m)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m => 1 / ((nseq m : ℝ) + 1)) atTop (𝓝 0) := by
    have : Tendsto (fun m => ((nseq m : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hn)
    have h2 := this.inv_tendsto_atTop
    refine h2.congr (fun m => ?_)
    simp [one_div]
  exact squeeze_zero (fun m => (levδ_pos hU _).le) (fun m => levδ_le hU _) h1

variable {α : Type} [MeasurableSpace α]

/-- **Contact data at one original index**: a parent at depth `r` with a row
normalization, a dense retained contact set and a base correction of the native
polynomial, all controlled by one constant `C` (and `‖Gb‖ ≤ N^c₁`). -/
structure ContactParent (p : Parameters) (a : PreparedModel α) (r : ℝ) (k : ℕ)
    (C c₁ e₀' : ℝ) where
  Q : Fin (a.n k r)
  B : Fin 2 → ℝ
  lam : ℝ
  G : Set (α × ℝ)
  Gb : MvPolynomial (Fin 3) ℝ
  G_meas : MeasurableSet G
  G_sub : G ⊆ a.B k r Q ×ˢ a.block k r Q
  mass : ENNReal.ofReal (a.q k r / C) * a.nu k (a.A k r Q) ≤ a.rho k G
  lam_ne : lam ≠ 0
  lam_inv_le : |lam⁻¹| ≤ C
  lam_le : |lam| ≤ C
  B_le : |B 0| + |B 1| ≤ C
  contact : ∀ z ∈ G, |Zoom.nCoeff (parentZoom p a k r Q) B lam (a.b k z.1) 4 +
    Zoom.nCoeff (parentZoom p a k r Q) B lam (a.b k z.1) 0| ≤ p.N k ^ (-e₀')
  Gb_deg : Gb.totalDegree ≤ 2
  signal : ∀ z ∈ G, ∀ t ∈ a.block k r Q,
    |eval (point (a.b k z.1) t) (baseCalibratedTest (a.P k) Gb)| ≤ C * width p k r
  Gb_le : coeffL1 Gb ≤ p.N k ^ c₁

/-- Atlas range at level `n`. -/
def levR (r : ℝ) (n : ℕ) : ℝ := (n : ℝ) + 2 + r⁻¹

/-- Witness velocity scale at level `n`. -/
def levv (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- The zoomed constant at level `n` and original index `k`. -/
def levKz (p : Parameters) (U' C : ℝ) (n k : ℕ) : ℝ :=
  p.K k + 2 * C + (2 * p.K k + C * (2 * p.K k + C + 2 * C * p.K k)) + 108 * p.K k ^ 2 * C +
    p.K k ^ 2 * p.N k ^ ((p.kappa + p.d + p.ell) * levδ U' n) +
    2 * 4 ^ levM U' n / (1 / (4 * C)) +
    (4 * p.K k + C * (4 * p.K k + 12 * p.K k ^ 2 / p.N k ^ (-levv n) + C)) +
    p.K k * C * p.N k ^ ((1 + p.ell) * levδ U' n) + C

/-- Conditions at level `n` and original index `k`. -/
def LevelOK (p : Parameters) (a : PreparedModel α) (r U' : ℝ) (Cf : ℕ → ℝ) (n k : ℕ) : Prop :=
  (∀ s : ℝ, (levR r n)⁻¹ ≤ s → s ≤ p.U → a.AtlasAt p (levR r n) k s) ∧
  (∀ m' : ℤ, a.pi k {w | ⌊w / p.N k ^ (-levv n)⌋ = m'} ≤
    ENNReal.ofReal (p.K k * p.N k ^ (-p.S * levv n))) ∧
  p.K k ≤ p.N k ^ (p.S * levv n / 8) ∧ Cf k ≤ p.N k ^ (p.S * levv n / 8) ∧
  (4 : ℝ) ^ levM U' n ≤ p.N k ^ (p.S * levv n / 8) ∧ (24 : ℝ) ≤ p.N k ^ (p.S * levv n / 8)

theorem levR_gt {r : ℝ} (hr : 0 < r) (n : ℕ) : 1 < levR r n := by
  unfold levR; have := inv_pos.mpr hr; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith

theorem levR_inv_le {r : ℝ} (hr : 0 < r) (n : ℕ) : (levR r n)⁻¹ ≤ r := by
  have h : r⁻¹ ≤ levR r n := by unfold levR; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have := inv_anti₀ (inv_pos.mpr hr) h
  rwa [inv_inv] at this

theorem levv_pos (n : ℕ) : 0 < levv n := by unfold levv; positivity

theorem levv_le_one (n : ℕ) : levv n ≤ 1 := by
  unfold levv
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem levR_inv_le_levv {r : ℝ} (hr : 0 < r) (n : ℕ) : (levR r n)⁻¹ ≤ levv n := by
  unfold levR levv
  rw [one_div]
  apply inv_anti₀ (by positivity)
  have := inv_pos.mpr hr
  linarith

/-- **Level conditions hold eventually** at every level. -/
theorem levelOK_eventually {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) {r U' : ℝ} (hr : 0 < r) {Cf : ℕ → ℝ}
    (hCsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Cf k ≤ p.N k ^ ε) (n : ℕ) :
    ∀ᶠ k in atTop, LevelOK p a r U' Cf n k := by
  have hS : 0 < p.S := hp.2.2.2.2.2.2.2.2.1
  have hη : 0 < p.S * levv n / 8 := by have := levv_pos n; positivity
  have hR := levR_gt hr n
  have hNinf : Tendsto (fun k => p.N k ^ (p.S * levv n / 8)) atTop atTop :=
    (tendsto_rpow_atTop hη).comp hp.2.1
  filter_upwards [ha.2.2.1 (levR r n) hR, ha.2.1 (levR r n) hR,
    hp.2.2.1.2 _ hη, hCsub _ hη, hNinf.eventually_ge_atTop ((4 : ℝ) ^ levM U' n),
    hNinf.eventually_ge_atTop 24] with k h1 h2 h3 h4 h5 h6
  refine ⟨h1, ?_, h3, h4, h5, h6⟩
  have hR1 : 1 ≤ levR r n := hR.le
  have h2' := h2 1 0 (levv n) (inv_le_one_of_one_le₀ hR1) hR1 le_rfl (by linarith)
    (levR_inv_le_levv hr n) ((levv_le_one n).trans hR1)
  exact h2'.1

/-- **Pruning gaps** from the level conditions. -/
theorem gaps_of_levelOK {p : Parameters} (hp : p.Valid) {a : PreparedModel α} {r U' : ℝ}
    {Cf : ℕ → ℝ} {n k : ℕ} (hC1 : 1 ≤ Cf k) (h : LevelOK p a r U' Cf n k)
    (j : Fin (levM U' n)) :
    3 * (p.K k * (p.K k * p.N k ^ (-p.S * levv n))) <
      (1 / (4 * Cf k)) * (1 / 4 : ℝ) ^ (j : ℕ) / 2 := by
  obtain ⟨-, -, hK, hC, h4, h24⟩ := h
  set X := p.N k ^ (p.S * levv n / 8) with hX
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hN1 : 1 < p.N k := by linarith [hp.1 k]
  have hS : 0 < p.S := hp.2.2.2.2.2.2.2.2.1
  have hv := levv_pos n
  have hK0 : 0 ≤ p.K k := le_trans zero_le_one (hp.2.2.1.1 k)
  have hX0 : 0 ≤ X := by positivity
  have hX5 : X ^ 5 < p.N k ^ (p.S * levv n) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    apply Real.rpow_lt_rpow_of_exponent_lt hN1
    push_cast
    nlinarith
  have h4j : (4 : ℝ) ^ (j : ℕ) ≤ X :=
    (pow_le_pow_right₀ (by norm_num) j.2.le).trans h4
  have hprod : 24 * p.K k ^ 2 * Cf k * 4 ^ (j : ℕ) ≤ X ^ 5 := by
    calc 24 * p.K k ^ 2 * Cf k * 4 ^ (j : ℕ) ≤ X * X ^ 2 * X * X := by
          gcongr
      _ = X ^ 5 := by ring
  have key : 24 * p.K k ^ 2 * Cf k * 4 ^ (j : ℕ) < p.N k ^ (p.S * levv n) :=
    lt_of_le_of_lt hprod hX5
  have hNS : p.N k ^ (-p.S * levv n) = (p.N k ^ (p.S * levv n))⁻¹ := by
    rw [neg_mul, Real.rpow_neg hN0.le]
  have hP : 0 < p.N k ^ (p.S * levv n) := by positivity
  have h4p : (0 : ℝ) < 4 ^ (j : ℕ) := by positivity
  have hC0 : 0 < Cf k := by linarith
  rw [hNS, one_div_pow]
  rw [show 3 * (p.K k * (p.K k * (p.N k ^ (p.S * levv n))⁻¹)) =
      3 * p.K k ^ 2 / p.N k ^ (p.S * levv n) by field_simp,
    show 1 / (4 * Cf k) * (1 / 4 ^ (j : ℕ)) / 2 = 1 / (8 * Cf k * 4 ^ (j : ℕ)) by
      field_simp; ring]
  rw [div_lt_div_iff₀ hP (by positivity)]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Bound for the zoomed constant** from the level conditions. -/
theorem levKz_le {p : Parameters} (hp : p.Valid) {a : PreparedModel α} {r U' : ℝ}
    (hU : 0 < U') {Cf : ℕ → ℝ} {n k : ℕ} (hC1 : 1 ≤ Cf k) (h : LevelOK p a r U' Cf n k) :
    levKz p U' (Cf k) n k ≤
      150 * p.N k ^ ((6 + p.kappa + p.d + 2 * p.ell) * levv n) := by
  obtain ⟨-, -, hK, hC, h4, -⟩ := h
  have hN0 : 0 < p.N k := by linarith [hp.1 k]
  have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
  have hS : 0 < p.S := hp.2.2.2.2.2.2.2.2.1
  have hS1 : p.S ≤ 1 := hp.2.2.2.2.2.2.2.2.2.1
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hd : 0 ≤ p.d := hp.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hv := levv_pos n
  have hK0 : 0 ≤ p.K k := le_trans zero_le_one (hp.2.2.1.1 k)
  have hC0 : 0 ≤ Cf k := by linarith
  set Y := p.N k ^ levv n with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 hv.le
  have hsmall : p.N k ^ (p.S * levv n / 8) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hKY : p.K k ≤ Y := hK.trans hsmall
  have hCY : Cf k ≤ Y := hC.trans hsmall
  have h4Y : (4 : ℝ) ^ levM U' n ≤ Y := h4.trans hsmall
  set B := 6 + p.kappa + p.d + 2 * p.ell with hB
  have hpow : ∀ c : ℝ, 0 ≤ c → c ≤ B → p.N k ^ (c * levv n) ≤ p.N k ^ (B * levv n) :=
    fun c _ hc => Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hYn : ∀ m : ℕ, Y ^ m = p.N k ^ ((m : ℝ) * levv n) := by
    intro m
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hY2 : Y ^ 2 ≤ p.N k ^ (B * levv n) := by
    rw [hYn]; exact hpow _ (by norm_num) (by push_cast; linarith)
  have hY3 : Y ^ 3 ≤ p.N k ^ (B * levv n) := by
    rw [hYn]; exact hpow _ (by norm_num) (by push_cast; linarith)
  have hY4 : Y ^ 4 ≤ p.N k ^ (B * levv n) := by
    rw [hYn]; exact hpow _ (by norm_num) (by push_cast; linarith)
  have hY1' : Y ≤ p.N k ^ (B * levv n) := by
    have := hYn 1; rw [pow_one] at this; rw [this]
    exact hpow _ (by norm_num) (by push_cast; linarith)
  have hδv := levδ_le hU n
  have hδ0 := (levδ_pos hU n).le
  have hgrid : p.N k ^ ((p.kappa + p.d + p.ell) * levδ U' n) ≤
      p.N k ^ ((p.kappa + p.d + p.ell) * levv n) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by unfold levv at *; nlinarith)
  have hrow : p.N k ^ ((1 + p.ell) * levδ U' n) ≤ p.N k ^ ((1 + p.ell) * levv n) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by unfold levv at *; nlinarith)
  have hT5 : p.K k ^ 2 * p.N k ^ ((p.kappa + p.d + p.ell) * levδ U' n) ≤
      p.N k ^ (B * levv n) := by
    calc p.K k ^ 2 * p.N k ^ ((p.kappa + p.d + p.ell) * levδ U' n)
        ≤ Y ^ 2 * p.N k ^ ((p.kappa + p.d + p.ell) * levv n) := by gcongr
      _ = p.N k ^ ((2 + (p.kappa + p.d + p.ell)) * levv n) := by
          rw [hYn, ← Real.rpow_add hN0]; push_cast; ring_nf
      _ ≤ p.N k ^ (B * levv n) := hpow _ (by positivity) (by linarith)
  have hT8 : p.K k * Cf k * p.N k ^ ((1 + p.ell) * levδ U' n) ≤ p.N k ^ (B * levv n) := by
    calc p.K k * Cf k * p.N k ^ ((1 + p.ell) * levδ U' n)
        ≤ Y * Y * p.N k ^ ((1 + p.ell) * levv n) := by gcongr
      _ = p.N k ^ ((2 + (1 + p.ell)) * levv n) := by
          rw [show Y * Y = Y ^ 2 by ring, hYn, ← Real.rpow_add hN0]; push_cast; ring_nf
      _ ≤ p.N k ^ (B * levv n) := hpow _ (by positivity) (by linarith)
  have hinv : 1 / p.N k ^ (-levv n) = Y := by
    rw [Real.rpow_neg hN0.le, one_div, inv_inv]
  have hT6 : 2 * 4 ^ levM U' n / (1 / (4 * Cf k)) ≤ 8 * Y ^ 2 := by
    have e : 2 * (4 : ℝ) ^ levM U' n / (1 / (4 * Cf k)) = 8 * Cf k * 4 ^ levM U' n := by
      have : (4 : ℝ) * Cf k ≠ 0 := by positivity
      field_simp
      ring
    rw [e]
    have h40 : (0 : ℝ) ≤ 4 ^ levM U' n := by positivity
    calc 8 * Cf k * 4 ^ levM U' n ≤ 8 * Y * Y := by gcongr
      _ = 8 * Y ^ 2 := by ring
  have hYa : Y ≤ Y ^ 2 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ 2 := pow_le_pow_right₀ hY1 (by norm_num)
  have hYb : Y ^ 2 ≤ Y ^ 3 := pow_le_pow_right₀ hY1 (by norm_num)
  have hYc : Y ^ 3 ≤ Y ^ 4 := pow_le_pow_right₀ hY1 (by norm_num)
  have hT3 : 2 * p.K k + Cf k * (2 * p.K k + Cf k + 2 * Cf k * p.K k) ≤ 7 * Y ^ 3 := by
    have h1 : 2 * p.K k + Cf k + 2 * Cf k * p.K k ≤ 2 * Y + Y + 2 * Y * Y := by gcongr
    have h2 : Cf k * (2 * p.K k + Cf k + 2 * Cf k * p.K k) ≤ Y * (2 * Y + Y + 2 * Y * Y) :=
      mul_le_mul hCY h1 (by positivity) (by positivity)
    have e : Y * (2 * Y + Y + 2 * Y * Y) = 3 * Y ^ 2 + 2 * Y ^ 3 := by ring
    linarith
  have hT4 : 108 * p.K k ^ 2 * Cf k ≤ 108 * Y ^ 3 := by
    have : p.K k ^ 2 * Cf k ≤ Y ^ 2 * Y := by gcongr
    have e : Y ^ 2 * Y = Y ^ 3 := by ring
    linarith
  have hT7 : 4 * p.K k + Cf k * (4 * p.K k + 12 * p.K k ^ 2 / p.N k ^ (-levv n) + Cf k) ≤
      21 * Y ^ 4 := by
    have e : 12 * p.K k ^ 2 / p.N k ^ (-levv n) = 12 * p.K k ^ 2 * Y := by
      rw [div_eq_mul_one_div, hinv]
    rw [e]
    have h1 : 4 * p.K k + 12 * p.K k ^ 2 * Y + Cf k ≤ 4 * Y + 12 * Y ^ 2 * Y + Y := by gcongr
    have h2 : Cf k * (4 * p.K k + 12 * p.K k ^ 2 * Y + Cf k) ≤ Y * (4 * Y + 12 * Y ^ 2 * Y + Y) :=
      mul_le_mul hCY h1 (by positivity) (by positivity)
    have e : Y * (4 * Y + 12 * Y ^ 2 * Y + Y) = 5 * Y ^ 2 + 12 * Y ^ 4 := by ring
    linarith
  unfold levKz
  have hNB : 0 ≤ p.N k ^ (B * levv n) := by positivity
  linarith [hKY, hCY, hY1', hY2, hY3, hY4, hT3, hT4, hT5, hT6, hT7, hT8]

/-- The nine summands of the zoomed constant are nonnegative. -/
theorem levKz_terms {p : Parameters} (hp : p.Valid) {U' C : ℝ} (hC : 0 ≤ C) (n k : ℕ) :
    0 ≤ p.K k ∧ 0 ≤ 2 * C ∧ 0 ≤ 2 * p.K k + C * (2 * p.K k + C + 2 * C * p.K k) ∧
      0 ≤ 108 * p.K k ^ 2 * C ∧ 0 ≤ p.K k ^ 2 * p.N k ^ ((p.kappa + p.d + p.ell) * levδ U' n) ∧
      0 ≤ 2 * 4 ^ levM U' n / (1 / (4 * C)) ∧
      0 ≤ 4 * p.K k + C * (4 * p.K k + 12 * p.K k ^ 2 / p.N k ^ (-levv n) + C) ∧
      0 ≤ p.K k * C * p.N k ^ ((1 + p.ell) * levδ U' n) ∧ 0 ≤ C := by
  have hK : 0 ≤ p.K k := le_trans zero_le_one (hp.2.2.1.1 k)
  have hN : 0 < p.N k := by linarith [hp.1 k]
  refine ⟨hK, by positivity, by positivity, by positivity, by positivity, by positivity,
    by positivity, by positivity, hC⟩

set_option maxHeartbeats 3200000 in
/-- **Frequent contact parents give the frozen result** under the contact
principle: for a fixed parent depth `0 < r < U`, contact exponent `e₀'` and
sheet exponent `c₁`, with one subpolynomial constant `Cf`. All slow choices
(grid, pruning, witness scales, diagonal atlas range, zoomed constant) are
made here. -/
theorem result_of_contact_parents {p : Parameters} (hp : p.Valid) {a : PreparedModel α}
    (ha : a.Valid p) (hCMP : ContactModelPrinciple) {r e₀' c₁ : ℝ} (hr : 0 < r)
    (hrU : r < p.U) (he : 0 < e₀') (hc₁ : 0 ≤ c₁) (Cf : ℕ → ℝ) (hC1 : ∀ k, 1 ≤ Cf k)
    (hCsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Cf k ≤ p.N k ^ ε)
    (hfreq : ∃ᶠ k in atTop, Nonempty (ContactParent p a r k (Cf k) c₁ e₀')) :
    a.Result p := by
  classical
  obtain ⟨φ, hφmono, hφ⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hφt : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  set U' := (p.U - r) / 2 with hU'
  have hU'0 : 0 < U' := by rw [hU']; linarith
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  have hd : 0 ≤ p.d := hp.2.2.2.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  -- the sheet coefficient condition, eventually in `k`
  have hGbev : ∀ᶠ k in atTop, (p.N k ^ c₁ + 1) * (2 + p.K k) ^ 2 *
      ((2 * p.K k + Cf k + 1) * Cf k * p.K k) ≤ p.N k ^ (c₁ + 1) := by
    have hNinf : Tendsto (fun k => p.N k ^ ((1 : ℝ) / 16)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp hp.2.1
    filter_upwards [hp.2.2.1.2 ((1 : ℝ) / 16) (by norm_num), hCsub ((1 : ℝ) / 16) (by norm_num),
      hNinf.eventually_ge_atTop 1000] with k hK hC hN1000
    have hN0 : 0 < p.N k := by linarith [hp.1 k]
    have hN1 : 1 ≤ p.N k := by linarith [hp.1 k]
    set X := p.N k ^ ((1 : ℝ) / 16) with hX
    have hX1 : 1 ≤ X := by linarith
    have hK1 := hp.2.2.1.1 k
    have hCk := hC1 k
    have hNc : 1 ≤ p.N k ^ c₁ := Real.one_le_rpow hN1 hc₁
    have hX16 : X ^ 16 = p.N k := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have h1 : (p.N k ^ c₁ + 1) ≤ 2 * p.N k ^ c₁ := by linarith
    have h2 : (2 + p.K k) ^ 2 ≤ 9 * X ^ 2 := by
      have : 2 + p.K k ≤ 3 * X := by linarith
      nlinarith
    have h3 : (2 * p.K k + Cf k + 1) * Cf k * p.K k ≤ 4 * X ^ 3 := by
      have ha1 : 2 * p.K k + Cf k + 1 ≤ 4 * X := by linarith
      have : (2 * p.K k + Cf k + 1) * Cf k ≤ 4 * X * X :=
        mul_le_mul ha1 hC (by linarith) (by linarith)
      calc (2 * p.K k + Cf k + 1) * Cf k * p.K k ≤ 4 * X * X * X :=
            mul_le_mul this hK (by linarith) (by positivity)
        _ = 4 * X ^ 3 := by ring
    have hX5 : X ^ 5 ≤ X ^ 16 := pow_le_pow_right₀ hX1 (by norm_num)
    have h72 : (72 : ℝ) ≤ X ^ 11 := by
      have : X ≤ X ^ 11 := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ 11 := pow_le_pow_right₀ hX1 (by norm_num)
      linarith
    calc (p.N k ^ c₁ + 1) * (2 + p.K k) ^ 2 * ((2 * p.K k + Cf k + 1) * Cf k * p.K k)
        ≤ (2 * p.N k ^ c₁) * (9 * X ^ 2) * (4 * X ^ 3) := by
          gcongr
      _ = p.N k ^ c₁ * (72 * X ^ 5) := by ring
      _ ≤ p.N k ^ c₁ * (X ^ 11 * X ^ 5) := by gcongr
      _ = p.N k ^ c₁ * X ^ 16 := by ring
      _ = p.N k ^ (c₁ + 1) := by rw [hX16, Real.rpow_add hN0, Real.rpow_one]
  obtain ⟨nseq, hn, hev⟩ := exists_slow_diag
    (P := fun n k => LevelOK p a r U' Cf n k ∧ ((p.N k ^ c₁ + 1) * (2 + p.K k) ^ 2 *
      ((2 * p.K k + Cf k + 1) * Cf k * p.K k) ≤ p.N k ^ (c₁ + 1)))
    (fun n => (levelOK_eventually hp ha hr hCsub n).and hGbev) hφt
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hev
  have hok : ∀ m, LevelOK p a r U' Cf (nseq (m + m₀)) (φ (m + m₀)) ∧
      ((p.N (φ (m + m₀)) ^ c₁ + 1) * (2 + p.K (φ (m + m₀))) ^ 2 *
        ((2 * p.K (φ (m + m₀)) + Cf (φ (m + m₀)) + 1) * Cf (φ (m + m₀)) * p.K (φ (m + m₀))) ≤
          p.N (φ (m + m₀)) ^ (c₁ + 1)) := fun m => hm₀ (m + m₀) (by omega)
  have hshift : Tendsto (fun m => m + m₀) atTop atTop := tendsto_add_atTop_nat m₀
  have hkk : Tendsto (fun m => φ (m + m₀)) atTop atTop := hφt.comp hshift
  have hnn : Tendsto (fun m => nseq (m + m₀)) atTop atTop := hn.comp hshift
  let D : ∀ m, ContactParent p a r (φ (m + m₀)) (Cf (φ (m + m₀))) c₁ e₀' :=
    fun m => Classical.choice (hφ (m + m₀))
  let I : ℕ → ZoomInput p a r := fun m =>
    ⟨φ (m + m₀), (D m).Q, (D m).B, (D m).lam, (D m).G, levM U' (nseq (m + m₀)),
      levδ U' (nseq (m + m₀)), 1 / (4 * Cf (φ (m + m₀))),
      Zoom.nPush (parentZoom p a (φ (m + m₀)) r (D m).Q) (D m).B (D m).lam
        (baseCalibratedTest (a.P (φ (m + m₀))) (D m).Gb)⟩
  let Z : ZoomSeq p a r :=
    ⟨I, fun m => levM_pos U' (nseq (m + m₀)), fun m => (D m).Gb, fun m => Cf (φ (m + m₀)),
      fun m => Cf (φ (m + m₀)), fun m => levR r (nseq (m + m₀)), fun m => levv (nseq (m + m₀)),
      fun m => levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀)), U', e₀'⟩
  have hterms := fun m => levKz_terms hp (U' := U') (le_trans zero_le_one (hC1 (φ (m + m₀))))
    (nseq (m + m₀)) (φ (m + m₀))
  have hdepth : ∀ m (j : Fin (levM U' (nseq (m + m₀)))),
      r ≤ r + (((j : ℕ) : ℝ) + 1) * levδ U' (nseq (m + m₀)) ∧
        r + (((j : ℕ) : ℝ) + 1) * levδ U' (nseq (m + m₀)) ≤ p.U := by
    intro m j
    have hδ := levδ_pos hU'0 (nseq (m + m₀))
    have hmul := levδ_mul U' (nseq (m + m₀))
    have hj : ((j : ℕ) : ℝ) + 1 ≤ (levM U' (nseq (m + m₀)) : ℝ) + 1 := by
      have := j.2; have : ((j : ℕ) : ℝ) < levM U' (nseq (m + m₀)) := by exact_mod_cast this
      linarith
    constructor
    · have : 0 ≤ (((j : ℕ) : ℝ) + 1) * levδ U' (nseq (m + m₀)) := by positivity
      linarith
    · have := mul_le_mul_of_nonneg_right hj hδ.le
      rw [hU'] at hmul
      linarith
  have hZ : Z.Good := by
    refine
      { r_pos := hr
        k_tendsto := hkk
        Pn_eq := fun m => rfl
        Gb_deg := fun m => (D m).Gb_deg
        R_gt := fun m => levR_gt hr _
        R_tendsto := ?_
        atlas_r := fun m => (hok m).1.1 r (levR_inv_le hr _) hrU.le
        atlas_depth := fun m j => (hok m).1.1 _ ((levR_inv_le hr _).trans (hdepth m j).1)
          (hdepth m j).2
        G_meas := fun m => (D m).G_meas
        G_sub := fun m => (D m).G_sub
        MG_pos := fun m => lt_of_lt_of_le zero_lt_one (hC1 _)
        θ_pos := fun m => by
          have := hC1 (φ (m + m₀)); show 0 < 1 / (4 * Cf (φ (m + m₀))); positivity
        θ_le := fun m => by
          have := hC1 (φ (m + m₀))
          show 4 * (1 / (4 * Cf (φ (m + m₀)))) ≤ 1 / Cf (φ (m + m₀))
          rw [show 4 * (1 / (4 * Cf (φ (m + m₀)))) = 1 / Cf (φ (m + m₀)) by field_simp]
        mass := fun m => (D m).mass
        lam_ne := fun m => (D m).lam_ne
        M₁_ge := fun m => hC1 _
        lam_inv_le := fun m => (D m).lam_inv_le
        lam_le := fun m => (D m).lam_le
        B_le := fun m => (D m).B_le
        δ_pos := fun m => levδ_pos hU'0 _
        δ_tendsto := tendsto_levδ hU'0 hnn
        U'_le := fun m => by
          show U' ≤ ((levM U' (nseq (m + m₀)) : ℝ) + 1) * levδ U' (nseq (m + m₀))
          rw [levδ_mul]
        depth_le := fun m => by
          show r + ((levM U' (nseq (m + m₀)) : ℝ) + 1) * levδ U' (nseq (m + m₀)) ≤ p.U
          rw [levδ_mul, hU']; linarith
        vs_ge := fun m => levR_inv_le_levv hr _
        vs_le := fun m => (levv_le_one _).trans (levR_gt hr _).le
        pi_vs := fun m => (hok m).1.2.1
        gaps := fun m j => gaps_of_levelOK hp (hC1 _) (hok m).1 j
        contact := fun m => (D m).contact
        signal := fun m z hz t ht => by
          have h := (D m).signal z hz t ht
          refine h.trans (mul_le_mul_of_nonneg_right ?_ (width_pos p hp _ r).le)
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show Cf (φ (m + m₀)) ≤ levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Gb_coeff := ?_
        Kz_K := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show p.K (φ (m + m₀)) ≤ levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_MG := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show 2 * Cf (φ (m + m₀)) ≤ levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_coeff := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show 2 * p.K (φ (m + m₀)) + Cf (φ (m + m₀)) * (2 * p.K (φ (m + m₀)) + Cf (φ (m + m₀)) +
            2 * Cf (φ (m + m₀)) * p.K (φ (m + m₀))) ≤
              levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_caps := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show 108 * p.K (φ (m + m₀)) ^ 2 * Cf (φ (m + m₀)) ≤
            levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_grid := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show p.K (φ (m + m₀)) ^ 2 * p.N (φ (m + m₀)) ^ ((p.kappa + p.d + p.ell) *
            levδ U' (nseq (m + m₀))) ≤ levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_prune := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show 2 * 4 ^ levM U' (nseq (m + m₀)) / (1 / (4 * Cf (φ (m + m₀)))) ≤
            levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_box := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show 4 * p.K (φ (m + m₀)) + Cf (φ (m + m₀)) * (4 * p.K (φ (m + m₀)) +
            12 * p.K (φ (m + m₀)) ^ 2 / p.N (φ (m + m₀)) ^ (-levv (nseq (m + m₀))) +
              Cf (φ (m + m₀))) ≤ levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_row := fun m => by
          obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hterms m
          show p.K (φ (m + m₀)) * Cf (φ (m + m₀)) * p.N (φ (m + m₀)) ^ ((1 + p.ell) *
            levδ U' (nseq (m + m₀))) ≤ levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀))
          unfold levKz; linarith
        Kz_sub := ?_
        U'_pos := hU'0
        e₀'_pos := he }
    · -- R_tendsto
      show Tendsto (fun m => levR r (nseq (m + m₀))) atTop atTop
      unfold levR
      have h1 : Tendsto (fun m => ((nseq (m + m₀) : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hnn
      exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ h1)
    · -- Gb_coeff
      refine ⟨c₁ + 1, by linarith, Eventually.of_forall fun m => ?_⟩
      have h := (hok m).2
      have hG := (D m).Gb_le
      have hK0 : 0 ≤ p.K (φ (m + m₀)) := le_trans zero_le_one (hp.2.2.1.1 _)
      have hC0 : 0 ≤ Cf (φ (m + m₀)) := le_trans zero_le_one (hC1 _)
      show (coeffL1 (D m).Gb + 1) * (2 + p.K (φ (m + m₀))) ^ 2 *
          ((2 * p.K (φ (m + m₀)) + Cf (φ (m + m₀)) + 1) * Cf (φ (m + m₀)) * p.K (φ (m + m₀))) ≤
        p.N (φ (m + m₀)) ^ (c₁ + 1)
      refine le_trans ?_ h
      gcongr
    · -- Kz_sub
      intro ε hε
      set B := 6 + p.kappa + p.d + 2 * p.ell with hB
      have hB0 : 0 < B := by positivity
      have hv0 : Tendsto (fun m => levv (nseq (m + m₀))) atTop (𝓝 0) := by
        unfold levv
        have : Tendsto (fun m => ((nseq (m + m₀) : ℕ) : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hnn)
        have h2 := this.inv_tendsto_atTop
        refine h2.congr (fun m => ?_)
        simp [one_div]
      have hNinf : Tendsto (fun m => p.N (φ (m + m₀)) ^ (ε / 2)) atTop atTop :=
        (tendsto_rpow_atTop (by positivity)).comp (hp.2.1.comp hkk)
      filter_upwards [hv0.eventually (ge_mem_nhds (show 0 < ε / (2 * B) by positivity)),
        hNinf.eventually_ge_atTop 150] with m hm1 hm2
      have hN1 : 1 ≤ p.N (φ (m + m₀)) := by linarith [hp.1 (φ (m + m₀))]
      have hN0 : 0 < p.N (φ (m + m₀)) := by linarith
      have hle := levKz_le hp (a := a) (r := r) hU'0 (hC1 _) (hok m).1
      show levKz p U' (Cf (φ (m + m₀))) (nseq (m + m₀)) (φ (m + m₀)) ≤ p.N (φ (m + m₀)) ^ ε
      refine hle.trans ?_
      have hexp : B * levv (nseq (m + m₀)) ≤ ε / 2 := by
        have := mul_le_mul_of_nonneg_left hm1 hB0.le
        rw [show B * (ε / (2 * B)) = ε / 2 by field_simp] at this
        exact this
      calc 150 * p.N (φ (m + m₀)) ^ (B * levv (nseq (m + m₀)))
          ≤ p.N (φ (m + m₀)) ^ (ε / 2) * p.N (φ (m + m₀)) ^ (ε / 2) := by
            gcongr
        _ = p.N (φ (m + m₀)) ^ ε := by rw [← Real.rpow_add hN0]; ring_nf
  exact ZoomSeq.contact_transfer hp ha hZ hCMP

end

end Submission.Obl.k4_row_parent_contact_candidates
