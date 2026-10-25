-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.ZoomMain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomRotFamily

/-!
# Normalization of the slope

Examples whose slope has value and first two derivatives bounded by a small negative power of
the scale yield examples with a normalized slope: zoom by `r = 16 δ ^ (-η₁)`, which divides
the derivatives of the slope by `r` and `r ^ 2`, then rotate about the vertical axis.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- Examples whose slope is `C²` with value and two derivatives at most `δ ^ (-η)` on the
whole line. -/
def WeakSmoothExamples (σ : ℝ) : Prop :=
  ∀ η d₀ : ℝ, 0 < η → 0 < d₀ → ∃ δ : ℝ, 0 < δ ∧ δ ≤ d₀ ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      ExtremalFamily σ η δ n x v Y ∧ ∃ (f : ℝ → ℝ) (P : Space → Space),
        (ContDiff ℝ 2 f ∧ ∀ z : ℝ, |f z| ≤ δ ^ (-η) ∧ |deriv f z| ≤ δ ^ (-η) ∧
          |deriv (deriv f) z| ≤ δ ^ (-η)) ∧ Grains σ δ (δ ^ (-η)) v Y f P

/-- Derivative of a slope composed with an affine change of the height. -/
theorem deriv_comp_affine {g : ℝ → ℝ} (hg : Differentiable ℝ g) (a r : ℝ) (t : ℝ) :
    deriv (fun s => g (a + s / r)) t = deriv g (a + t / r) / r := by
  have h1 : HasDerivAt (fun s => a + s / r) (1 / r) t := by
    simpa using ((hasDerivAt_id t).div_const r).const_add a
  have h2 : HasDerivAt (fun s => g (a + s / r)) (deriv g (a + t / r) * (1 / r)) t :=
    (hg (a + t / r)).hasDerivAt.comp t h1
  rw [h2.deriv]
  ring

theorem ExtremalFamily.mono_error {σ η η' δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηη' : η ≤ η')
    (h : ExtremalFamily σ η δ n x v Y) : ExtremalFamily σ η' δ n x v Y := by
  obtain ⟨hD, hS, hC, hV⟩ := h
  refine ⟨dense_restrict (a := 0) hδ hδ1 (by linarith) hD (fun i => subset_rfl) hD.2.2.2.2.1
    (by simp), strong_mono_error hδ hδ1 hηη' hS, hC, hV.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))⟩

/-- Small powers absorb constants. -/
theorem cut_le_one {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → C * δ ^ a ≤ 1 := by
  obtain ⟨d, hd, h⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff ha
    (show 0 < 1 / (|C| + 1) by positivity)
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have h1 := h δ hδ hδd
  have h2 : C ≤ |C| + 1 := by linarith [le_abs_self C]
  calc C * δ ^ a ≤ (|C| + 1) * δ ^ a := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ (|C| + 1) * (1 / (|C| + 1)) := by gcongr
    _ = 1 := by field_simp

theorem small_and {p q : ℝ → Prop} (hp : ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → p δ)
    (hq : ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → q δ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → p δ ∧ q δ := by
  obtain ⟨d₁, hd₁, h₁⟩ := hp
  obtain ⟨d₂, hd₂, h₂⟩ := hq
  exact ⟨min d₁ d₂, lt_min hd₁ hd₂, fun δ hδ hδd =>
    ⟨h₁ δ hδ (hδd.trans (min_le_left _ _)), h₂ δ hδ (hδd.trans (min_le_right _ _))⟩⟩

theorem small_mono {p q : ℝ → Prop} (hp : ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → p δ)
    (hpq : ∀ δ : ℝ, 0 < δ → p δ → q δ) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → q δ := by
  obtain ⟨d, hd, h⟩ := hp
  exact ⟨d, hd, fun δ hδ hδd => hpq δ hδ (h δ hδ hδd)⟩

/-- `κ ^ p δ ^ q` with `κ = δ ^ (-η₁)` is a single power of `δ`. -/
theorem kappa_mul {δ η₁ : ℝ} (hδ : 0 < δ) (p q : ℝ) :
    (δ ^ (-η₁)) ^ p * δ ^ q = δ ^ (q - η₁ * p) := by
  rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
  ring_nf

theorem Ng_le {r : ℝ} (hr : 1 ≤ r) : (Ng r : ℝ) ≤ (66 * r) ^ 3 := by
  unfold Ng
  push_cast
  have h1 : (⌈64 * r⌉₊ : ℝ) < 64 * r + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (⌈64 * r⌉₊ : ℝ) + 1 ≤ 66 * r := by linarith
  exact pow_le_pow_left₀ (by positivity) h2 3

theorem conflictConst_ge_one : 1 ≤ conflictConst := by unfold conflictConst; norm_num

theorem Kc_le {r : ℝ} (hr : 1 ≤ r) : (Kc r : ℝ) ≤ 2 * conflictConst * r ^ 4 := by
  unfold Kc
  push_cast
  have h1 : (⌊conflictConst * r ^ 4⌋₊ : ℝ) ≤ conflictConst * r ^ 4 :=
    Nat.floor_le (by have := conflictConst_ge_one; positivity)
  have h2 : 1 ≤ conflictConst * r ^ 4 := by
    have := conflictConst_ge_one
    have : 1 ≤ r ^ 4 := one_le_pow₀ hr
    nlinarith
  linarith

/-- The constant in the lower bound for the retention fraction. -/
def Bcon (N : ℕ) : ℝ := 768 * 66 ^ 3 * (2 * conflictConst) ^ (N + 2) * (N + 2)

theorem Bcon_pos (N : ℕ) : 0 < Bcon N := by
  unfold Bcon; have := conflictConst_ge_one; positivity

theorem tpar_ge {δ η₁ r : ℝ} (hδ : 0 < δ) (hr : 1 ≤ r) (N : ℕ) :
    δ ^ η₁ / (Bcon N * r ^ (4 * N + 10)) ≤ tpar δ η₁ r N := by
  have hr0 : 0 < r := by linarith
  have hCc := conflictConst_ge_one
  unfold tpar
  have hden : (768 * (Ng r : ℝ) * Kc r * (Kc r : ℝ) ^ (N + 1) * (N + 2)) ≤
      Bcon N * r ^ (4 * N + 11) := by
    have hK := Kc_le hr
    have hK0 : (0 : ℝ) ≤ Kc r := Nat.cast_nonneg _
    have hKpow : (Kc r : ℝ) * (Kc r : ℝ) ^ (N + 1) ≤ (2 * conflictConst * r ^ 4) ^ (N + 2) := by
      rw [← pow_succ']
      exact pow_le_pow_left₀ hK0 hK _
    calc 768 * (Ng r : ℝ) * Kc r * (Kc r : ℝ) ^ (N + 1) * (N + 2)
        = 768 * (Ng r : ℝ) * ((Kc r : ℝ) * (Kc r : ℝ) ^ (N + 1)) * (N + 2) := by ring
      _ ≤ 768 * (66 * r) ^ 3 * (2 * conflictConst * r ^ 4) ^ (N + 2) * (N + 2) := by
          gcongr
          · exact Ng_le hr
      _ = Bcon N * r ^ (4 * N + 11) := by
          unfold Bcon
          have hpw : r ^ 3 * r ^ (4 * (N + 2)) = r ^ (4 * N + 11) := by
            rw [← pow_add]; congr 1; ring
          rw [mul_pow, mul_pow, ← pow_mul, ← hpw]
          ring
  have hpos : 0 < 768 * (Ng r : ℝ) * Kc r * (Kc r : ℝ) ^ (N + 1) * (N + 2) := by
    unfold Ng Kc; positivity
  calc δ ^ η₁ / (Bcon N * r ^ (4 * N + 10))
      = δ ^ η₁ * r / (Bcon N * r ^ (4 * N + 11)) := by
        rw [show r ^ (4 * N + 11) = r ^ (4 * N + 10) * r by rw [← pow_succ], ← mul_assoc,
          mul_div_mul_right _ _ hr0.ne']
    _ ≤ δ ^ η₁ * r / (768 * (Ng r : ℝ) * Kc r * (Kc r : ℝ) ^ (N + 1) * (N + 2)) := by
        apply div_le_div_of_nonneg_left (by positivity) hpos hden

/-- A smaller power of `δ` eventually beats a larger one, with any constants. -/
theorem pow_cmp {A B a b : ℝ} (hB : 0 < B) (hab : 0 < a - b) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → A * δ ^ a ≤ B * δ ^ b := by
  obtain ⟨d, hd, h⟩ := cut_le_one hab (A / B)
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have h1 := h δ hδ hδd
  have h2 : A * δ ^ (a - b) ≤ B := by
    have := mul_le_mul_of_nonneg_left h1 hB.le
    rwa [mul_one, ← mul_assoc, mul_div_cancel₀ _ hB.ne'] at this
  calc A * δ ^ a = A * δ ^ (a - b) * δ ^ b := by
        rw [mul_assoc, ← Real.rpow_add hδ]; ring_nf
    _ ≤ B * δ ^ b := mul_le_mul_of_nonneg_right h2 (by positivity)

theorem rd_eq {δ η₁ : ℝ} (hδ : 0 < δ) : 16 * δ ^ (-η₁) * δ = 16 * δ ^ (1 - η₁) := by
  rw [mul_assoc, show δ ^ (1 - η₁) = δ ^ (-η₁) * δ ^ (1 : ℝ) by
    rw [← Real.rpow_add hδ]; ring_nf, Real.rpow_one]

theorem rdp_eq {δ η₁ : ℝ} (hδ : 0 < δ) (p : ℝ) :
    (16 * δ ^ (-η₁) * δ) ^ p = 16 ^ p * δ ^ ((1 - η₁) * p) := by
  rw [rd_eq hδ, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hδ.le]

theorem rk_eq {δ η₁ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    (16 * δ ^ (-η₁)) ^ k = 16 ^ k * δ ^ (-η₁ * k) := by
  rw [mul_pow, ← Real.rpow_natCast (δ ^ (-η₁)), ← Real.rpow_mul hδ.le]

/-- All parameter conditions hold for small `δ`, with `r = 16 δ ^ (-η₁)`. -/
theorem params_small {η η₁ σ d₀ : ℝ} {N : ℕ} (hη₁ : 0 < η₁) (hd₀ : 0 < d₀)
    (hσ0 : 0 ≤ σ) (hsmall : η₁ * (4 * N + 15 + η) < η) (hη₁q : η₁ < 1 / 4) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      δ ≤ 1 / (131072 * (16 * δ ^ (-η₁))) ∧ 16 * δ ^ (-η₁) * δ ≤ 1 / 8 ∧
      δ ^ (-η₁) * (16 * δ ^ (-η₁) * δ) ^ (η / 4) ≤ 1 / 16384 ∧
      δ ^ (-η₁) * δ ≤ 1 / (131072 * (16 * δ ^ (-η₁))) ∧
      8 * δ ^ (-η₁) ≤ (16 * δ ^ (-η₁) * δ) ^ (-η) ∧
      δ ^ (-η₁) * (16 * δ ^ (-η₁) * δ) ^ (-(η / 4)) ≤ (16 * δ ^ (-η₁) * δ) ^ (-η) ∧
      64 * (432 * 512) * (16 * δ ^ (-η₁)) ^ 2 * δ ^ (-η₁) ≤
        (16 * δ ^ (-η₁) * δ) ^ (-η) * tpar δ η₁ (16 * δ ^ (-η₁)) N ∧
      (16 * δ ^ (-η₁) * δ) ^ η ≤ 384 * tpar δ η₁ (16 * δ ^ (-η₁)) N ∧
      (16 * δ ^ (-η₁)) ^ 3 * δ ^ (σ - η₁) ≤ (16 * δ ^ (-η₁) * δ) ^ (σ - η) ∧
      16 * δ ^ (-η₁) * δ ≤ d₀ ∧ 16 * δ ^ (-η₁) * δ ≤ 1 / 100 := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- (1)
  have c1 := pow_cmp (A := 2097152) (B := 1) (a := 1 - η₁) (b := 0) one_pos (by linarith)
  have c2 := pow_cmp (A := 16) (B := 1 / 8) (a := 1 - η₁) (b := 0) (by norm_num) (by linarith)
  have c3 := pow_cmp (A := 16 ^ (η / 4)) (B := 1 / 16384) (a := (1 - η₁) * (η / 4) - η₁)
    (b := 0) (by norm_num) (by nlinarith)
  have c4 := pow_cmp (A := 2097152) (B := 1) (a := 1 - 2 * η₁) (b := 0) one_pos (by linarith)
  have c5 := pow_cmp (A := 8) (B := (16 : ℝ) ^ (-η)) (a := -η₁) (b := (1 - η₁) * (-η))
    (by positivity) (by nlinarith)
  have c6 := pow_cmp (A := (16 : ℝ) ^ (-(η / 4))) (B := (16 : ℝ) ^ (-η))
    (a := -η₁ + (1 - η₁) * (-(η / 4))) (b := (1 - η₁) * (-η)) (by positivity) (by nlinarith)
  have c7 := pow_cmp (A := 64 * (432 * 512) * 16 ^ (4 * N + 12) * Bcon N)
    (B := (16 : ℝ) ^ (-η)) (a := -η₁ * (4 * N + 13 : ℕ)) (b := (1 - η₁) * (-η) + η₁)
    (by positivity) (by push_cast; nlinarith)
  have c8 := pow_cmp (A := 16 ^ η * Bcon N * 16 ^ (4 * N + 10)) (B := 384)
    (a := (1 - η₁) * η + -η₁ * (4 * N + 10 : ℕ)) (b := η₁) (by norm_num)
    (by push_cast; nlinarith)
  have c9 := pow_cmp (A := 4096) (B := (16 : ℝ) ^ (σ - η)) (a := σ - 4 * η₁)
    (b := (1 - η₁) * (σ - η)) (by positivity) (by nlinarith)
  have c10 := pow_cmp (A := 16) (B := d₀) (a := 1 - η₁) (b := 0) hd₀ (by linarith)
  have c11 := pow_cmp (A := 16) (B := 1 / 100) (a := 1 - η₁) (b := 0) (by norm_num)
    (by linarith)
  obtain ⟨d, hd, h⟩ := small_and c1 (small_and c2 (small_and c3 (small_and c4 (small_and c5
    (small_and c6 (small_and c7 (small_and c8 (small_and c9 (small_and c10 c11)))))))))
  refine ⟨min d 1, lt_min hd one_pos, fun δ hδ hδd => ?_⟩
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_right _ _)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h δ hδ (hδd.trans (min_le_left _ _))
  simp only [Real.rpow_zero, mul_one] at h1 h2 h3 h4 h10 h11
  have hκ : 0 < δ ^ (-η₁) := Real.rpow_pos_of_pos hδ _
  have hr : (1 : ℝ) ≤ 16 * δ ^ (-η₁) := by
    have : 1 ≤ δ ^ (-η₁) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
    linarith
  have hκδ : δ ^ (-η₁) * δ = δ ^ (1 - η₁) := by
    rw [show δ ^ (1 - η₁) = δ ^ (-η₁) * δ ^ (1 : ℝ) by rw [← Real.rpow_add hδ]; ring_nf,
      Real.rpow_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    calc δ * (131072 * (16 * δ ^ (-η₁))) = 2097152 * (δ ^ (-η₁) * δ) := by ring
      _ = 2097152 * δ ^ (1 - η₁) := by rw [hκδ]
      _ ≤ 1 := h1
  · rw [rd_eq hδ]; exact h2
  · rw [rdp_eq hδ, mul_left_comm, ← Real.rpow_add hδ]
    convert h3 using 3
    ring
  · rw [le_div_iff₀ (by positivity)]
    calc δ ^ (-η₁) * δ * (131072 * (16 * δ ^ (-η₁))) =
        2097152 * (δ ^ (-η₁) * δ ^ (-η₁) * δ) := by ring
      _ = 2097152 * δ ^ (1 - 2 * η₁) := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add_one hδ.ne']; ring_nf
      _ ≤ 1 := h4
  · rw [rdp_eq hδ]; exact h5
  · rw [rdp_eq hδ, rdp_eq hδ, mul_left_comm, ← Real.rpow_add hδ]; exact h6
  · have hT := tpar_ge (η₁ := η₁) hδ hr N
    set r := 16 * δ ^ (-η₁)
    have hB := Bcon_pos N
    have hrpos : 0 < r := by linarith
    have hδpow : δ ^ (-η₁ * ((4 * N + 12 : ℕ) : ℝ)) * δ ^ (-η₁) =
        δ ^ (-η₁ * ((4 * N + 13 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hδ]; push_cast; ring_nf
    have hkey : 64 * (432 * 512) * r ^ 2 * δ ^ (-η₁) * (Bcon N * r ^ (4 * N + 10)) ≤
        (r * δ) ^ (-η) * δ ^ η₁ := by
      calc 64 * (432 * 512) * r ^ 2 * δ ^ (-η₁) * (Bcon N * r ^ (4 * N + 10))
          = 64 * (432 * 512) * Bcon N * (r ^ (4 * N + 12) * δ ^ (-η₁)) := by
            rw [show r ^ (4 * N + 12) = r ^ 2 * r ^ (4 * N + 10) by rw [← pow_add]; ring_nf]
            ring
        _ = 64 * (432 * 512) * Bcon N * (16 ^ (4 * N + 12) *
              (δ ^ (-η₁ * ((4 * N + 12 : ℕ) : ℝ)) * δ ^ (-η₁))) := by
            rw [rk_eq hδ]; ring
        _ = (64 * (432 * 512) * 16 ^ (4 * N + 12) * Bcon N) *
              δ ^ (-η₁ * ((4 * N + 13 : ℕ) : ℝ)) := by rw [hδpow]; ring
        _ ≤ 16 ^ (-η) * δ ^ ((1 - η₁) * -η + η₁) := h7
        _ = (r * δ) ^ (-η) * δ ^ η₁ := by rw [rdp_eq hδ, Real.rpow_add hδ]; ring
    have hrδpos : 0 < (r * δ) ^ (-η) := Real.rpow_pos_of_pos (by positivity) _
    have hden : 0 < Bcon N * r ^ (4 * N + 10) := by positivity
    calc 64 * (432 * 512) * r ^ 2 * δ ^ (-η₁)
        ≤ (r * δ) ^ (-η) * δ ^ η₁ / (Bcon N * r ^ (4 * N + 10)) := by
          rw [le_div_iff₀ hden]; exact hkey
      _ = (r * δ) ^ (-η) * (δ ^ η₁ / (Bcon N * r ^ (4 * N + 10))) := by ring
      _ ≤ (r * δ) ^ (-η) * tpar δ η₁ r N := mul_le_mul_of_nonneg_left hT hrδpos.le
  · have hT := tpar_ge (η₁ := η₁) hδ hr N
    set r := 16 * δ ^ (-η₁)
    have hB := Bcon_pos N
    have hrpos : 0 < r := by linarith
    have hden : 0 < Bcon N * r ^ (4 * N + 10) := by positivity
    have hkey : (r * δ) ^ η * (Bcon N * r ^ (4 * N + 10)) ≤ 384 * δ ^ η₁ := by
      calc (r * δ) ^ η * (Bcon N * r ^ (4 * N + 10))
          = 16 ^ η * δ ^ ((1 - η₁) * η) * (Bcon N * (16 ^ (4 * N + 10) *
              δ ^ (-η₁ * ((4 * N + 10 : ℕ) : ℝ)))) := by rw [rdp_eq hδ, rk_eq hδ]
        _ = (16 ^ η * Bcon N * 16 ^ (4 * N + 10)) *
              δ ^ ((1 - η₁) * η + -η₁ * ((4 * N + 10 : ℕ) : ℝ)) := by
            rw [Real.rpow_add hδ]; ring
        _ ≤ 384 * δ ^ η₁ := h8
    calc (r * δ) ^ η ≤ 384 * δ ^ η₁ / (Bcon N * r ^ (4 * N + 10)) := by
          rw [le_div_iff₀ hden]; exact hkey
      _ = 384 * (δ ^ η₁ / (Bcon N * r ^ (4 * N + 10))) := by ring
      _ ≤ 384 * tpar δ η₁ r N := by gcongr
  · rw [rk_eq hδ, rdp_eq hδ]
    calc (16 : ℝ) ^ 3 * δ ^ (-η₁ * ((3 : ℕ) : ℝ)) * δ ^ (σ - η₁) = 4096 * δ ^ (σ - 4 * η₁) := by
          rw [mul_assoc, ← Real.rpow_add hδ]; push_cast; ring_nf
      _ ≤ 16 ^ (σ - η) * δ ^ ((1 - η₁) * (σ - η)) := h9
  · rw [rd_eq hδ]; exact h10
  · rw [rd_eq hδ]; exact h11

/-- **Normalization.** Examples with a slope whose value and first two derivatives are bounded
by a small negative power of the scale yield examples with a normalized `C²` slope. -/
theorem normalize {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hW : WeakSmoothExamples σ) :
    SmoothExamples σ := by
  intro η d₀ hη hd₀
  set η' := min η (1 / 2)
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'h : η' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨N, hN, hgap⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_net_size
    (η := η' / 4) (by positivity)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set η₁ := η' / (8 * N + 40)
  have hη₁ : 0 < η₁ := by positivity
  have hsmall : η₁ * (4 * N + 15 + η') < η' := by
    simp only [η₁]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hη₁q : η₁ < 1 / 4 := by
    simp only [η₁]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨d₁, hd₁, hpar⟩ := params_small (η := η') (N := N) hη₁ hd₀ hσ0 hsmall hη₁q
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hfam, g, P, ⟨hg, hgb⟩, hgr⟩ := hW η₁ d₁ hη₁ hd₁
  obtain ⟨p1, p2, p4, p4', p5, p5', p7, p8, p9, p10, p11⟩ := hpar δ hδ hδd
  have hδ1 : δ ≤ 1 := by linarith
  have hκ1 : 1 ≤ δ ^ (-η₁) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  set r := 16 * δ ^ (-η₁)
  have hr : 16 ≤ r := by simp only [r]; linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨c, m, x', v', Y', hfam', hgr'⟩ := zoom_family (η := η') (N := N) hδ hδ100 hr
    hη'0 hη₁ hN hgap hfam hgr p1 p2 p4 p4' p5 p5' p7 p8 p9
  -- the zoomed slope
  set gz : ℝ → ℝ := fun t => g (c 2 + t / r)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgd' : Differentiable ℝ (deriv g) := differentiable_deriv_of_contDiff_two hg
  have hgz : ContDiff ℝ 2 gz := hg.comp (contDiff_const.add (contDiff_id.div_const r))
  have hD : deriv gz = fun t => deriv g (c 2 + t / r) / r :=
    funext fun t => deriv_comp_affine hgd (c 2) r t
  have hd1 : ∀ t, |deriv gz t| ≤ 1 / 16 := by
    intro t
    rw [hD, abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    have := (hgb (c 2 + t / r)).2.1
    simp only [r]; linarith
  have hd2 : ∀ t, |deriv (deriv gz) t| ≤ 1 / 16 := by
    intro t
    have hDD : deriv (deriv gz) t = deriv (deriv g) (c 2 + t / r) / r / r := by
      rw [hD]
      have := deriv_comp_affine hgd' (c 2) r t
      rw [deriv_div_const, this]
    rw [hDD, abs_div, abs_div, abs_of_pos hr0, div_div, div_le_iff₀ (by positivity)]
    have h1 := (hgb (c 2 + t / r)).2.2
    have h2 : δ ^ (-η₁) ≤ 1 / 16 * (r * r) := by
      simp only [r]; nlinarith
    linarith
  obtain ⟨x'', v'', Y'', P'', hfam'', hnorm, hgr''⟩ := rotate_family (K := δ ^ (-η₁))
    (mul_pos hr0 hδ) (by linarith) hσ1 hfam' hgr' hgz hd1 hd2
  have hrδ1 : r * δ ≤ 1 := by linarith
  have hconst : 2 * δ ^ (-η₁) ≤ (r * δ) ^ (-η) := by
    have h1 : (r * δ) ^ (-η') ≤ (r * δ) ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_ge (mul_pos hr0 hδ) hrδ1 (by linarith)
    have h2 : 0 ≤ δ ^ (-η₁) := by linarith
    linarith
  refine ⟨r * δ, mul_pos hr0 hδ, p10, p11, m, x'', v'', Y'',
    hfam''.mono_error (mul_pos hr0 hδ) hrδ1 hη'η, rotSlope gz, P'', hnorm,
    hgr''.mono_constant (mul_pos hr0 hδ) hconst⟩

end

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
