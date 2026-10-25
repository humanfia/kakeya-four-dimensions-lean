-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/FrameCompat.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/FrameCompat.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.CommonFrames
import Submission.Lib.K4VelocityStrips.StripIntersections

/-!
# Witness compatibility lists of the common frames

The supplied paper's Lemma 3.5: "`A'` determines a list of only `K₀` possible `D`'s on
retained pairs".  A witness chart `(c', u', Q')` enumerates the codes whose rounded normal
is within three mesh steps of its own normal (either sign), and, in the axes of each such
code, the position and velocity codes within `Kb` steps of its own rounded center and
velocity.  This list `codeNbhd` has at most `2 · 49 · (2Kb+1)^4` codes.

`chartCode_mem_codeNbhd`: if a trajectory is confined in a source chart and in a witness
chart (on their own old blocks inside one coarse block), both charts satisfy the scale
hypotheses `2ρ r₁ ≤ K S₁`, `ρ r₂ + 6g (2ρ r₁) ≤ K S₂`, and the normals are not separated,
`|wedge(ν, ν')| ≤ g`, then the source's code lies in the witness's list.  Pairs with
separated normals are the normal exception, bounded separately.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open Matrix Submission.Lib.K4FinitePlankAtlases Submission.Lib.K4VelocityStrips

/-- Integer box `[a - K, a + K]`. -/
def intBox (a : ℤ) (K : ℕ) : Finset ℤ := Finset.Icc (a - K) (a + K)

theorem intBox_card (a : ℤ) (K : ℕ) : (intBox a K).card = 2 * K + 1 := by
  unfold intBox
  rw [Int.card_Icc]
  omega

/-- The rounded position and velocity of a chart in the axes of a normal code. -/
noncomputable def roundedPV (g S₁ S₂ q₁ tm : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (kn : ℤ × ℤ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  let e := axisT g kn
  let n := axisN g kn
  let p := c + tm • u
  ((⌊inner ℝ p e / S₁⌋, ⌊inner ℝ p n / S₂⌋),
    (⌊inner ℝ u e / (S₁ / q₁)⌋, ⌊inner ℝ u n / (S₂ / q₁)⌋))

/-- The codes compatible with a witness chart. -/
noncomputable def codeNbhd (g S₁ S₂ q₁ tm : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (Kb : ℕ) : Finset FrameCode := by
  classical
  exact (({1, -1} : Finset ℝ) ×ˢ (Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3)).biUnion
    (fun σδ =>
      let kn : ℤ × ℤ := roundCode g (σδ.1 • nrm Q) + σδ.2
      let pv := roundedPV g S₁ S₂ q₁ tm c u kn
      ((intBox pv.1.1 Kb ×ˢ intBox pv.1.2 Kb) ×ˢ (intBox pv.2.1 Kb ×ˢ intBox pv.2.2 Kb)).image
        (fun x => ({ kn := kn, kp := x.1, kv := x.2 } : FrameCode)))

theorem codeNbhd_card_le (g S₁ S₂ q₁ tm : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (Kb : ℕ) :
    (codeNbhd g S₁ S₂ q₁ tm c u Q Kb).card ≤ 98 * (2 * Kb + 1) ^ 4 := by
  classical
  unfold codeNbhd
  refine (Finset.card_biUnion_le).trans ?_
  have hterm : ∀ σδ ∈ (({1, -1} : Finset ℝ) ×ˢ (Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3)),
      (let kn : ℤ × ℤ := roundCode g (σδ.1 • nrm Q) + σδ.2
       let pv := roundedPV g S₁ S₂ q₁ tm c u kn
       ((intBox pv.1.1 Kb ×ˢ intBox pv.1.2 Kb) ×ˢ (intBox pv.2.1 Kb ×ˢ intBox pv.2.2 Kb)).image
        (fun x => ({ kn := kn, kp := x.1, kv := x.2 } : FrameCode))).card ≤ (2 * Kb + 1) ^ 4 := by
    intro σδ _
    refine Finset.card_image_le.trans ?_
    simp only [Finset.card_product, intBox_card]
    ring_nf
    exact le_rfl
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  have hc : (({1, -1} : Finset ℝ) ×ˢ (Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3)).card ≤ 98 := by
    rw [Finset.card_product, Finset.card_product]
    have h1 : ({1, -1} : Finset ℝ).card ≤ 2 := Finset.card_le_two
    have h2 : (Finset.Icc (-3 : ℤ) 3).card = 7 := by simp
    rw [h2]
    nlinarith
  exact Nat.mul_le_mul_right _ hc

/-- Floors of two reals at most `D` apart differ by at most `D + 1`. -/
theorem floor_diff_le {a b D : ℝ} (h : |a - b| ≤ D) : |((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ)| ≤ D + 1 := by
  have h1 := Int.floor_le a
  have h2 := Int.lt_floor_add_one a
  have h3 := Int.floor_le b
  have h4 := Int.lt_floor_add_one b
  rw [abs_le] at h ⊢
  push_cast
  constructor <;> linarith [h.1, h.2]

theorem mem_intBox_of {k a : ℤ} {K : ℕ} {D : ℝ} (hD : D + 1 ≤ K)
    (h : |((k - a : ℤ) : ℝ)| ≤ D + 1) : k ∈ intBox a K := by
  unfold intBox
  rw [Finset.mem_Icc]
  have h' : |((k - a : ℤ) : ℝ)| ≤ (K : ℝ) := h.trans hD
  rw [abs_le] at h'
  have i1 : k - a ≤ (K : ℤ) := by exact_mod_cast h'.2
  have i2 : -(K : ℤ) ≤ k - a := by exact_mod_cast h'.1
  constructor <;> omega

theorem floor_mem_intBox {K : ℝ} {Kb : ℕ} (hKb : 2 * K + 1 ≤ (Kb : ℝ)) {a b B : ℝ}
    (hB : 0 < B) (hab : |a - b| ≤ 2 * K * B) : (⌊a / B⌋ : ℤ) ∈ intBox ⌊b / B⌋ Kb := by
  apply mem_intBox_of (D := 2 * K) hKb
  apply floor_diff_le
  rw [← sub_div, abs_div, abs_of_pos hB, div_le_iff₀ hB]
  linarith

theorem abs_sub_le_of_scaled {q K B a b : ℝ} (hq : 0 < q) (ha : |a| * q ≤ K * B)
    (hb : |b| * q ≤ K * B) : |a - b| ≤ 2 * K * (B / q) := by
  have h1 : |a - b| * q ≤ (|a| + |b|) * q := mul_le_mul_of_nonneg_right (abs_sub a b) hq.le
  rw [add_mul] at h1
  rw [mul_div_assoc', le_div_iff₀ hq]
  linarith

/-- The rounded normals of two charts whose unit normals are close up to sign. -/
theorem roundCode_close {g : ℝ} (hg : 0 < g) {ν ν' : EuclideanSpace ℝ (Fin 2)}
    (h : ‖ν - ν'‖ ≤ 2 * g) :
    roundCode g ν - roundCode g ν' ∈ Finset.Icc (-3 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3 := by
  have hc : ∀ i : Fin 2, |ν i / g - ν' i / g| ≤ 2 := by
    intro i
    have hi : |ν i - ν' i| ≤ 2 * g := by
      have := abs_coord_le_norm (ν - ν') i
      simp only [PiLp.sub_apply] at this
      linarith
    rw [← sub_div, abs_div, abs_of_pos hg, div_le_iff₀ hg]
    linarith
  have hint : ∀ i : Fin 2, (⌊ν i / g⌋ - ⌊ν' i / g⌋ : ℤ) ∈ Finset.Icc (-3 : ℤ) 3 := by
    intro i
    have h := floor_diff_le (hc i)
    rw [Finset.mem_Icc]
    rw [abs_le] at h
    constructor
    · have : ((-3 : ℤ) : ℝ) ≤ ((⌊ν i / g⌋ - ⌊ν' i / g⌋ : ℤ) : ℝ) := by push_cast at h ⊢; linarith
      exact_mod_cast this
    · have : ((⌊ν i / g⌋ - ⌊ν' i / g⌋ : ℤ) : ℝ) ≤ ((3 : ℤ) : ℝ) := by push_cast at h ⊢; linarith
      exact_mod_cast this
  rw [Finset.mem_product]
  exact ⟨hint 0, hint 1⟩

/-- Normals not separated by more than `g` are within `2g` of each other up to sign. -/
theorem exists_sign_close {ν ν' : EuclideanSpace ℝ (Fin 2)} (hν : ‖ν‖ = 1) (hν' : ‖ν'‖ = 1)
    {g : ℝ} (hw : |stripWedge ν ν'| ≤ g) :
    ∃ σ ∈ ({1, -1} : Finset ℝ), ‖ν - σ • ν'‖ ≤ 2 * g := by
  by_cases hs : 0 ≤ inner ℝ ν ν'
  · refine ⟨1, by simp, ?_⟩
    rw [one_smul]
    exact (unit_normals_dist_le_wedge hν hν' hs).trans (by linarith)
  · refine ⟨-1, by simp, ?_⟩
    have hm : ‖(-1 : ℝ) • ν'‖ = 1 := by rw [norm_smul]; simp [hν']
    have hs' : 0 ≤ inner ℝ ν ((-1 : ℝ) • ν') := by
      rw [inner_smul_right]; linarith
    have hwd : stripWedge ν ((-1 : ℝ) • ν') = -stripWedge ν ν' := by
      simp [stripWedge]; ring
    refine (unit_normals_dist_le_wedge hν hm hs').trans ?_
    rw [hwd, abs_neg]
    linarith

/-- The extents of one chart in the axes of a code close to its normal. -/
theorem chart_extents {S₁ S₂ q₀ q₁ tm κ₀ K t₁ ε : ℝ} (hq₀ : 0 < q₀)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {l : ℕ × (Fin 6 → ℝ)}
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u)‖ ≤ κ₀)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (y l (t₁ + q₀) - c - (t₁ + q₀) • u)‖ ≤ κ₀)
    (htm₁ : |tm - t₁| ≤ q₁)
    {e n : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hnν : ‖n - nrm Q‖ ≤ ε)
    (hq : 0 ≤ q₁)
    (hA₁ : 2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q ≤ K * S₁)
    (hA₂ : κ₀ * (1 + 2 * q₁ / q₀) * r₂ Q + ε * (2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q) ≤
      K * S₂) :
    |inner ℝ (y l tm - (c + tm • u)) e| ≤ K * S₁ ∧
    |inner ℝ (y l tm - (c + tm • u)) n| ≤ K * S₂ ∧
    |inner ℝ (v l - u) e| * q₁ ≤ K * S₁ ∧
    |inner ℝ (v l - u) n| * q₁ ≤ K * S₂ := by
  obtain ⟨⟨gm, hgm, hgmeq⟩, ⟨gv, hgv, hgveq⟩⟩ := chart_extrapolation hQ hq₀ h₁ h₂ tm
  have hκ₀ : 0 ≤ κ₀ := (norm_nonneg _).trans h₁
  set ρ := κ₀ * (1 + 2 * q₁ / q₀) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hgmρ : ‖gm‖ ≤ ρ := hgm.trans (by rw [hρ]; gcongr)
  have hgvρ : ‖gv‖ * q₁ ≤ ρ := by
    have h1 : ‖gv‖ * q₁ ≤ 2 * κ₀ / q₀ * q₁ := mul_le_mul_of_nonneg_right hgv hq
    have h2 : 2 * κ₀ / q₀ * q₁ ≤ ρ := by
      rw [hρ]
      have e : 2 * κ₀ / q₀ * q₁ = κ₀ * (2 * q₁ / q₀) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ hκ₀
      linarith
    linarith
  have hr₁ := r₁_nonneg Q
  have hr₂ := r₂_nonneg Q
  have hε : 0 ≤ ε := (norm_nonneg _).trans hnν
  have hpos : y l tm - (c + tm • u) = y l tm - c - tm • u := by abel
  have hm := image_coords hQ he hn gm
  have hv := image_coords hQ he hn gv
  rw [← hgmeq] at hm
  rw [← hgveq] at hv
  rw [hpos]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hm.1.trans (le_trans ?_ hA₁)
    gcongr
  · refine hm.2.trans (le_trans ?_ hA₂)
    have a1 : ‖gm‖ * r₂ Q ≤ ρ * r₂ Q := by gcongr
    have a2 : ‖n - nrm Q‖ * (2 * ‖gm‖ * r₁ Q) ≤ ε * (2 * ρ * r₁ Q) := by gcongr
    linarith
  · have h := mul_le_mul_of_nonneg_right hv.1 hq
    refine h.trans (le_trans ?_ hA₁)
    have e : 2 * ‖gv‖ * r₁ Q * q₁ = 2 * (‖gv‖ * q₁) * r₁ Q := by ring
    rw [e]
    gcongr
  · have h := mul_le_mul_of_nonneg_right hv.2 hq
    refine h.trans (le_trans ?_ hA₂)
    have e : (‖gv‖ * r₂ Q + ‖n - nrm Q‖ * (2 * ‖gv‖ * r₁ Q)) * q₁ =
        (‖gv‖ * q₁) * r₂ Q + ‖n - nrm Q‖ * (2 * (‖gv‖ * q₁) * r₁ Q) := by ring
    rw [e]
    have a1 : (‖gv‖ * q₁) * r₂ Q ≤ ρ * r₂ Q := by gcongr
    have a2 : ‖n - nrm Q‖ * (2 * (‖gv‖ * q₁) * r₁ Q) ≤ ε * (2 * ρ * r₁ Q) := by gcongr
    linarith

set_option maxHeartbeats 1000000 in
/-- **Compatibility.**  A trajectory confined in a source chart and in a witness chart, on
their old blocks inside one coarse block, with non-separated normals: the source's code
lies in the witness's list. -/
theorem chartCode_mem_codeNbhd {g S₁ S₂ q₀ q₁ tm κ₀ K t₁ t₁' : ℝ} (hg : 0 < g)
    (hg8 : g ≤ 1 / 8) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    {c u c' u' : EuclideanSpace ℝ (Fin 2)} {Q Q' : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.det ≠ 0) (hQ' : Q'.det ≠ 0) {l : ℕ × (Fin 6 → ℝ)}
    (h₁ : ‖Matrix.toEuclideanLin Q⁻¹ (y l t₁ - c - t₁ • u)‖ ≤ κ₀)
    (h₂ : ‖Matrix.toEuclideanLin Q⁻¹ (y l (t₁ + q₀) - c - (t₁ + q₀) • u)‖ ≤ κ₀)
    (h₁' : ‖Matrix.toEuclideanLin Q'⁻¹ (y l t₁' - c' - t₁' • u')‖ ≤ κ₀)
    (h₂' : ‖Matrix.toEuclideanLin Q'⁻¹ (y l (t₁' + q₀) - c' - (t₁' + q₀) • u')‖ ≤ κ₀)
    (htm : |tm - t₁| ≤ q₁) (htm' : |tm - t₁'| ≤ q₁)
    (hA₁ : 2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q ≤ K * S₁)
    (hA₂ : κ₀ * (1 + 2 * q₁ / q₀) * r₂ Q + 6 * g * (2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q) ≤
      K * S₂)
    (hA₁' : 2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q' ≤ K * S₁)
    (hA₂' : κ₀ * (1 + 2 * q₁ / q₀) * r₂ Q' + 6 * g * (2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q') ≤
      K * S₂)
    (hwedge : |stripWedge (nrm Q) (nrm Q')| ≤ g)
    {Kb : ℕ} (hKb : 2 * K + 1 ≤ Kb) :
    chartCode g S₁ S₂ q₁ tm c u Q ∈ codeNbhd g S₁ S₂ q₁ tm c' u' Q' Kb := by
  classical
  have hν := norm_nrm hQ
  have hν' := norm_nrm hQ'
  obtain ⟨σ, hσ, hσc⟩ := exists_sign_close hν hν' hwedge
  have hσ1 : |σ| = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl <;> simp
  have hδ := roundCode_close hg hσc
  obtain ⟨he, hn, hen⟩ := axes_orthonormal (codeVec_ne_zero hg hg8 hν)
  have hnν : ‖axisN g (roundCode g (nrm Q)) - nrm Q‖ ≤ 4 * g := axisN_err hg hg8 hν
  set kn := roundCode g (nrm Q) with hkn
  set e := axisT g kn with he_def
  set n := axisN g kn with hn_def
  have hnν' : ‖n - nrm Q'‖ ≤ 6 * g ∨ ‖n - (-1 : ℝ) • nrm Q'‖ ≤ 6 * g := by
    have hsplit : n - σ • nrm Q' = (n - nrm Q) + (nrm Q - σ • nrm Q') := by abel
    have hb : ‖n - σ • nrm Q'‖ ≤ 6 * g := by
      rw [hsplit]; refine (norm_add_le _ _).trans ?_; linarith
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with rfl | rfl
    · left; simpa using hb
    · right; exact hb
  -- witness extents in the axes (e, n), using the witness normal up to sign
  have hwit : |inner ℝ (y l tm - (c' + tm • u')) e| ≤ K * S₁ ∧
      |inner ℝ (y l tm - (c' + tm • u')) n| ≤ K * S₂ ∧
      |inner ℝ (v l - u') e| * q₁ ≤ K * S₁ ∧
      |inner ℝ (v l - u') n| * q₁ ≤ K * S₂ := by
    rcases hnν' with h6 | h6
    · exact chart_extents hq₀ hQ' h₁' h₂' htm' he hn h6 hq₁.le hA₁' hA₂'
    · -- replace the witness normal by its negative: the extents only see |inner|
      have hn' : ‖(-1 : ℝ) • n‖ = 1 := by rw [norm_smul]; simp [hn]
      have h6' : ‖(-1 : ℝ) • n - nrm Q'‖ ≤ 6 * g := by
        have : (-1 : ℝ) • n - nrm Q' = (-1 : ℝ) • (n - (-1 : ℝ) • nrm Q') := by module
        rw [this, norm_smul]; simpa using h6
      obtain ⟨a1, a2, a3, a4⟩ := chart_extents hq₀ hQ' h₁' h₂' htm' he hn' h6' hq₁.le hA₁' hA₂'
      simp only [inner_smul_right, abs_mul, abs_neg, abs_one, one_mul] at a2 a4
      exact ⟨a1, a2, a3, a4⟩
  have hA₂4 : κ₀ * (1 + 2 * q₁ / q₀) * r₂ Q + 4 * g * (2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q) ≤
      K * S₂ := by
    have h0 : 0 ≤ 2 * (κ₀ * (1 + 2 * q₁ / q₀)) * r₁ Q := by
      have := r₁_nonneg Q
      have hk : 0 ≤ κ₀ := (norm_nonneg _).trans h₁
      positivity
    have := mul_le_mul_of_nonneg_right (show 4 * g ≤ 6 * g by linarith) h0
    linarith
  have hsrc := chart_extents hq₀ hQ h₁ h₂ htm he hn hnν hq₁.le hA₁ hA₂4
  obtain ⟨s1, s2, s3, s4⟩ := hsrc
  obtain ⟨w1, w2, w3, w4⟩ := hwit
  -- differences of the old centers and velocities
  have dP : ∀ f : EuclideanSpace ℝ (Fin 2),
      inner ℝ (c + tm • u) f - inner ℝ (c' + tm • u') f =
        inner ℝ (y l tm - (c' + tm • u')) f - inner ℝ (y l tm - (c + tm • u)) f := by
    intro f; rw [inner_sub_left, inner_sub_left]; ring
  have dV : ∀ f : EuclideanSpace ℝ (Fin 2),
      inner ℝ u f - inner ℝ u' f = inner ℝ (v l - u') f - inner ℝ (v l - u) f := by
    intro f; rw [inner_sub_left, inner_sub_left]; ring
  have hK0 : 0 ≤ K := by
    have := abs_nonneg (inner ℝ (y l tm - (c + tm • u)) e)
    have := s1
    nlinarith
  have hKb' : 2 * K + 1 ≤ (Kb : ℝ) := hKb
  have box : ∀ (a b B : ℝ), 0 < B → |a - b| ≤ 2 * K * B →
      (⌊a / B⌋ : ℤ) ∈ intBox ⌊b / B⌋ Kb :=
    fun a b B hB hab => floor_mem_intBox hKb' hB hab
  have hS₁q : 0 < S₁ / q₁ := div_pos hS₁ hq₁
  have hS₂q : 0 < S₂ / q₁ := div_pos hS₂ hq₁
  have vbound : ∀ (a b : ℝ) (B : ℝ), |a| * q₁ ≤ K * B → |b| * q₁ ≤ K * B →
      |a - b| ≤ 2 * K * (B / q₁) :=
    fun a b B ha hb => abs_sub_le_of_scaled hq₁ ha hb
  -- membership
  unfold codeNbhd
  rw [Finset.mem_biUnion]
  refine ⟨(σ, kn - roundCode g (σ • nrm Q')), Finset.mem_product.mpr ⟨hσ, hδ⟩, ?_⟩
  simp only
  rw [Finset.mem_image]
  refine ⟨((chartCode g S₁ S₂ q₁ tm c u Q).kp, (chartCode g S₁ S₂ q₁ tm c u Q).kv), ?_, ?_⟩
  · simp only [Finset.mem_product]
    have hkn' : roundCode g (σ • nrm Q') + (kn - roundCode g (σ • nrm Q')) = kn := by abel
    rw [hkn']
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact box _ _ S₁ hS₁ (by rw [dP]; exact (abs_sub _ _).trans (by linarith))
    · exact box _ _ S₂ hS₂ (by rw [dP]; exact (abs_sub _ _).trans (by linarith))
    · exact box _ _ (S₁ / q₁) hS₁q (by rw [dV]; exact vbound _ _ S₁ w3 s3)
    · exact box _ _ (S₂ / q₁) hS₂q (by rw [dV]; exact vbound _ _ S₂ w4 s4)
  · have hkn' : roundCode g (σ • nrm Q') + (kn - roundCode g (σ • nrm Q')) = kn := by abel
    rw [hkn']
    rfl

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
