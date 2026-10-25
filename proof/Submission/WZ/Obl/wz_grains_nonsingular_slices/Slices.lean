-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Slices.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Basic

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- The AD estimate gives a power bound on a slice lying in `[-2,2]`. -/
lemma volume_le_eight_rpow {δ η σ : ℝ} {B : Set ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 ≤ σ) (_hσ1 : σ ≤ 1)
    (hB : B ⊆ Icc (-2) 2) (h : AD δ (1 - σ) (δ ^ (-η)) B) :
    volume B ≤ ENNReal.ofReal (8 * δ ^ (σ - η)) := by
  have hB' : B ⊆ Icc (-2) (-2 + 4) := by norm_num; exact hB
  have hv := volume_le_of_ad hδ.le (show δ ≤ 4 by linarith) hB' h
  have hfour : (4 : ℝ) ^ (1 - σ) ≤ 4 := by
    calc (4 : ℝ) ^ (1 - σ) ≤ 4 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have hpow : δ * (δ ^ (-η) * (δ ^ (1 - σ))⁻¹) = δ ^ (σ - η) := by
    rw [← Real.rpow_neg hδ.le, ← Real.rpow_add hδ]
    nth_rw 1 [← Real.rpow_one δ]
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have heq : 2 * δ * (δ ^ (-η) * (4 / δ) ^ (1 - σ)) =
      2 * 4 ^ (1 - σ) * δ ^ (σ - η) := by
    rw [Real.div_rpow (by norm_num) hδ.le, div_eq_mul_inv, ← hpow]
    ring
  refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [heq]
  nlinarith [Real.rpow_nonneg hδ.le (σ - η)]

/-- Every positive gap between exponents absorbs the fixed factor from the covering. -/
lemma exists_slice_cutoff {σ η : ℝ} (hgap : σ / 8 < σ - η) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      8 * δ ^ (σ - η) ≤ δ ^ (σ / 8) / 2 := by
  obtain ⟨d, hd, hcut⟩ := exists_rpow_cutoff
    (show 0 < σ - η - σ / 8 by linarith) (show (0 : ℝ) < 1 / 16 by norm_num)
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδd
  have h := mul_le_mul_of_nonneg_left (hcut δ hδ hδd)
    (Real.rpow_nonneg hδ.le (σ / 8))
  rw [← Real.rpow_add hδ] at h
  have hexp : σ / 8 + (σ - η - σ / 8) = σ - η := by ring
  rw [hexp] at h
  linarith

/-- A larger error parameter weakens the global count. -/
lemma GlobalCount.mono_error {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε)
    (h : GlobalCount η δ n x v) : GlobalCount ε δ n x v := by
  intro W hW
  refine (h W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) (Nat.cast_nonneg _)

/-- A larger error parameter weakens the shading mass requirement. -/
lemma dense_mono_error {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε)
    (h : Dense η δ n x v Y) : Dense ε δ n x v Y := by
  obtain ⟨hn, hv, hball, hsep, hmeas, hY, hmass⟩ := h
  refine ⟨hn, hv, hball, hsep, hmeas, hY, le_trans (ENNReal.ofReal_le_ofReal ?_) hmass⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hηε) (Nat.cast_nonneg _)) (sq_nonneg _)

/-- Global and local grains with the precise regularity and volume in the frozen premise. -/
def Grains (σ : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
    0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ Strong η δ n x v ∧
      (∀ i, IsCompact (Y i)) ∧ volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
      ∃ (f : ℝ → ℝ) (P : Space → Space),
        (ContDiff ℝ 2 f ∧ ∀ z ∈ Icc (-1) 1,
          |f z| ≤ 1 ∧ |deriv f z| ≤ 1 ∧ |deriv (deriv f) z| ≤ 1) ∧
        (∀ z ∈ Icc (-1) 1, AD δ (1 - σ) (δ ^ (-η)) (PS f (⋃ i, Y i) z)) ∧
        LipschitzWith 1 P ∧ (∀ p ∈ ⋃ i, Y i, ‖P p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ) ∧
        (∀ ρ : ℝ, δ ≤ ρ → ρ ≤ 1 → ∀ p ∈ ⋃ i, Y i,
          AD ρ (1 - σ) (δ ^ (-η))
            ((fun q : Space => inner ℝ (P p) q) '' ((⋃ i, Y i) ∩ ball p (Real.sqrt ρ))))

/-- All required quantitative slice bounds hold for the original regular slope.
The nonsingularity and transverse-coordinate normalization are not asserted here. -/
theorem regular_slices {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hC : Grains σ) :
    ∀ ε d0 : ℝ, 0 < ε → 0 < d0 → ∃ δ : ℝ,
      0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Dense ε δ n x v Y ∧ (∀ i, IsCompact (Y i)) ∧ GlobalCount ε δ n x v ∧
        ∃ f : ℝ → ℝ, (ContDiff ℝ 2 f ∧ ∀ z ∈ Icc (-1) 1,
          |f z| ≤ 1 ∧ |deriv f z| ≤ 1 ∧ |deriv (deriv f) z| ≤ 1) ∧
        ∀ z ∈ Icc (-1) 1,
          volume (PS f (⋃ i, Y i) z) ≤ ENNReal.ofReal (δ ^ (σ / 8) / 2) := by
  intro ε d0 hε hd0
  let η := min ε (σ / 4)
  have hη : 0 < η := lt_min hε (by positivity)
  have hηε : η ≤ ε := min_le_left _ _
  have hησ : η ≤ σ / 4 := min_le_right _ _
  obtain ⟨d, hd, hcut⟩ := exists_slice_cutoff (show σ / 8 < σ - η by linarith)
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hH, hS, hcompact, _,
    f, P, hf, hAD, _⟩ := hC η (min d0 d) hη (lt_min hd0 hd)
  have hδ1 : δ ≤ 1 := by linarith
  have hE : (⋃ i, Y i) ⊆ ball 0 1 :=
    iUnion_subset fun i => (hH.2.2.2.2.2.1 i).trans (hH.2.2.1 i)
  refine ⟨δ, hδ, hδd.trans (min_le_left _ _), hδ100, n, x, v, Y,
    dense_mono_error hδ hδ1 hηε hH, hcompact,
    (globalCount_of_strong hδ hδ1 hS).mono_error hδ hδ1 hηε, f, hf, ?_⟩
  intro z hz
  exact (volume_le_eight_rpow hδ hδ1 hσ.le hσ1.le
    (ps_subset_interval hE (hf.2 z hz).1) (hAD z hz)).trans
      (ENNReal.ofReal_le_ofReal (hcut δ hδ (hδd.trans (min_le_right _ _))))

/-- The complete normalized conclusion of the frozen obligation. -/
def NormalizedExamples (σ : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
    0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ (∀ i, IsCompact (Y i)) ∧
      (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) ∧ GlobalCount η δ n x v ∧
      ∃ f : ℝ → ℝ,
        (ContDiff ℝ 2 f ∧ ∀ z ∈ Icc (-1) 1,
          1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧
            |deriv (deriv f) z| ≤ (1 / 100 : ℝ)) ∧
        ∀ z ∈ Icc (-1) 1,
          volume (PS f (⋃ i, Y i) z) ≤ ENNReal.ofReal (δ ^ (σ / 8) / 2)

end WangZahlLot.Obl.wz_grains_nonsingular_slices
