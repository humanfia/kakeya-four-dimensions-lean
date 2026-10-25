-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.Extremal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Slices

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- The extremal deficit predicate in the frozen statement. -/
def Extremal (s : ℝ) : Prop :=
  ∀ η d0 : ℝ, 0 < η → 0 < d0 → ∃ δ : ℝ,
    0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
    ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Dense η δ n x v Y ∧ Strong η δ n x v ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ s)

lemma strong_mono_error {η ε δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε)
    (h : Strong η δ n x v) : Strong ε δ n x v := by
  have hpow : δ ^ (-η) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  intro r hdr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, hcov, hsep⟩ := h r hdr hr1
  refine ⟨ρ, hrρ, hρ1,
    hρr.trans (mul_le_mul_of_nonneg_right hpow (hδ.le.trans hdr)),
    k, hk, z, w, ?_, hsep⟩
  obtain ⟨hw, hdisj, huniq, hfull, hbal, hcount⟩ := hcov
  refine ⟨hw, hdisj, huniq, hfull, ?_, ?_⟩
  · intro j j'
    exact (hbal j j').trans (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  · intro j W hW
    refine (hcount j W hW).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    exact mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)

lemma Extremal.mono {s t : ℝ} (h : Extremal s) (hts : t ≤ s) : Extremal t := by
  intro η d0 hη hd0
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hH, hS, hvol⟩ := h η d0 hη hd0
  refine ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hH, hS, hvol.trans ?_⟩
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) hts)

/-- Failure of an exponent supplies a uniform lower volume bound at some fixed error. -/
theorem uniform_volume_lower {s : ℝ} (h : ¬ Extremal s) :
    ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Dense η δ n x v Y → Strong η δ n x v →
          ENNReal.ofReal (δ ^ s) < volume (⋃ i, Y i) := by
  classical
  by_contra hnot
  push Not at hnot
  apply h
  intro η d0 hη hd0
  exact hnot η d0 hη hd0

/-- The uniform lower estimate is valid at every smaller positive error. -/
theorem uniform_volume_lower_mono {σ : ℝ} (hupper : ∀ t : ℝ, σ < t → ¬ Extremal t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η0 d0 : ℝ, 0 < η0 ∧ 0 < d0 ∧
      ∀ η δ : ℝ, η ≤ η0 → 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Dense η δ n x v Y → Strong η δ n x v →
          ENNReal.ofReal (δ ^ (σ + ε)) < volume (⋃ i, Y i) := by
  obtain ⟨η0, d0, hη0, hd0, hlower⟩ :=
    uniform_volume_lower (hupper (σ + ε) (by linarith))
  refine ⟨η0, d0, hη0, hd0, ?_⟩
  intro η δ hη hδ hδd hδ100 n x v Y hH hS
  have hδ1 : δ ≤ 1 := by linarith
  exact hlower δ hδ hδd hδ100 n x v Y
    (dense_mono_error hδ hδ1 hη hH) (strong_mono_error hδ hδ1 hη hS)

end WangZahlLot.Obl.wz_grains_nonsingular_slices
