-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Proof.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallScaleGain
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FiniteScales

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal

/-- The assembled gain, with the auxiliary small-scale cutoff removed. -/
theorem clustered_gain {σ ω : ℝ} (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hE : E σ ω) (hJ : J σ ω)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ h : ℝ, 0 < h ∧ h ≤ ζ / 10 ∧ ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
    A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
    ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ)
      (y w : Fin N → V) (f : Fin n → Fin N),
    G ω δ h n x v Y S Z ρ N y w f →
    (∀ U : Finset (Fin N), O (δ ^ (ζ / 2)) * ∑ i ∈ S, volume (Z i) ≤
        ∑ i ∈ S.filter (fun i => f i ∈ U), volume (Z i) →
      ¬ ∀ Q, Convex ℝ Q → O (q N {k | k ∈ U ∧ T ρ (y k) (w k) ⊆ Q} * ρ ^ 2) ≤
        O (δ ^ (-ζ)) * volume Q) →
    O (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨h, α, κs, d, hh, hhζ, hα, hκs, hd, Hsmall⟩ := clustered_gain_small hσ hσhalf hω hω1 hE hJ hζ
  obtain ⟨κb, hκb, Hbig⟩ := Parent.first_alternative_away_from_zero hσ.le hh.le hd (ω - α)
  refine ⟨h, hh, hhζ, α, hα, min κs κb, lt_min hκs hκb, ?_⟩
  intro δ hδ hδ100 n x v Y hA S Z ρ N y w f hG hno
  have hδ1 : δ ≤ 1 := by linarith
  by_cases hδd : δ ≤ d
  · exact Parent.Interfaces.gain_mono hδ hδ1 le_rfl (min_le_left _ _) hκs.le
      (Hsmall δ hδ hδ100 hδd n x v Y hA S Z ρ N y w f hG hno)
  · exact Parent.Interfaces.gain_mono hδ hδ1 le_rfl (min_le_right _ _) hκb.le
      (Hbig δ (le_of_not_ge hδd) hδ1 n x v Y (Parent.hypotheses_iff.mpr hA))

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
