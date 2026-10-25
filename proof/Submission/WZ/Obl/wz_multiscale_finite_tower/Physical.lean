-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Physical.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Local
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.LocalEstimate

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (ConvexCount SlabBound Fibre doubled convexCount_mono slabBound_mono)

/-- The physical fibre invariant, with all errors measured at the bottom scale. -/
def PhysicalFrame (d r s θ : ℝ) (y w : Space) (n : ℕ)
    (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
  (∀ i, ‖v i‖ = 1 ∧ Tube s (x i) (v i) ⊆ Tube r y w ∧
    MeasurableSet (Y i) ∧ Y i ⊆ Tube s (x i) (v i)) ∧
  ENNReal.ofReal (d ^ θ * n * s ^ 2) ≤ ∑ i, volume (Y i) ∧
  ConvexCount s (d ^ (-θ)) (fun _ => True) (fun i => Tube s (x i) (v i)) ∧
  SlabBound (doubled r y w) (d ^ (-θ)) (fun _ => True) (fun i => Tube s (x i) (v i))

theorem PhysicalFrame.to_fibre {d r s θ h η : ℝ} {y w : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : PhysicalFrame d r s θ y w n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) (hs : 0 < s)
    (hη : 0 ≤ η) (hgap : s / r ≤ d ^ h) (hθη : θ ≤ h * η) :
    Fibre r s η y w x v Y := by
  have hratio : 0 < s / r := div_pos hs hr
  have hden := local_density_power hd hd1 hratio.le hη hgap hθη
  have hcount : d ^ (-θ) ≤ (s / r) ^ (-η) := by
    rw [Real.rpow_neg hd.le, Real.rpow_neg hratio.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hratio _) hden
  exact ⟨hF.1, hF.2.1,
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hden (Nat.cast_nonneg n)) (sq_nonneg s))).trans hF.2.2.1,
    convexCount_mono hcount hF.2.2.2.1, slabBound_mono hcount hF.2.2.2.2⟩

theorem Endpoint.to_estimateE {σ ω : ℝ} (hE : Endpoint σ ω) :
    WangZahlLot.Obl.wz_nonflat_factored_improvement.EstimateE σ ω := by
  intro ε hε
  obtain ⟨a, ha, η, hη, HE⟩ := hE ε hε
  refine ⟨a, ha, η, hη, ?_⟩
  intro d hd hd100 M L hM hL n x v Y hn hv hball hsep hYm hYT hmass hK hF
  exact HE d hd hd100 M L hM hL n x v Y
    ⟨hn, fun i => ⟨hv i, hball i, hYm i, hYT i⟩, hsep, hmass, hK, hF⟩

/-- The accepted affine normalization supplies a physical endpoint estimate on each
large logarithmic gap. No separation hypothesis is needed for the fibre. -/
theorem Endpoint.physical_on_large_gap {σ ω : ℝ} (hE : Endpoint σ ω) (hσ : 0 ≤ σ)
    {loss h : ℝ} (hloss : 0 < loss) (hh : 0 < h) :
    ∃ a θ c : ℝ, 0 < a ∧ 0 < θ ∧ θ ≤ 1 ∧ 0 < c ∧ c ≤ 1 ∧
      ∀ d r s : ℝ, 0 < d → d ≤ 1 → 0 < r → 0 < s → d * r ≤ s →
      s ≤ c * r → r ≤ 1 → s / r ≤ d ^ h →
      ∀ y w : Space, ‖w‖ = 1 → ∀ n x v Y,
      PhysicalFrame d r s θ y w n x v Y →
      ENNReal.ofReal (a * d ^ loss * r ^ 2 * volumeFactor σ ω (s / r) n) ≤
        volume (⋃ i, Y i) := by
  obtain ⟨a, η, c, ha, hη, hc, hc1, HE⟩ :=
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.local_estimate hσ hE.to_estimateE hloss
  refine ⟨a, min 1 (h * η), c, ha, lt_min zero_lt_one (mul_pos hh hη),
    min_le_left _ _, hc, hc1, ?_⟩
  intro d r s hd hd1 hr hs hdr hsr hr1 hgap y w hw n x v Y hF
  have hF' := hF.to_fibre hd hd1 hr hs hη.le hgap (min_le_right _ _)
  have hV := HE η r s hη le_rfl hs hsr hr1 y w hw n x v Y hF'
  have hratio : 0 < s / r := div_pos hs hr
  have hp : d ^ loss ≤ (s / r) ^ loss :=
    Real.rpow_le_rpow hd.le ((le_div_iff₀ hr).mpr hdr) hloss.le
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hV
  calc
    _ ≤ a * (s / r) ^ loss * r ^ 2 * volumeFactor σ ω (s / r) n := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp ha.le) (sq_nonneg r))
      dsimp [volumeFactor]
      positivity
    _ = _ := by
      dsimp [volumeFactor]
      rw [Real.rpow_add hratio]
      field_simp

end WangZahlLot.Obl.wz_multiscale_finite_tower
