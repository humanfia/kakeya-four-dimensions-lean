-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.LocalizedRegularity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleLocalization
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionNumerics
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FiniteLineMap

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

theorem LocalizedTriple.frostman {δ θ ζ : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (R : LocalizedTriple (δ ^ θ) δ ζ F G U H) (hδ : 0 < δ)
    (hF : ClosedFiniteFrostman δ (δ ^ (-θ)) F)
    (hG : ClosedFiniteFrostman δ (δ ^ (-θ)) G)
    (hU : ClosedFiniteFrostman δ (δ ^ (-θ)) U) :
    ClosedFiniteFrostman δ (projectionFrostman δ θ ζ) R.first ∧
      ClosedFiniteFrostman δ (projectionFrostman δ θ ζ) R.second ∧
      ClosedFiniteFrostman δ (projectionFrostman δ θ ζ) R.third := by
  have hret : 0 < (δ ^ θ) ^ (3 : ℕ) * δ ^ ζ / 27648 := by positivity
  have h₁ := hF.subset hδ.le (by positivity) hret R.first_subset R.first_retention
  have h₂ := hG.subset hδ.le (by positivity) hret R.second_subset R.second_retention
  have h₃ := hU.subset hδ.le (by positivity) hret R.third_subset R.third_retention
  rw [localization_frostman_identity hδ] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

theorem LocalizedTriple.nonempty_factors {d δ ζ : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (R : LocalizedTriple d δ ζ F G U H) : R.first.Nonempty ∧ R.second.Nonempty ∧ R.third.Nonempty := by
  obtain ⟨p, hp⟩ := R.nonempty
  have h := Finset.mem_product.mp (R.contained hp)
  have h' := Finset.mem_product.mp h.2
  exact ⟨⟨p.1, h.1⟩, ⟨p.2.1, h'.1⟩, ⟨p.2.2, h'.2⟩⟩

theorem projectionLine_ge_one {δ θ ζ β : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ) (hβ : 0 ≤ β) : 1 ≤ projectionLine δ θ ζ β := by
  have hp : 1 ≤ δ ^ (-(2 * θ + β * ζ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by have := mul_nonneg hβ hζ; linarith)
  unfold projectionLine
  linarith

theorem localized_line_rescaling {S : Finset Plane} {δ θ ζ β w h : ℝ}
    (hδ : 0 < δ) (hζ : 0 ≤ ζ) (hw : 0 < w) (hh : 0 < h)
    (hwidth : h ≤ δ ^ (-β) * w)
    (hline : StripFrostman δ (13824 / (δ ^ θ) ^ (2 : ℕ)) ζ w S) :
    StripFrostman δ (projectionLine δ θ ζ β) ζ h S := by
  have hbase := hline.change_width hδ.le hw hh
  apply hbase.mono_constant hδ.le hh
  have hratio : h / w ≤ δ ^ (-β) := (div_le_iff₀ hw).mpr hwidth
  calc (13824 / (δ ^ θ) ^ (2 : ℕ)) * (h / w) ^ ζ ≤
        (13824 / (δ ^ θ) ^ (2 : ℕ)) * (δ ^ (-β)) ^ ζ := by gcongr
    _ = projectionLine δ θ ζ β := by
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_mul hδ.le]
      norm_num only [Nat.cast_ofNat]
      have heq : 13824 / δ ^ (θ * 2) * δ ^ (-β * ζ) =
          13824 * (δ ^ (-β * ζ) / δ ^ (θ * 2)) := by ring
      rw [heq, ← Real.rpow_sub hδ]
      unfold projectionLine
      congr 2
      ring

theorem capped_width_bounds {δ β t w : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ : 0 ≤ β) (ht1 : t ≤ 1) (hδw : δ ≤ w)
    (hwide : δ ^ (1 - t) < δ ^ (-β) * w) :
    δ ≤ min 1 (δ ^ (-β) * w) ∧
      δ / min 1 (δ ^ (-β) * w) ≤ δ ^ t ∧
      (min 1 (δ ^ (-β) * w) < 1 → min 1 (δ ^ (-β) * w) = δ ^ (-β) * w) := by
  have hw : 0 < w := hδ.trans_le hδw
  have hp : 1 ≤ δ ^ (-β) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hδW : δ ≤ δ ^ (-β) * w := hδw.trans (by nlinarith)
  have hδh : δ ≤ min 1 (δ ^ (-β) * w) := le_min hδ1 hδW
  refine ⟨hδh, ?_, ?_⟩
  · have hh : 0 < min 1 (δ ^ (-β) * w) := hδ.trans_le hδh
    apply (div_le_iff₀ hh).mpr
    have hr : δ ^ (1 - t) ≤ min 1 (δ ^ (-β) * w) := le_min
      (Real.rpow_le_one hδ.le hδ1 (by linarith)) hwide.le
    calc δ = δ ^ t * δ ^ (1 - t) := by rw [← Real.rpow_add hδ]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)
  · intro hh
    exact min_eq_right (by
      by_contra hn
      have hW : 1 ≤ δ ^ (-β) * w := (lt_of_not_ge hn).le
      rw [min_eq_left hW] at hh
      exact (lt_irrefl _ hh))

end WangZahlLot.Obl.wz_separated_projection_dichotomy
