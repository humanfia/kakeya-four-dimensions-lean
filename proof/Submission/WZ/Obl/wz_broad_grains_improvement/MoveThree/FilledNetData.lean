-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FilledNetData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FilledNetData.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FilledNetData.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ShortCarrier
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FilledNormalization
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FilledDensity

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent (uniformMap uniformMap_apply uniformMap_volume)

/-- Each adapted filled prism supplies the square-prism containment, centre and
density data required by the balanced intermediate-net estimate. -/
theorem filled_prism_net_data {δ a b r k D : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 3)
    (hr : 5 * (a / 2) ≤ r) (hrhi : r ≤ 4 * a)
    (hk : 0 < k) (hksmall : k ≤ 1 / 100000000) (hD : 0 ≤ D)
    (z v : V) (hv : ‖v‖ = 1) (e g : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ q i, f.linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e q i)
    (hfvol : ∀ Q : Set V, μ (f '' Q) = O (1 / (4 * a * b)) * μ Q)
    (hfz : ‖f z‖ ≤ 2) (hv₀ : |e v 0| ≤ 4 * a) (hv₁ : |e v 1| ≤ 4 * b)
    (hg₂ : ∀ p, g p 2 = inner ℝ v p)
    (hg₀ : ∀ w, |g w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
      |inner ℝ (boxAxis e 0) v| * ‖w‖)) (Γ : Set V)
    (hden : O D * μ (P (10 * δ) (6 * b * δ / r) 2 z g) ≤
      μ (P (10 * δ) (6 * b * δ / r) 2 z g ∩ Γ)) :
    let F := f.trans (uniformMap hk).toAffineEquiv
    let B := 64 * k * δ / a
    B ≤ 1 / 1000000 ∧ ‖F z‖ < 1 / 100 ∧
      ∃ u : Fin 3 → V, Orthonormal ℝ u ∧
        F '' P (10 * δ) (6 * b * δ / r) 2 z g ⊆
          WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B (F z) u ∧
        O ((D * k / 1000) * B ^ 2) ≤
          μ (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B (F z) u ∩ F '' Γ) := by
  let F := f.trans (uniformMap hk).toAffineEquiv
  let B := 64 * k * δ / a
  change B ≤ 1 / 1000000 ∧ ‖F z‖ < 1 / 100 ∧ _
  have ha : 0 < a := hδ.trans_le hδa
  have hbpos : 0 < b := ha.trans_le hab
  have hrpos : 0 < r := by linarith
  obtain ⟨hsub, hlength⟩ := filled_prism_normalized_tube hδ ha hab hb hr z v hv e g f hf hv₀ hv₁ hg₂ hg₀
  have hvne : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  have haxis : (2 : ℝ) • f.linear v ≠ 0 :=
    smul_ne_zero (by norm_num) ((map_ne_zero_iff f.linear f.linear.injective).mpr hvne)
  have hB : B ≤ 1 / 1000000 := by
    calc
      _ ≤ 64 * k := by
        dsimp [B]
        rw [div_le_iff₀ ha]
        nlinarith [mul_le_mul_of_nonneg_left hδa hk.le]
      _ ≤ _ := by linarith
  have hrad : k * (64 * δ / a) = B := by dsimp [B]; ring
  obtain ⟨u, hu, hprism⟩ := contracted_short_carrier_prism (r := 64 * δ / a) hk (by linarith)
    (by simpa only [hrad] using hB) (f z - f.linear v) ((2 : ℝ) • f.linear v) haxis hlength
  have hmid : f z - f.linear v + (1 / 2 : ℝ) • ((2 : ℝ) • f.linear v) = f z := by module
  rw [hmid, hrad] at hprism
  have hcover : F '' P (10 * δ) (6 * b * δ / r) 2 z g ⊆
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B (F z) u := by
    rintro _ ⟨p, hp, rfl⟩
    exact hprism ⟨f p, hsub ⟨p, hp, rfl⟩, rfl⟩
  have hFvol (Q : Set V) : μ (F '' Q) = O (k ^ 3 / (4 * a * b)) * μ Q := by
    have he : F '' Q = uniformMap hk '' (f '' Q) := by
      rw [Set.image_image]
      rfl
    rw [he]
    have hcvol : μ (uniformMap hk '' (f '' Q)) = O (k ^ 3) * μ (f '' Q) := uniformMap_volume hk _
    rw [hcvol, hfvol, ← mul_assoc]
    dsimp only [O]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  refine ⟨hB, ?_, u, hu, hcover, ?_⟩
  · change ‖k • f z‖ < 1 / 100
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    nlinarith [mul_le_mul_of_nonneg_left hfz hk.le]
  · exact filled_round_density hδ ha hbpos hrpos hrhi hk hD z g F Γ _ hFvol hcover hden

/-- Each adapted filled prism supplies the square-prism containment, centre and
density data required by the balanced intermediate-net estimate. -/
theorem filled_prism_net_data_wide {δ a b r k D : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hb : b ≤ 4)
    (hr : 5 * (a / 2) ≤ r) (hrhi : r ≤ 4 * a)
    (hk : 0 < k) (hksmall : k ≤ 1 / 1000000000) (hD : 0 ≤ D)
    (z v : V) (hv : ‖v‖ = 1) (e g : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ q i, f.linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e q i)
    (hfvol : ∀ Q : Set V, μ (f '' Q) = O (1 / (4 * a * b)) * μ Q)
    (hfz : ‖f z‖ ≤ 2) (hv₀ : |e v 0| ≤ 4 * a) (hv₁ : |e v 1| ≤ 4 * b)
    (hg₂ : ∀ p, g p 2 = inner ℝ v p)
    (hg₀ : ∀ w, |g w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
      |inner ℝ (boxAxis e 0) v| * ‖w‖)) (Γ : Set V)
    (hden : O D * μ (P (10 * δ) (6 * b * δ / r) 2 z g) ≤
      μ (P (10 * δ) (6 * b * δ / r) 2 z g ∩ Γ)) :
    let F := f.trans (uniformMap hk).toAffineEquiv
    let B := 256 * k * δ / a
    B ≤ 1 / 1000000 ∧ ‖F z‖ < 1 / 100 ∧
      ∃ u : Fin 3 → V, Orthonormal ℝ u ∧
        F '' P (10 * δ) (6 * b * δ / r) 2 z g ⊆
          WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B (F z) u ∧
        O ((D * k / 16000) * B ^ 2) ≤
          μ (WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B (F z) u ∩ F '' Γ) := by
  let F := f.trans (uniformMap hk).toAffineEquiv
  let B := 256 * k * δ / a
  change B ≤ 1 / 1000000 ∧ ‖F z‖ < 1 / 100 ∧ _
  have ha : 0 < a := hδ.trans_le hδa
  have hbpos : 0 < b := ha.trans_le hab
  have hrpos : 0 < r := by linarith
  obtain ⟨hsub, hlength⟩ := filled_prism_normalized_tube_wide hδ ha hab hb hr z v hv e g f hf hv₀ hv₁ hg₂ hg₀
  have hvne : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  have haxis : (2 : ℝ) • f.linear v ≠ 0 :=
    smul_ne_zero (by norm_num) ((map_ne_zero_iff f.linear f.linear.injective).mpr hvne)
  have hB : B ≤ 1 / 1000000 := by
    calc
      _ ≤ 256 * k := by
        dsimp [B]
        rw [div_le_iff₀ ha]
        nlinarith [mul_le_mul_of_nonneg_left hδa hk.le]
      _ ≤ _ := by linarith
  have hrad : k * (256 * δ / a) = B := by dsimp [B]; ring
  obtain ⟨u, hu, hprism⟩ := contracted_short_carrier_prism (r := 256 * δ / a) hk (by linarith)
    (by simpa only [hrad] using hB) (f z - f.linear v) ((2 : ℝ) • f.linear v) haxis hlength
  have hmid : f z - f.linear v + (1 / 2 : ℝ) • ((2 : ℝ) • f.linear v) = f z := by module
  rw [hmid, hrad] at hprism
  have hcover : F '' P (10 * δ) (6 * b * δ / r) 2 z g ⊆
      WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism B B (F z) u := by
    rintro _ ⟨p, hp, rfl⟩
    exact hprism ⟨f p, hsub ⟨p, hp, rfl⟩, rfl⟩
  have hFvol (Q : Set V) : μ (F '' Q) = O (k ^ 3 / (4 * a * b)) * μ Q := by
    have he : F '' Q = uniformMap hk '' (f '' Q) := by
      rw [Set.image_image]
      rfl
    rw [he]
    have hcvol : μ (uniformMap hk '' (f '' Q)) = O (k ^ 3) * μ (f '' Q) := uniformMap_volume hk _
    rw [hcvol, hfvol, ← mul_assoc]
    dsimp only [O]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  refine ⟨hB, ?_, u, hu, hcover, ?_⟩
  · change ‖k • f z‖ < 1 / 100
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    nlinarith [mul_le_mul_of_nonneg_left hfz hk.le]
  · exact filled_round_density_wide hδ ha hbpos hrpos hrhi hk hD z g F Γ _ hFvol hcover hden

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
