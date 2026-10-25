-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.BodyDyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyNormalization
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.DyadicPrisms

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (prism prism_mono prism_eq_orthogonalBox orthogonalBox_subset_ball volume_prism
    exists_dyadic_between dyadic_round_mono)

theorem normalized_dyadic_body {U : Set Space} (hUc : IsCompact U)
    (hUconv : Convex ℝ U) {x : Space} {δ B S : ℝ} {K : ℕ}
    (hδ : 0 < δ) (hSlarge : 1000000000 ≤ S)
    (hK : (1 / 2 : ℝ) ^ K < δ / (6 * S))
    (hball : ball x δ ⊆ U)
    (hdiam : ∃ p ∈ U, ∃ q ∈ U, (1 / 16 : ℝ) ≤ dist p q)
    (hwide : WideSection U B) (f : Space ≃ᵃ[ℝ] Space)
    (hsmall : f ⁻¹' U ⊆ closedBall (0 : Space) (2 / S))
    (hLip : ∀ p q, dist (f p) (f q) ≤ (6 * S) * dist p q) :
    ∃ (k l : Fin (K + 1)) (u : OrthonormalBasis (Fin 3) ℝ Space),
      let a := (1 / 2 : ℝ) ^ k.val
      let b := (1 / 2 : ℝ) ^ l.val
      δ / (12 * S) ≤ a ∧ a ≤ b ∧ B / (24 * S) ≤ b ∧
      b ≤ 48 / S ∧ b ≤ 1 / 1000000 ∧
      prism a b (f.symm x) u ⊆ ball (0 : Space) (1 / 100) ∧
      U ⊆ f '' prism a b (f.symm x) u ∧
      volume (prism a b (f.symm x) u) ≤
        ENNReal.ofReal (400000 * S) * volume (f ⁻¹' U) := by
  have hS : 0 < S := by linarith
  obtain ⟨a, b, u, hδa, ha, hab, hBb, hbS, hb, hsmallP, hU, hvol⟩ :=
    normalized_convex_prism hUc hUconv hδ hSlarge hball hdiam hwide f hsmall hLip
  have hbase : (1 / 2 : ℝ) ^ K < 2 * (δ / (12 * S)) := by
    convert hK using 1 <;> ring
  have hb1 : b ≤ 1 := hb.trans (by norm_num)
  obtain ⟨k, hk, hka, hka2⟩ := exists_dyadic_between
    (by positivity : 0 < δ / (12 * S)) hbase hδa (hab.trans hb1)
  obtain ⟨l, hl, hlb, hlb2⟩ := exists_dyadic_between
    (by positivity : 0 < δ / (12 * S)) hbase (hδa.trans hab) hb1
  have hab' := dyadic_round_mono hab hka2 hlb
  have hlS : (1 / 2 : ℝ) ^ l ≤ 48 / S := by
    calc
      (1 / 2 : ℝ) ^ l ≤ 2 * b := hlb2.le
      _ ≤ 2 * (24 / S) := by gcongr
      _ = _ := by ring
  have hlsmall : (1 / 2 : ℝ) ^ l ≤ 1 / 1000000 := by
    apply hlS.trans
    rw [div_le_iff₀ hS]
    linarith
  have hmono := prism_mono hka hlb (f.symm x) (u : Fin 3 → Space)
  refine ⟨⟨k, by omega⟩, ⟨l, by omega⟩, u, hδa.trans hka, hab',
    hBb.trans hlb, hlS, hlsmall, ?_, hU.trans (image_mono hmono), ?_⟩
  · have hx : ‖f.symm x‖ ≤ 2 / S := by
      have hxU : f.symm x ∈ f ⁻¹' U := by simpa using hball (mem_ball_self hδ)
      simpa using hsmall hxU
    rw [prism_eq_orthogonalBox]
    apply orthogonalBox_subset_ball _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    · intro i
      fin_cases i
      · exact hab'.trans (hlsmall.trans (by norm_num))
      · exact hlsmall.trans (by norm_num)
      · exact le_rfl
    · have h : 2 / S ≤ (1 / 1000000 : ℝ) := by
        rw [div_le_iff₀ hS]
        linarith
      linarith
  · have hbpos : 0 ≤ b := ha.le.trans hab
    have hfour : volume (prism ((1 / 2 : ℝ) ^ k) ((1 / 2 : ℝ) ^ l) (f.symm x) u) ≤
        ENNReal.ofReal 4 * volume (prism a b (f.symm x) u) := by
      rw [volume_prism _ _ (by positivity) (by positivity), volume_prism _ _ ha.le hbpos,
        ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul hka2.le hlb2.le (by positivity) (by positivity)
      nlinarith only [h]
    calc
      _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal (2000 * S) * volume (f ⁻¹' U)) :=
        hfour.trans (mul_le_mul' le_rfl hvol)
      _ = ENNReal.ofReal (8000 * S) * volume (f ⁻¹' U) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
        congr 2
        ring
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end WangZahlLot.Obl.wz_flat_factored_improvement
