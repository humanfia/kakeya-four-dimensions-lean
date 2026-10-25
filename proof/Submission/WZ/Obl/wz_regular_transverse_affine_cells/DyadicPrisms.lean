-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.DyadicPrisms.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.TubePrism
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Dyadic
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Basic

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set
open scoped ENNReal

lemma prism_isClosed (a b : ℝ) (c : E) (u : Fin 3 → E) :
    IsClosed (prism a b c u) := by
  have hf (k : Fin 3) : Continuous (fun p : E => |inner ℝ (u k) (p - c)|) := by fun_prop
  exact (isClosed_le (hf 0) continuous_const).inter
    ((isClosed_le (hf 1) continuous_const).inter (isClosed_le (hf 2) continuous_const))

lemma closedTube_subset_affine_prism {δ a b : ℝ} {x v c : E} {u : Fin 3 → E}
    (f : E ≃ᵃ[ℝ] E) (h : tube δ x v ⊆ f '' prism a b c u) :
    closedTube δ x v ⊆ f '' prism a b c u := by
  apply closure_minimal h
  exact f.toContinuousAffineEquiv.toHomeomorph.isClosedMap _ (prism_isClosed a b c u)

lemma dyadic_round_mono {a b : ℝ} {k l : ℕ} (hab : a ≤ b)
    (hk : (1 / 2 : ℝ) ^ k < 2 * a) (hl : b ≤ (1 / 2 : ℝ) ^ l) :
    (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ l := by
  by_cases h : l ≤ k
  · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  · have hkl : k + 1 ≤ l := by omega
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hkl
    rw [pow_succ] at hp
    nlinarith

/-- All normalizations use the same finite dyadic palette. The rounding happens
before density and local regularity are imposed. -/
lemma normalized_dyadic_tube_prism {δ S : ℝ} (hδ : 0 < δ) (hSlarge : 1000000000 ≤ S)
    {K : ℕ} (hK : (1 / 2 : ℝ) ^ K < δ / (6 * S))
    (f : E ≃ᵃ[ℝ] E) (x v : E) (hv : ‖v‖ = 1)
    (htube : tube δ x v ⊆ Metric.ball (0 : E) 1)
    (hsmall : f ⁻¹' closedTube δ x v ⊆ Metric.closedBall (0 : E) (2 / S))
    (hLip : ∀ p q, dist (f p) (f q) ≤ (6 * S) * dist p q) :
    ∃ (k l : Fin (K + 1)) (u : OrthonormalBasis (Fin 3) ℝ E),
      let a := (1 / 2 : ℝ) ^ k.val
      let b := (1 / 2 : ℝ) ^ l.val
      δ / (12 * S) ≤ a ∧ a ≤ b ∧ b ≤ 48 / S ∧ b ≤ 1 / 1000000 ∧
      prism a b (f.symm x) u ⊆ Metric.ball (0 : E) (1 / 100) ∧
      closedTube δ x v ⊆ f '' prism a b (f.symm x) u ∧
      volume (prism a b (f.symm x) u) ≤ ENNReal.ofReal (400000 * S) *
        volume (f ⁻¹' closedTube δ x v) := by
  have hS : 0 < S := by linarith
  obtain ⟨a₀, b₀, u, haδ, ha₀, hab₀, hbS, hb₀, hPball, hwhole, hvol⟩ :=
    normalized_tube_prism hδ hSlarge f x v hv htube hsmall hLip
  have hb₀1 : b₀ ≤ 1 := hb₀.trans (by norm_num)
  have hbottom : (1 / 2 : ℝ) ^ K < 2 * (δ / (12 * S)) := by
    calc (1 / 2 : ℝ) ^ K < δ / (6 * S) := hK
      _ = _ := by ring
  obtain ⟨k, hkK, hka, hka'⟩ := exists_dyadic_between (by positivity : 0 < δ / (12 * S))
    hbottom haδ (hab₀.trans hb₀1)
  obtain ⟨l, hlK, hlb, hlb'⟩ := exists_dyadic_between (by positivity : 0 < δ / (12 * S))
    hbottom (haδ.trans hab₀) hb₀1
  let a := (1 / 2 : ℝ) ^ k
  let b := (1 / 2 : ℝ) ^ l
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := dyadic_round_mono hab₀ hka' hlb
  have hbS' : b ≤ 48 / S := by
    calc b ≤ 2 * b₀ := hlb'.le
      _ ≤ 2 * (24 / S) := by gcongr
      _ = _ := by ring
  have hbsmall : b ≤ 1 / 1000000 := by
    apply hbS'.trans
    rw [div_le_iff₀ hS]
    linarith
  have hmono : prism a₀ b₀ (f.symm x) u ⊆ prism a b (f.symm x) u := prism_mono hka hlb _ _
  refine ⟨⟨k, by omega⟩, ⟨l, by omega⟩, u, haδ.trans hka, hab, hbS', hbsmall, ?_, ?_, ?_⟩
  · have hxsmall : ‖f.symm x‖ ≤ 2 / S := by
      have hx : f.symm x ∈ f ⁻¹' closedTube δ x v := by
        simpa using (closedTube_endpoints hδ x v).1
      simpa using hsmall hx
    rw [prism_eq_orthogonalBox]
    apply orthogonalBox_subset_ball _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    · intro i
      fin_cases i
      · exact hab.trans (hbsmall.trans (by norm_num))
      · exact hbsmall.trans (by norm_num)
      · exact le_rfl
    · have hx : 2 / S ≤ (1 / 1000000 : ℝ) := by rw [div_le_iff₀ hS]; linarith
      linarith
  · exact (closedTube_subset_affine_prism f hwhole).trans (image_mono hmono)
  · have hv4 : volume (prism a b (f.symm x) u) ≤ 4 * volume (prism a₀ b₀ (f.symm x) u) := by
      rw [volume_prism _ _ ha.le hb.le, volume_prism _ _ ha₀.le (ha₀.le.trans hab₀),
        ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hmul := mul_le_mul hka'.le hlb'.le (by positivity : (0 : ℝ) ≤ (1 / 2) ^ l)
        (by positivity : 0 ≤ 2 * a₀)
      dsimp [a, b]
      nlinarith
    calc volume (prism a b (f.symm x) u) ≤ 4 * volume (prism a₀ b₀ (f.symm x) u) := hv4
      _ ≤ 4 * (ENNReal.ofReal (100000 * S) * volume (f ⁻¹' closedTube δ x v)) := mul_le_mul_right hvol _
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
        congr 2
        ring

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
