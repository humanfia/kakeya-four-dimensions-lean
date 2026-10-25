-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.RegularPrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularShading
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GlobalFilling

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

theorem prism_convex (a b : ℝ) (c : Space) (u : Fin 3 → Space) :
    Convex ℝ (prism a b c u) := by
  have hcoord (i : Fin 3) (r : ℝ) : Convex ℝ {p | |inner ℝ (u i) (p - c)| ≤ r} := by
    have hh : Convex ℝ ((fun p : Space => inner ℝ (u i) p) ⁻¹' Icc (-r) r) :=
      (convex_Icc (-r) r).linear_preimage (innerSL ℝ (u i)).toLinearMap
    have ht := hh.translate_preimage_left (-c)
    change Convex ℝ {p : Space | -r ≤ inner ℝ (u i) (p + -c) ∧
      inner ℝ (u i) (p + -c) ≤ r} at ht
    simpa only [← abs_le, sub_eq_add_neg] using ht
  exact (hcoord 0 a).inter ((hcoord 1 b).inter (hcoord 2 (1 / 1000)))

theorem prism_measurable (a b : ℝ) (c : Space) (u : Fin 3 → Space) :
    MeasurableSet (prism a b c u) := by
  have hcoord (i : Fin 3) (r : ℝ) : MeasurableSet {p | |inner ℝ (u i) (p - c)| ≤ r} :=
    (isClosed_le ((continuous_const.inner (continuous_id.sub continuous_const)).abs)
      continuous_const).measurableSet
  exact (hcoord 0 a).inter ((hcoord 1 b).inter (hcoord 2 (1 / 1000)))

/-- At one specified radius, regularizing a prism shading costs only a fixed
constant in density and retains half of its mass. -/
theorem prism_regular_subshading {a b lam s : ℝ} (hlam : 0 ≤ lam) (hs : 0 < s)
    (c : Space) (u : Fin 3 → Space) (hu : Orthonormal ℝ u)
    (H : Set Space) (hHm : MeasurableSet H) (hHU : H ⊆ prism a b c u)
    (hdense : ENNReal.ofReal lam * volume (prism a b c u) ≤ volume H) :
    ∃ Z : Set Space, MeasurableSet Z ∧ Z ⊆ H ∧
      (1 / 2 : ℝ≥0∞) * volume H ≤ volume Z ∧
      ∀ p ∈ Z, ENNReal.ofReal (lam / 16000) * volume (prism a b c u ∩ ball p s) ≤
        volume (Z ∩ ball p s) := by
  have hTB := prism_totallyBounded a b c hu
  have hfin : volume (prism a b c u) ≠ ⊤ := hTB.isBounded.measure_lt_top.ne
  obtain ⟨Z, hZm, hZH, hmass, hreg⟩ := convex_regular_subshading_finite
    (prism_convex a b c u) (prism_measurable a b c u) hTB hfin hHm hHU hlam hdense
    (by norm_num : 0 < (1 : ℕ)) (fun _ => s) (fun _ => hs)
  exact ⟨Z, hZm, hZH, hmass, fun p hp => by simpa using hreg p hp 0⟩

/-- The anchor in the angular filling estimate only needs average density;
its one-scale regularity follows from a half-mass refinement. -/
theorem angular_global_filling_of_density {n B : ℕ} (hn : 0 < n) (hB : 1 ≤ B)
    {a b h lam θ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hh : 0 < h) (hlam : 0 < lam) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (c : Fin n → V) (u : Fin n → Fin 3 → V) (H : Fin n → Set V)
    (c₀ : V) (u₀ : Fin 3 → V) (H₀ : Set V)
    (hu : ∀ i, Orthonormal ℝ (u i)) (hHm : ∀ i, MeasurableSet (H i))
    (hHU : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hu₀ : Orthonormal ℝ u₀) (hH₀m : MeasurableSet H₀) (hH₀ : H₀ ⊆ prism a b c₀ u₀)
    (hdense₀ : O lam * μ (prism a b c₀ u₀) ≤ μ H₀)
    (hcover : H₀ ⊆ ⋃ i, H i)
    (hangle : ∀ i, θ ≤ pd (u i 0) (u₀ 0) ∧ pd (u i 0) (u₀ 0) ≤ B * θ) :
    O ((lam / 16000) ^ 2 * h ^ 2 * θ * b ^ 2 /
      (52428800000000 * (((128 * B + 1) ^ 4 : ℕ) : ℝ) * (1 + Real.log (b / a)))) ≤
      μ ({p | |inner ℝ (u₀ 0) (p - c₀)| ≤ 3 * a + (B * θ) * b} ∩
        (cTube b c₀ u₀ ∩ ⋃ i, H i)) := by
  obtain ⟨Z, _, hZH, hmass, hreg⟩ := prism_regular_subshading hlam.le (ha.trans_le hab)
    c₀ u₀ hu₀ H₀ hH₀m hH₀ hdense₀
  have hdenseZ : O (lam / 16000) * μ (prism a b c₀ u₀) ≤ μ Z := by
    calc
      _ ≤ ((1 / 2 : ℝ≥0∞) * O lam) * μ (prism a b c₀ u₀) := by
        apply mul_le_mul' _ le_rfl
        have he : (1 / 2 : ℝ≥0∞) = O (1 / 2 : ℝ) := by
          norm_num [O, ENNReal.ofReal_div_of_pos]
        rw [he, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        apply ENNReal.ofReal_le_ofReal
        linarith
      _ = (1 / 2 : ℝ≥0∞) * (O lam * μ (prism a b c₀ u₀)) := mul_assoc _ _ _
      _ ≤ (1 / 2 : ℝ≥0∞) * μ H₀ := mul_le_mul' le_rfl hdense₀
      _ ≤ μ Z := hmass
  exact angular_global_filling hn hB ha hab hb hh (by positivity) hθ hθ1
    c u H c₀ u₀ Z hu hHm hHU hregular hu₀ (hZH.trans hH₀) hdenseZ hreg (hZH.trans hcover) hangle

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
