-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.LocalThickening.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PlanarMoment
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Thickening
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.PrismBalls
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file LocalThickening.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

/-- The planar thickening input of Proposition 5.1, with independent quantitative density
and Frostman losses absorbed into a prescribed positive power of delta. -/
theorem local_prism_thickening (e : ℝ) (he : 0 < e) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 1 →
    ∀ (c e₁ e₂ e₃ : Space), Orthonormal ℝ ![e₁, e₂, e₃] →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), 0 < n →
      (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ prism a b c e₁ e₂ e₃) →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
      (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) *
          volume (prism a b c e₁ e₂ e₃) ≤ ENNReal.ofReal (δ ^ (-η) * n) * volume U) →
      ENNReal.ofReal (A * δ ^ e) * volume (prism a b c e₁ e₂ e₃) ≤
        volume (prism a b c e₁ e₂ e₃ ∩ thickening a (⋃ i, Y i)) := by
  let q := e / 4
  let η := e / 8
  have hq : 0 < q := by dsimp [q]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C, hC, hmoment⟩ := planar_shading_moment q hq
  let M : ℝ := (128000 : ℝ) ^ 2
  have hM : 0 < M := by norm_num [M]
  let A := min (1 / 512000 : ℝ) (1 / (8 * M * C))
  have hA : 0 < A := lt_min (by norm_num) (by positivity)
  have hA1 : A ≤ 1 / 512000 := min_le_left _ _
  have hA2 : 8 * A * M * C ≤ 1 := by
    have h : A * (8 * M * C) ≤ 1 :=
      (le_div_iff₀ (by positivity : 0 < 8 * M * C)).mp (min_le_right _ _ : A ≤ 1 / (8 * M * C))
    nlinarith only [h]
  refine ⟨A, hA, η, hη, ?_⟩
  intro δ hδ hδ1 a b hδa hab hb c e₁ e₂ e₃ hframe n x v Y hn hv hTP hYm hYT hden hcount
  have ha : 0 < a := hδ.trans_le hδa
  have hb0 : 0 < b := ha.trans_le hab
  have ha1 : a ≤ 1 := hab.trans hb
  let P := prism a b c e₁ e₂ e₃
  let E := P ∩ thickening a (⋃ i, Y i)
  let Z := fun i => P ∩ thickening a (Y i)
  let lam := δ ^ η
  let D := δ ^ (-η)
  have hlam : 0 < lam := Real.rpow_pos_of_pos hδ _
  have hD : 0 < D := Real.rpow_pos_of_pos hδ _
  have hPm : MeasurableSet P := (prism_isClosed a b c e₁ e₂ e₃).measurableSet
  have hEm : MeasurableSet E := hPm.inter isOpen_thickening.measurableSet
  have hEfin : volume E ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := volume P)
    · rw [prism_volume ha.le hb0.le c e₁ e₂ e₃ hframe]
      exact ENNReal.ofReal_ne_top
    · exact measure_mono Set.inter_subset_left
  have hZm : ∀ i, MeasurableSet (Z i) := fun _ => hPm.inter isOpen_thickening.measurableSet
  have hZE : ∀ i, Z i ⊆ E := fun i =>
    Set.inter_subset_inter_right _ (thickening_subset_of_subset _ (Set.subset_iUnion Y i))
  have hZden : ∀ i, ENNReal.ofReal (lam / 32000 * a ^ 2) ≤ volume (Z i) := by
    intro i
    have h := tube_shading_thickening hδ ha hlam.le (by norm_num : (0 : ℝ) ≤ 1 / 4000)
      hPm (hYm i) (hv i) (hYT i) (hden i) (by
        intro y hy
        have h := prism_inter_ball_lower ha hab hb hframe (hTP i (hYT i hy))
        convert h using 1
        congr 1
        ring)
    convert h using 1
    congr 1
    ring
  have hZT : ∀ i, Z i ⊆ tube (2 * a) (x i) (v i) := by
    intro i p hp
    obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.mp hp.2
    obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp (hYT i hy)
    refine mem_thickening_iff.mpr ⟨z, hz, ?_⟩
    calc
      dist p z ≤ dist p y + dist y z := dist_triangle _ _ _
      _ < a + δ := add_lt_add hpy hyz
      _ ≤ 2 * a := by linarith
  have hfinal : 8 * A * δ ^ e * a * b ≤ (volume E).toReal := by
    by_cases hsmall : a ≤ 1 / 2
    · have hrow := hmoment a b δ (2 * a) D (lam / 128000) ha hab hb
        (by linarith) (by positivity) (by linarith) hD (by positivity)
        n x v c e₁ e₂ e₃ hn hframe hv hTP hcount Z E hEm hEfin hZm hZT hZE (by
          intro i
          convert hZden i using 1
          congr 1
          ring)
      have hpow : (2 * a) ^ (-q) ≤ a ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos ha (by linarith) (by linarith)
      have hrow' : lam ^ 2 * a * b ≤ (M * C * a ^ (-q) * D) * (volume E).toReal := by
        have hh := mul_le_mul_of_nonneg_right hrow hM.le
        have hh' : 2 * lam ^ 2 * a * b ≤ (M * C * (2 * a) ^ (-q) * D) * (volume E).toReal := by
          convert hh using 1 <;> dsimp [M] <;> ring
        calc
          _ ≤ 2 * lam ^ 2 * a * b := by nlinarith [mul_nonneg (sq_nonneg lam) (mul_nonneg ha.le hb0.le)]
          _ ≤ _ := hh'
          _ ≤ _ := by gcongr
      have hpower : δ ^ e * a ^ (-q) * D ≤ lam ^ 2 := by
        calc
          _ ≤ δ ^ e * δ ^ (-q) * δ ^ (-η) := by
            dsimp [D]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_nonpos hδ hδa (by linarith))
                (Real.rpow_nonneg hδ.le e)) (Real.rpow_nonneg hδ.le (-η))
          _ = δ ^ (e - q - η) := by
            rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
            congr 1
          _ ≤ δ ^ (2 * η) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [q, η]; linarith)
          _ = lam ^ 2 := by
            dsimp [lam]
            rw [mul_comm]
            exact Real.rpow_mul_natCast hδ.le η 2
      apply (mul_le_mul_iff_right₀ (by positivity : 0 < M * C * a ^ (-q) * D)).mp
      calc
        (M * C * a ^ (-q) * D) * (8 * A * δ ^ e * a * b) =
            (8 * A * M * C) * (δ ^ e * a ^ (-q) * D) * (a * b) := by ring
        _ ≤ 1 * lam ^ 2 * (a * b) := by gcongr
        _ = lam ^ 2 * a * b := by ring
        _ ≤ _ := hrow'
    · have hlarge : 1 / 2 ≤ a := (le_of_not_ge hsmall)
      have hpow : δ ^ e ≤ lam := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [η]; linarith)
      have hz := (hZden ⟨0, hn⟩).trans (measure_mono (hZE ⟨0, hn⟩))
      have hzr := ENNReal.toReal_mono hEfin hz
      rw [ENNReal.toReal_ofReal (by positivity)] at hzr
      apply le_trans _ hzr
      calc
        8 * A * δ ^ e * a * b ≤ 8 * (1 / 512000) * lam * a * (2 * a) := by gcongr; linarith
        _ = lam / 32000 * a ^ 2 := by ring
  rw [prism_volume ha.le hb0.le c e₁ e₂ e₃ hframe,
    ← ENNReal.ofReal_mul (by positivity)]
  change ENNReal.ofReal _ ≤ volume E
  rw [← ENNReal.ofReal_toReal hEfin]
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [hfinal]

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
