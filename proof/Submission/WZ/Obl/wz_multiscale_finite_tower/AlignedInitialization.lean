-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.AlignedInitialization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AxisShiftCounts
import Submission.WZ.Obl.wz_multiscale_finite_tower.ScalarAlignment
import Submission.WZ.Obl.wz_multiscale_finite_tower.Regularization
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

set_option maxHeartbeats 800000

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (doubled SlabBound convexExpansionLoss)

lemma shading_axis_shift_half {d a b lam : ℝ} (hd : 0 < d) (hdb : d ≤ b)
    (hb1 : b ≤ 1) (ha : |a| ≤ b) (hlam : 0 ≤ lam) (hsmall : 1536 * b ≤ lam)
    (x v : Space) (hv : ‖v‖ = 1) {Y : Set Space} (hY : Y ⊆ Tube d x v)
    (hden : ENNReal.ofReal (lam * d ^ 2) ≤ volume Y) :
    (1 / 2 : ℝ≥0∞) * volume Y ≤ volume (Y ∩ Tube d (x + a • v) v) ∧
      ENNReal.ofReal (lam / 2 * d ^ 2) ≤ volume (Y ∩ Tube d (x + a • v) v) := by
  let Z := Y ∩ Tube d (x + a • v) v
  have hb : 0 < b := hd.trans_le hdb
  have hYfin : volume Y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((measure_mono hY).trans (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper
      hd.le (hdb.trans hb1) x v hv))
  have hZfin : volume Z ≠ ⊤ := ne_top_of_le_ne_top hYfin (measure_mono inter_subset_left)
  have hlow : lam * d ^ 2 ≤ (volume Y).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hYfin).mp hden
  have hm := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hZfin, ENNReal.ofReal_ne_top⟩)
    (shading_axis_shift_loss hd hdb hb1 ha x v hv hY)
  rw [ENNReal.toReal_add hZfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 768 * b * d ^ 2)] at hm
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (sq_nonneg d)
  constructor
  · apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num) hYfin) hZfin).mp
    rw [ENNReal.toReal_mul]
    norm_num
    dsimp [Z] at hZfin ⊢
    linarith
  · apply (ENNReal.ofReal_le_iff_le_toReal hZfin).mpr
    linarith

/-- Data used at the leaves of the geometric induction. Essential separation is
only needed when converting the finished hierarchy to the final refinement. -/
structure AlignedFamily (d lam K L : ℝ) (u : Space) (h : ℝ) (n : ℕ)
    (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop where
  nonempty : 0 < n
  unit : ∀ i, ‖v i‖ = 1
  ball : ∀ i, Tube d (x i) (v i) ⊆ Metric.ball 0 1
  measurable : ∀ i, MeasurableSet (Y i)
  shading : ∀ i, Y i ⊆ Tube d (x i) (v i)
  density : ∀ i, ENNReal.ofReal (lam * d ^ 2) ≤ volume (Y i)
  count : KatzTao d K n x v
  slab : SlabBound (doubled 1 (- (1 / 2 : ℝ) • u) u) L
    (fun _ : Fin n => True) (fun i => Tube d (x i) (v i))
  root_unit : ‖u‖ = 1
  direction_cap : ∀ i, ‖v i - u‖ ≤ 1 / 10
  aligned : ∀ i, inner ℝ (v i) (axisMidpoint (x i) (v i)) = h
  midpoint : ∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 7 / 8

lemma AlignedFamily.mono {d lam lam' K K' L L' h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : AlignedFamily d lam K L u h n x v Y)
    (hlam : lam' ≤ lam) (hK : K ≤ K') (hL : L ≤ L') :
    AlignedFamily d lam' K' L' u h n x v Y := by
  refine ⟨hF.nonempty, hF.unit, hF.ball, hF.measurable, hF.shading, ?_,
    hF.count.mono hK, WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slabBound_mono hL hF.slab,
    hF.root_unit, hF.direction_cap, hF.aligned, hF.midpoint⟩
  intro i
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlam (sq_nonneg d))).trans (hF.density i)

lemma AlignedFamily.mass_le {d lam K L h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hF : AlignedFamily d lam K L u h n x v Y) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (∑ i, volume (Y i)) ≤ ENNReal.ofReal (56 * n * d ^ 2) := by
  calc
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (56 * d ^ 2) := Finset.sum_le_sum fun i _ =>
      (measure_mono (hF.shading i)).trans
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hd hd1 _ _ (hF.unit i))
    _ = ENNReal.ofReal (n * (56 * d ^ 2)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ = _ := by congr 1; ring

theorem aligned_refinement_at_width : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {d η M L b : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space},
      0 < d → d ≤ b → b ≤ 1 / 2 → 3072 * b ≤ d ^ η → 0 ≤ M → 0 ≤ L →
      Admissible d η M L n x v Y →
    ∃ (m : ℕ) (X V : Fin m → Space) (Z : Fin m → Set Space) (u : Space) (h : ℝ),
      AlignedFamily d (d ^ η / 4) (M * convexExpansionLoss 2)
        (512000000 * L * n / m) u h m X V Z ∧ m ≤ n ∧
      (⋃ i, Z i) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (b / (16 * C)) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) := by
  classical
  obtain ⟨C, hC, hcap⟩ := direction_cap_selection
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C, hC, ?_⟩
  intro d η M L b n x v Y hd hdb hb1 hsmall hM hL hA
  have hb : 0 < b := hd.trans_le hdb
  have hb1' : b ≤ 1 := by linarith
  obtain ⟨U, hU, hUmass, hUdense⟩ := hA.heavy_indices hd
  have hUpos : 0 < ∑ i ∈ U, volume (Y i) :=
    (ENNReal.mul_pos (by norm_num) (hA.mass_pos hd).ne').trans_le hUmass
  obtain ⟨V, hVU, hV, u, hu, hVmass, hVdir⟩ :=
    hcap U v (fun i => (hA.2.1 i).1) (fun i => volume (Y i)) hUpos
  have hVpos : 0 < ∑ i ∈ V, volume (Y i) := by
    by_contra hn
    have he : (∑ i ∈ V, volume (Y i)) = 0 := le_antisymm (le_of_not_gt hn) bot_le
    rw [he, mul_zero] at hVmass
    exact (not_lt_of_ge hVmass) hUpos
  let scalar := fun i => inner ℝ (v i) (axisMidpoint (x i) (v i))
  have hscalar (i : Fin n) : |scalar i| ≤ 1 := by
    have hm := midpoint_bound_of_unit_ball hd (hA.2.1 i).1 (hA.2.1 i).2.1
    have hh := abs_real_inner_le_norm (v i) (axisMidpoint (x i) (v i))
    rw [(hA.2.1 i).1, one_mul] at hh
    exact hh.trans (by linarith)
  obtain ⟨S, hSV, hS, h, hSmass, hSalign⟩ := select_inward_scalar hb hb1' V scalar hscalar
    (fun i => volume (Y i)) hVpos
  let a : Fin n → ℝ := fun i => if i ∈ S then h - scalar i else 0
  let X : Fin n → Space := fun i => x i + a i • v i
  let Z : Fin n → Set Space := fun i => Y i ∩ Tube d (X i) (v i)
  have ha (i : Fin n) : |a i| ≤ b := by
    by_cases hi : i ∈ S
    · simpa only [a, if_pos hi] using (hSalign i hi).2
    · simp only [a, if_neg hi, abs_zero]
      exact hb.le
  have hball (i : Fin n) : Tube d (X i) (v i) ⊆ ball 0 1 := by
    by_cases hi : i ∈ S
    · simpa only [X, a, if_pos hi, scalar] using
        inward_axis_shift (hA.2.1 i).1 (hSalign i hi).1 (hA.2.1 i).2.1
    · simpa only [X, a, if_neg hi, zero_smul, add_zero] using (hA.2.1 i).2.1
  have hhalf (i : Fin n) (hi : i ∈ S) : (1 / 2 : ℝ≥0∞) * volume (Y i) ≤ volume (Z i) ∧
      ENNReal.ofReal (d ^ η / 4 * d ^ 2) ≤ volume (Z i) := by
    have hh := shading_axis_shift_half hd hdb hb1' (ha i) (by positivity : 0 ≤ d ^ η / 2)
      (by linarith : 1536 * b ≤ d ^ η / 2) (x i) (v i) (hA.2.1 i).1 (hA.2.1 i).2.2.2
      (by convert hUdense i (hVU (hSV hi)) using 1 <;> congr 1 <;> ring)
    refine ⟨hh.1, ?_⟩
    convert hh.2 using 1
    congr 1
    ring
  have hZmass : (1 / 2 : ℝ≥0∞) * (∑ i ∈ S, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => (hhalf i hi).1)
  have hCinv : ENNReal.ofReal C⁻¹ * ENNReal.ofReal C = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hC0.le), inv_mul_cancel₀ hC0.ne', ENNReal.ofReal_one]
  have hVmass' : ENNReal.ofReal C⁻¹ * (∑ i ∈ U, volume (Y i)) ≤ ∑ i ∈ V, volume (Y i) := by
    have hh := mul_le_mul' (a := ENNReal.ofReal C⁻¹) le_rfl hVmass
    rwa [← mul_assoc, hCinv, one_mul] at hh
  have hmass : ENNReal.ofReal (b / (16 * C)) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Z i) := by
    have he : b / (16 * C) = (1 / 2 : ℝ) * (b / 4) * (C⁻¹ * (1 / 2)) := by
      field_simp
      ring
    have hhalfR : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    calc
      _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (b / 4) *
          (ENNReal.ofReal C⁻¹ * ((1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i)))) := by
        rw [he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (inv_nonneg.mpr hC0.le), hhalfR]
        ac_rfl
      _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (b / 4) *
          (ENNReal.ofReal C⁻¹ * ∑ i ∈ U, volume (Y i))) := by gcongr
      _ ≤ (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (b / 4) * ∑ i ∈ V, volume (Y i)) := by gcongr
      _ ≤ (1 / 2 : ℝ≥0∞) * ∑ i ∈ S, volume (Y i) := mul_le_mul' le_rfl hSmass
      _ ≤ _ := hZmass
  let g := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate S
  have hg := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_injective S
  have hgin (i) : g i ∈ S := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem S i
  have hm : 0 < S.card := Finset.card_pos.mpr hS
  have hm0 : (S.card : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hcount := (hA.2.2.2.2.1.longitudinal_shift hd hM a (fun i => (ha i).trans hb1) hball).comp g hg
  have hslab := hA.2.2.2.2.2.longitudinal_root_shift hd hL
    (fun i => (hA.2.1 i).2.1) a (fun i => (ha i).trans hb1) hball u hu
  have hslab' := slabBound_comp hslab g hg
    (show 512000000 * L * n ≤ (512000000 * L * n / S.card) * S.card by
      rw [div_mul_cancel₀ _ hm0])
  refine ⟨S.card, X ∘ g, v ∘ g, Z ∘ g, u, h, ?_, ?_, ?_, ?_⟩
  · refine ⟨hm, fun i => (hA.2.1 (g i)).1, fun i => hball (g i),
      fun i => (hA.2.1 (g i)).2.2.1.inter isOpen_thickening.measurableSet,
      fun i => inter_subset_right, fun i => (hhalf (g i) (hgin i)).2,
      hcount, hslab', hu, fun i => hVdir (g i) (hSV (hgin i)), ?_, ?_⟩
    · intro i
      have hvv : inner ℝ (v (g i)) (v (g i)) = 1 := by
        rw [real_inner_self_eq_norm_sq, (hA.2.1 (g i)).1]
        norm_num
      have he : axisMidpoint (X (g i)) (v (g i)) =
          axisMidpoint (x (g i)) (v (g i)) + a (g i) • v (g i) := by
        dsimp [axisMidpoint, X]
        module
      change inner ℝ (v (g i)) (axisMidpoint (X (g i)) (v (g i))) = h
      rw [he, inner_add_right, inner_smul_right, hvv, mul_one]
      simp only [a, if_pos (hgin i), scalar]
      ring
    · intro i
      exact midpoint_bound_of_unit_ball hd (hA.2.1 (g i)).1 (hball (g i))
  · simpa only [Fintype.card_fin] using Finset.card_le_univ S
  · exact iUnion_subset fun i => subset_iUnion_of_subset (g i) inter_subset_left
  · change ENNReal.ofReal (b / (16 * C)) * (∑ i, volume (Y i)) ≤
      ∑ i : Fin S.card, volume (Z (g i))
    rw [show (∑ i : Fin S.card, volume (Z (g i))) = ∑ i ∈ S, volume (Z i) from
      WangZahlLot.Obl.wz_tower_balanced_refinement.sum_enumerate S (fun i => volume (Z i))]
    exact hmass

end WangZahlLot.Obl.wz_multiscale_finite_tower
