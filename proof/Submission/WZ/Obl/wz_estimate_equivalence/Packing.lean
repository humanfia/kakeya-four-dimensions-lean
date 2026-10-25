-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Packing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_estimate_equivalence

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya

/-- A fixed contraction of a tube lies in any tube with sufficiently close parameters. -/
theorem contracted_tube_subset {δ : ℝ} (hδ : 0 < δ) {x v x' v' : Space}
    (hx : ‖x - x'‖ ≤ δ / 40) (hv : ‖v - v'‖ ≤ δ / 40) :
    AffineMap.homothety x (9 / 10 : ℝ) '' thickening δ (segment ℝ x (x + v)) ⊆
      thickening δ (segment ℝ x' (x' + v')) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  simp only [add_sub_cancel_left] at hyz
  apply mem_thickening_iff.mpr
  refine ⟨x' + ((9 / 10 : ℝ) * t) • v', ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(9 / 10 : ℝ) * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simp
  · rw [dist_eq_norm] at hyz ⊢
    have heq : AffineMap.homothety x (9 / 10 : ℝ) y -
        (x' + ((9 / 10 : ℝ) * t) • v') =
        (9 / 10 : ℝ) • (y - (x + t • v)) + (x - x') +
          ((9 / 10 : ℝ) * t) • (v - v') := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      module
    rw [heq]
    calc
      ‖(9 / 10 : ℝ) • (y - (x + t • v)) + (x - x') +
          ((9 / 10 : ℝ) * t) • (v - v')‖ ≤
          ‖(9 / 10 : ℝ) • (y - (x + t • v))‖ + ‖x - x'‖ +
            ‖((9 / 10 : ℝ) * t) • (v - v')‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (9 / 10 : ℝ) * ‖y - (x + t • v)‖ + δ / 40 + δ / 40 := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 9 / 10 * t)]
        gcongr
        calc (9 / 10 : ℝ) * t * ‖v - v'‖ ≤ 1 * (δ / 40) := by
               apply mul_le_mul (by linarith [ht.1, ht.2]) hv (norm_nonneg _) zero_le_one
             _ = δ / 40 := one_mul _
      _ < δ := by linarith

/-- The half-overlap condition forces separation of the six tube parameters. -/
theorem tube_parameters_separated {δ : ℝ} (hδ : 0 < δ) {x v x' v' : Space}
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ ball (0 : Space) 1)
    (hsep : volume (thickening δ (segment ℝ x (x + v)) ∩
        thickening δ (segment ℝ x' (x' + v'))) ≤
      (1 / 2 : ENNReal) * volume (thickening δ (segment ℝ x (x + v)))) :
    δ / 40 < ‖(x, v) - (x', v')‖ := by
  by_contra! hclose
  have hx : ‖x - x'‖ ≤ δ / 40 := (norm_fst_le ((x, v) - (x', v'))).trans hclose
  have hv : ‖v - v'‖ ≤ δ / 40 := (norm_snd_le ((x, v) - (x', v'))).trans hclose
  have hsub : AffineMap.homothety x (9 / 10 : ℝ) ''
      thickening δ (segment ℝ x (x + v)) ⊆
      thickening δ (segment ℝ x (x + v)) ∩ thickening δ (segment ℝ x' (x' + v')) := by
    apply subset_inter
    · exact contracted_tube_subset hδ (by simp; positivity) (by simp; positivity)
    · exact contracted_tube_subset hδ hx hv
  have hvol := (measure_mono hsub).trans hsep
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at hvol
  have hpos : volume (thickening δ (segment ℝ x (x + v))) ≠ 0 :=
    ((measure_ball_pos volume x hδ).trans_le
      (measure_mono (ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ))).ne'
  have hfin : volume (thickening δ (segment ℝ x (x + v))) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hT)
  have hbad := (ENNReal.mul_le_mul_iff_left hpos hfin).mp hvol
  have hbad' := ENNReal.toReal_mono (by norm_num : (1 / 2 : ENNReal) ≠ ⊤) hbad
  norm_num at hbad'

/-- A coarse polynomial packing bound for essentially distinct unit tubes. -/
theorem tube_card_bound {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1 / 100)
    {n : ℕ} {x v : Fin n → Space} (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ ball (0 : Space) 1)
    (hsep : ∀ i j, i ≠ j →
      volume (thickening δ (segment ℝ (x i) (x i + v i)) ∩
        thickening δ (segment ℝ (x j) (x j + v j))) ≤
      (1 / 2 : ENNReal) * volume (thickening δ (segment ℝ (x i) (x i + v i)))) :
    (n : ℝ) * δ ^ 6 ≤ (160 : ℝ) ^ 6 := by
  let P := Space × Space
  let μ : Measure P := Measure.addHaar
  let c : Fin n → P := fun i => (x i, v i)
  let r : ℝ := δ / 80
  have hr : 0 < r := by dsimp [r]; positivity
  have hdim : Module.finrank ℝ P = 6 := by
    simp [P, Module.finrank_prod]
  have hc : ∀ i, ‖c i‖ ≤ 1 := by
    intro i
    have hx : ‖x i‖ < 1 := by
      have hi := hT i (self_subset_thickening hδ _ (left_mem_segment ℝ (x i) (x i + v i)))
      simpa only [mem_ball, dist_zero_right] using hi
    change max ‖x i‖ ‖v i‖ ≤ 1
    exact max_le hx.le (hv i).le
  have hd : Pairwise (fun i j => Disjoint (ball (c i) r) (ball (c j) r)) := by
    intro i j hij
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have h := tube_parameters_separated hδ (hT i) (hsep i j hij)
    dsimp [c, r]
    linarith
  have hsub : (⋃ i, ball (c i) r) ⊆ ball (0 : P) 2 := by
    apply iUnion_subset
    intro i
    apply ball_subset_ball'
    rw [dist_zero_right]
    have := hc i
    dsimp [r]
    linarith
  have hμpos : μ (ball (0 : P) 1) ≠ 0 := (measure_ball_pos μ _ zero_lt_one).ne'
  have hμfin : μ (ball (0 : P) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hvol : (n : ENNReal) * ENNReal.ofReal (r ^ 6) * μ (ball (0 : P) 1) ≤
      ENNReal.ofReal ((2 : ℝ) ^ 6) * μ (ball (0 : P) 1) := by
    calc
      (n : ENNReal) * ENNReal.ofReal (r ^ 6) * μ (ball (0 : P) 1) =
          μ (⋃ i, ball (c i) r) := by
        rw [measure_iUnion hd (fun _ => measurableSet_ball)]
        simp_rw [Measure.addHaar_ball_of_pos μ _ hr, hdim]
        simp [mul_assoc]
      _ ≤ μ (ball (0 : P) 2) := measure_mono hsub
      _ = _ := by rw [Measure.addHaar_ball_of_pos μ _ (by norm_num), hdim]
  have hcancel := (ENNReal.mul_le_mul_iff_left hμpos hμfin).mp hvol
  have hreal := ENNReal.toReal_mono (by finiteness) hcancel
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 6),
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2 ^ 6)] at hreal
  dsimp [r] at hreal
  norm_num [div_pow] at hreal ⊢
  linarith

end WangZahlLot.Obl.wz_estimate_equivalence
