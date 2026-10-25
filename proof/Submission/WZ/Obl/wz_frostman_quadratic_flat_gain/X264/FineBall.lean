-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.FineBall.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatFineEstimate
import Submission.WZ.Obl.wz_flat_factored_improvement.PacketNumerics
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.LevelOne
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file FineBall.lean), namespace renamed.

/-!
# Level i from the accepted o065

The tube estimate `E` gives, through o065's `body_estimate_of_tube_estimate` and
`flat_fine_estimate`, the fine estimate for the tubes of one prism, in the normalization of
`FinePrismEstimate` (tubes in the unit ball, `a ≤ 1/100`).
-/

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

noncomputable section

/-- The frozen tube estimate in o065's bundled form. -/
theorem tubeEstimate_of_estimateE {σ ω : ℝ} (hE : EstimateE σ ω) :
    WangZahlLot.Obl.wz_flat_factored_improvement.TubeEstimate σ ω := by
  intro ε hε
  obtain ⟨A, hA, η, hη, h⟩ := hE ε hε
  refine ⟨A, hA, η, hη, ?_⟩
  intro δ hδ hδ100 m l hm hl n x v Y hAdm
  obtain ⟨hn, hfamily, hsep, hsum, hconv, hslab⟩ := hAdm
  exact h δ hδ hδ100 m l hm hl n x v Y hn
    (fun i => (hfamily i).1) (fun i => (hfamily i).2.1) hsep
    (fun i => (hfamily i).2.2.1) (fun i => (hfamily i).2.2.2) hsum hconv hslab

/-- The frame of a prism as an affine isometry of the standard coordinates. -/
def frameIso {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c : Space) :
    AffineIsometryEquiv ℝ Space Space :=
  (orthonormalFrame he).repr.symm.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ Space c)

lemma frameIso_apply {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c p : Space) :
    frameIso he c p = c + (orthonormalFrame he).repr.symm p := by
  simp [frameIso, vadd_eq_add]

lemma frameIso_frameCoord {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃]) (c y : Space) :
    frameIso he c (frameCoord he c y) = y := by
  rw [frameIso_apply, frameCoord_apply, LinearIsometryEquiv.symm_apply_apply]
  abel

/-- A prism of half length one lies in the image of the standard prism of half length two. -/
lemma prism_subset_frameIso_image {e₁ e₂ e₃ : Space} (he : Orthonormal ℝ ![e₁, e₂, e₃])
    (a b : ℝ) (c : Space) :
    prism a b c e₁ e₂ e₃ ⊆
      frameIso he c '' WangZahlLot.Obl.wz_flat_factored_improvement.StandardPrism a b := by
  intro y hy
  have hbox := frameCoord_image_prism_subset he a b c ⟨y, hy, rfl⟩
  simp only [stdBox, Set.mem_ofPred_eq] at hbox
  refine ⟨frameCoord he c y, ⟨hbox.1, hbox.2.1, hbox.2.2.trans (by norm_num)⟩, ?_⟩
  exact frameIso_frameCoord he c y

/-- The fine estimate, restricted to tubes in the unit ball and to `a ≤ 1/100`. -/
abbrev FinePrismEstimateBall (σ ω : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ a b : ℝ, 0 < δ → δ ≤ d₀ →
  δ ≤ a → a ≤ b → b ≤ 1 → a ≤ 1 / 100 →
  ∀ (c e₁ e₂ e₃ : Space), Orthonormal ℝ ![e₁, e₂, e₃] →
  ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
  0 < n → (∀ i, ‖v i‖ = 1) →
  (∀ i, tube δ (x i) (v i) ⊆ ball 0 1) →
  (∀ i, tube δ (x i) (v i) ⊆ prism a b c e₁ e₂ e₃) →
  (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
    (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
  (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
  (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
  (∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ U}) *
      volume (prism a b c e₁ e₂ e₃) ≤
    ENNReal.ofReal (δ ^ (-η) * n) * volume U) →
  ENNReal.ofReal (A * δ ^ e * (δ / a) ^ ω *
    (n * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2)) *
      volume (prism a b c e₁ e₂ e₃) ≤ volume (⋃ i, Y i)

lemma fine_weight_identity {σ δ a b N : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b)
    (hN : 0 < N) :
    (N * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2) * (a * b) =
      (a * b) ^ (1 - σ) * N ^ (σ / 2) * δ ^ (2 * σ) := by
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  push_cast
  ring

set_option maxHeartbeats 800000 in
theorem fine_prism_estimate_ball {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : EstimateE σ ω) : FinePrismEstimateBall σ ω := by
  have hB := WangZahlLot.Obl.wz_flat_factored_improvement.body_estimate_of_tube_estimate
    hσ hσhalf hω (tubeEstimate_of_estimateE hE)
  intro e he
  obtain ⟨A, η₀, d, hA, hη₀, hd, hd100, H⟩ :=
    WangZahlLot.Obl.wz_flat_factored_improvement.flat_fine_estimate hσ hB
      (by positivity : 0 < e / 2)
  obtain ⟨dn, hdn, hdn100, Hn⟩ :=
    WangZahlLot.Obl.wz_flat_factored_improvement.tube_number_power_bound
  let η := min η₀ (e / 2)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨A / 8, by positivity, η, hη, min d dn, lt_min hd hdn, ?_⟩
  intro δ a b hδ hδd hδa hab hb1 ha100 c e₁ e₂ e₃ hframe n x v Y hn hv hball hP hover hYm hYT
    hden hFB
  have hδ1 : δ ≤ 1 := (hδd.trans (min_le_left _ _)).trans (hd100.trans (by norm_num))
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmax : (n : ℝ) ≤ δ ^ (-100 : ℝ) :=
    (Hn δ hδ (hδd.trans (min_le_right _ _)) n x v hv hball hover).trans
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))
  let L : ℝ := δ ^ (-η)
  have hL : 1 ≤ L := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hvolP : volume (prism a b c e₁ e₂ e₃) = ENNReal.ofReal (8 * a * b) :=
    prism_volume ha.le hb.le c e₁ e₂ e₃ hframe
  have hraw : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (L * n / (a * b)) * volume Q := by
    intro Q hQ
    have hh := hFB Q hQ
    rw [hvolP] at hh
    have hpos : (0 : ℝ) < 8 * a * b := by positivity
    calc
      ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ Q} : ℝ) =
          ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ Q} : ℝ) *
            ENNReal.ofReal (8 * a * b) * ENNReal.ofReal (8 * a * b)⁻¹ := by
        rw [mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
          ENNReal.ofReal_one, mul_one]
      _ ≤ ENNReal.ofReal (δ ^ (-η) * n) * volume Q * ENNReal.ofReal (8 * a * b)⁻¹ :=
        mul_le_mul' hh le_rfl
      _ = ENNReal.ofReal (δ ^ (-η) * n * (8 * a * b)⁻¹) * volume Q := by
        rw [ENNReal.ofReal_mul (p := δ ^ (-η) * n) (q := (8 * a * b)⁻¹) (by positivity)]
        ring
      _ ≤ _ := by
        apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        dsimp [L]
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        nlinarith [mul_pos ha hb]
  have hden' : ∀ i, ENNReal.ofReal (δ ^ η₀ * δ ^ 2) ≤ volume (Y i) := fun i =>
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (min_le_left _ _)) (sq_nonneg δ))).trans (hden i)
  have hbound := H δ a b L hδ (hδd.trans (min_le_left _ _)) hδa hab (hb1.trans (by norm_num))
    ha100 hL (frameIso hframe c) n x v Y hn hnmax hv hball
    (fun i => (hP i).trans (prism_subset_frameIso_image hframe a b c)) hover hYm hYT hden' hraw
  rw [hvolP, ← ENNReal.ofReal_mul (by
    have : 0 ≤ (n * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2) := by positivity
    positivity)]
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
  have hid := fine_weight_identity (σ := σ) hδ ha hb hn'
  have hLinv : L⁻¹ = δ ^ η := by
    dsimp [L]
    rw [Real.rpow_neg hδ.le, inv_inv]
  have hpow : δ ^ e ≤ δ ^ (e / 2) * δ ^ η := by
    rw [← Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by
      have := min_le_right η₀ (e / 2)
      dsimp [η] at *
      linarith)
  calc
    A / 8 * δ ^ e * (δ / a) ^ ω * (n * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2) * (8 * a * b)
        = A * δ ^ e * (δ / a) ^ ω * ((n * (δ ^ 2 / (a * b)) ^ 2) ^ (σ / 2) * (a * b)) := by
          ring
    _ = A * δ ^ e * (δ / a) ^ ω * ((a * b) ^ (1 - σ) * n ^ (σ / 2) * δ ^ (2 * σ)) := by
          rw [hid]
    _ ≤ A * (δ ^ (e / 2) * δ ^ η) * (δ / a) ^ ω * ((a * b) ^ (1 - σ) * n ^ (σ / 2) *
          δ ^ (2 * σ)) := by gcongr
    _ = A * δ ^ (e / 2) * (δ / a) ^ ω * L⁻¹ * (a * b) ^ (1 - σ) * (n : ℝ) ^ (σ / 2) *
          δ ^ (2 * σ) := by rw [hLinv]; ring

end

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
