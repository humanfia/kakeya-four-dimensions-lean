-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.FlatFineEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatBodies
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyEstimate

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube closedTube_volume_bounds tube_subset_closedTube tube_convex)

noncomputable def fineBodyConstant (σ u A : ℝ) : ℝ :=
  A * (384 : ℝ) ^ (-1 + 3 / 2 * σ) * (1024 : ℝ) ^ (-u) *
    (1024 : ℝ) ^ (-σ) * (1000 : ℝ) ^ (-σ) * (128 : ℝ) ^ (σ / 2)

theorem fineBodyConstant_pos {σ u A : ℝ} (hA : 0 < A) : 0 < fineBodyConstant σ u A := by
  unfold fineBodyConstant
  positivity

theorem fine_body_factorization {σ u ε A δ a b L n : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (hn : 0 < n) :
    A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (δ / (1024 * a)) ^ u *
        bodyWeight σ ((1 / (128 * a * b)) * δ ^ 2)
          (384 * (L * n / (a * b)) * δ ^ 2) (1024 * L) 1000 n =
      (1 / (128 * a * b)) * (fineBodyConstant σ u A * δ ^ ε * (δ / a) ^ u *
        L ^ (-1 + σ / 2) * (a * b) ^ (1 - σ) * n ^ (σ / 2) * δ ^ (2 * σ)) := by
  unfold bodyWeight fineBodyConstant
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_inv,
    Real.log_rpow, Real.log_pow, Real.log_one]
  ring

theorem raw_tube_count_lower {δ K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    {n : ℕ} (hn : 0 < n) (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hc : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) ≤ ENNReal.ofReal K * volume Q) :
    1 ≤ 384 * K * δ ^ 2 := by
  let i : Fin n := ⟨0, hn⟩
  have hcard : 1 ≤ Set.ncard {j | Tube δ (x j) (v j) ⊆ Tube δ (x i) (v i)} :=
    Nat.succ_le_iff.mpr (Set.ncard_pos (Set.toFinite _) |>.mpr ⟨i, Subset.rfl⟩)
  have hh : ENNReal.ofReal 1 ≤ ENNReal.ofReal (384 * K * δ ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (Set.ncard {j | Tube δ (x j) (v j) ⊆ Tube δ (x i) (v i)} : ℝ) :=
        ENNReal.ofReal_le_ofReal (by exact_mod_cast hcard)
      _ ≤ ENNReal.ofReal K * volume (Tube δ (x i) (v i)) := hc _ (tube_convex _ _ _)
      _ ≤ ENNReal.ofReal K * ENNReal.ofReal (384 * δ ^ 2) := mul_le_mul' le_rfl
        (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1 (x i) (v i) (hv i))
      _ = _ := by rw [← ENNReal.ofReal_mul hK]; congr 1; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

set_option maxHeartbeats 600000 in
/-- The fine use of the body estimate, with the improved middle width `delta/a`.
The relative convex coefficient costs only one power of `L`. -/
theorem flat_fine_estimate {σ u : ℝ} (hσ : 0 ≤ σ) (hF : BodyEstimate σ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A η d : ℝ, 0 < A ∧ 0 < η ∧ 0 < d ∧ d ≤ 1 / 100 ∧
    ∀ δ a b L : ℝ, 0 < δ → δ ≤ d → δ ≤ a → a ≤ b → b ≤ 2 → a ≤ 1 / 100 → 1 ≤ L →
    ∀ (e : AffineIsometryEquiv ℝ Space Space) (n : ℕ) (x v : Fin n → Space)
      (Y : Fin n → Set Space),
    0 < n → (n : ℝ) ≤ δ ^ (-100 : ℝ) → (∀ i, ‖v i‖ = 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1) →
    (∀ i, Tube δ (x i) (v i) ⊆ e '' StandardPrism a b) →
    (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ Tube δ (x i) (v i)) →
    (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
    (∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (L * n / (a * b)) * volume Q) →
    ENNReal.ofReal (A * δ ^ ε * (δ / a) ^ u * L⁻¹ *
      (a * b) ^ (1 - σ) * (n : ℝ) ^ (σ / 2) * δ ^ (2 * σ)) ≤ volume (⋃ i, Y i) := by
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := hF (ε / 2) (by positivity)
  let d := min d₀ (min (1 / 2048) ((1 / 384 : ℝ) ^ η⁻¹))
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨fineBodyConstant σ u A, η, d, fineBodyConstant_pos hA, hη, hd,
    (min_le_left _ _).trans hd₀small, ?_⟩
  intro δ a b L hδ hδd hδa hab hb2 haSmall hL e n x v Y hn hnmax hv hball hT hover hYm hYT hYden hraw
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hδsmall : δ ≤ 1 / 2048 := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδsmall.trans (by norm_num)
  have hδroot : δ ≤ (1 / 384 : ℝ) ^ η⁻¹ := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpow : δ ^ η ≤ 1 / 384 :=
    (Real.le_rpow_inv_iff_of_pos hδ.le (by norm_num) hη).mp hδroot
  have hdscale : δ ^ (2 : ℕ) ≤ d₀ :=
    (show δ ^ (2 : ℕ) ≤ δ by nlinarith).trans (hδd.trans (min_le_left _ _))
  have hinterior : δ ^ (2 : ℕ) ≤ δ / 8 := by nlinarith
  have hwidth : δ ^ (2 : ℕ) ≤ δ / (1024 * a) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hda : δ * (1024 * a) ≤ 1 := by
      have hh := mul_le_mul hδsmall haSmall ha.le (by norm_num : (0 : ℝ) ≤ 1 / 2048)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hda hδ.le]
  have hnmax' : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
    rw [← Real.rpow_natCast_mul hδ.le]
    exact hnmax.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num))
  let f := flatMap e a b ha hb
  let J := 1 / (128 * a * b)
  let K := L * n / (a * b)
  have hJ : 0 < J := by dsimp [J]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  let U := fun i => f '' closedTube δ (x i) (v i)
  let Z := fun i => f '' Y i
  have hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q := flatMap_volume e ha hb
  have hgeom : BodyGeometry U (fun i => f (x i)) (δ ^ (2 : ℕ))
      (δ / (1024 * a)) (J * δ ^ 2) :=
    flat_body_geometry hδ hδa hab haSmall hb2 hinterior e x v hv hball hT
  have hm : 1 ≤ 384 * K * δ ^ 2 := raw_tube_count_lower hδ hδ1 hK.le hn x v hv hraw
  have hconv : BodyConvexCount U (J * δ ^ 2) (K * δ ^ 2) :=
    (closedTube_convex_count hK.le x v hraw).affine_image (sq_nonneg δ) hJ f hvol
  have hconv' : BodyConvexCount U (J * δ ^ 2) (384 * K * δ ^ 2) :=
    hconv.mono_m (by nlinarith [mul_nonneg hK.le (sq_nonneg δ)])
  have hslab : BodySlabCount U (1024 * L) := by
    have huBall : ∀ i, U i ⊆ ball (0 : Space) 1 := by
      rintro i _ ⟨p, hp, rfl⟩
      exact mem_ball_zero_iff.mpr ((flatMap_prism_norm e ha hb
        (closedTube_subset_prism e (hT i) hp)).trans_lt (by norm_num))
    have hh := body_slab_of_convex_count hn (by positivity : 0 < J * δ ^ 2)
      (by positivity : 0 ≤ K * δ ^ 2) huBall hconv
    convert hh using 1
    dsimp [J, K]
    field_simp
    ring
  have hpack : BodyPacking U (J * δ ^ 2) 1000 :=
    (closedTube_packing hδ x v hv hover).affine_image (sq_nonneg δ) hJ f hvol
  have hZd : ∀ i, ENNReal.ofReal ((δ ^ (2 : ℕ)) ^ η) * volume (U i) ≤ volume (Z i) := by
    intro i
    have hh : 384 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ η := by
      rw [← Real.rpow_natCast_mul hδ.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * η = η + η by ring, Real.rpow_add hδ]
      have hp := Real.rpow_pos_of_pos hδ η
      nlinarith [mul_le_mul_of_nonneg_left hδpow hp.le]
    change ENNReal.ofReal _ * volume (f '' closedTube δ (x i) (v i)) ≤ volume (f '' Y i)
    rw [hvol, hvol]
    calc
      _ ≤ ENNReal.ofReal ((δ ^ (2 : ℕ)) ^ η) * (ENNReal.ofReal J * ENNReal.ofReal (384 * δ ^ 2)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (closedTube_volume_bounds hδ hδ1 (x i) (v i) (hv i)).2)
      _ ≤ ENNReal.ofReal J * ENNReal.ofReal (δ ^ η * δ ^ 2) := by
        simp only [← ENNReal.ofReal_mul (by positivity : 0 ≤ J),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ (δ ^ (2 : ℕ)) ^ η)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith only [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ J * δ ^ 2)]
      _ ≤ _ := mul_le_mul' le_rfl (hYden i)
  have hbound := H (δ ^ (2 : ℕ)) (by positivity) hdscale n U Z (fun i => f (x i))
    (δ / (1024 * a)) (J * δ ^ 2) (384 * K * δ ^ 2) (1024 * L) 1000 hn hnmax' hwidth
    (by positivity) hm (by linarith) (by norm_num) hgeom
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hYm i))
    (fun i => image_mono ((hYT i).trans (tube_subset_closedTube _ _ _))) hZd hconv' hslab hpack
  have hUvol : volume (⋃ i, Z i) = ENNReal.ofReal J * volume (⋃ i, Y i) := by
    rw [← hvol, image_iUnion]
  rw [hUvol] at hbound
  have hscalar := fine_body_factorization (σ := σ) (u := u) (ε := ε) hA hδ ha hb hLpos hn'
  change A * (δ ^ (2 : ℕ)) ^ (ε / 2) * (δ / (1024 * a)) ^ u *
    bodyWeight σ (J * δ ^ 2) (384 * K * δ ^ 2) (1024 * L) 1000 n = _ at hscalar
  rw [hscalar, ENNReal.ofReal_mul hJ.le] at hbound
  have hbound' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top).mp hbound
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbound'
  have hLp : L⁻¹ ≤ L ^ (-1 + σ / 2) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hA' := fineBodyConstant_pos (σ := σ) (u := u) hA
  gcongr

end WangZahlLot.Obl.wz_flat_factored_improvement
