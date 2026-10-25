-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.CoarseSlabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Incidences

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory Set Metric

theorem smul_mem_slab_iff {κ : ℝ} (hκ : 0 < κ) (u p : Space) (t r : ℝ) :
    |inner ℝ u (κ • p) - t| ≤ r ↔ |inner ℝ u p - t / κ| ≤ r / κ := by
  rw [inner_smul_right]
  have he : κ * inner ℝ u p - t = κ * (inner ℝ u p - t / κ) := by field_simp
  rw [he, abs_mul, abs_of_pos hκ, le_div_iff₀ hκ]
  rw [mul_comm κ]

theorem original_slab_subset_smul_preimage {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (u : Space) (t r : ℝ) :
    (unitBall ∩ {p | |inner ℝ u p - t / κ| ≤ r / κ}) ⊆
      (fun p : Space => κ • p) ⁻¹' (unitBall ∩ {p | |inner ℝ u p - t| ≤ r}) := by
  intro p hp
  refine ⟨?_, (smul_mem_slab_iff hκ u p t r).mpr hp.2⟩
  have hn : ‖p‖ < 1 := mem_ball_zero_iff.mp hp.1
  apply mem_ball_zero_iff.mpr
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
  exact (mul_le_mul_of_nonneg_right hκ1 (norm_nonneg p)).trans_lt (by simpa using hn)

/-- The slab bound survives coarse covering when every coarse tube has many fine tubes,
and each fine tube is used only a bounded number of times. -/
theorem slabCount_to_coarse {δ r κ l N D : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hl : 0 ≤ l) (hN : 0 < N) (hD : 0 ≤ D) {n M : ℕ} (hM : 0 < M)
    (x v : Fin n → Space) (z w : Fin M → Space) (R : Fin n → Fin M → Prop)
    (hball : ∀ i, tube δ (x i) (v i) ⊆ unitBall)
    (hslab : SlabCount δ l x v)
    (hlower : ∀ j, N ≤ (Set.ncard {i | R i j} : ℝ))
    (hupper : ∀ i, (Set.ncard {j | R i j} : ℝ) ≤ D)
    (hcontain : ∀ i j, R i j →
      (fun p : Space => κ • p) '' tube δ (x i) (v i) ⊆ tube r (z j) (w j)) :
    SlabCount r (D * l * n * κ⁻¹ ^ 3 / (N * M)) z w := by
  intro u t s hu hs
  let U : Set Space := unitBall ∩ {p | |inner ℝ u p - t| ≤ s}
  let V : Set Space := unitBall ∩ {p | |inner ℝ u p - t / κ| ≤ s / κ}
  let P : Fin n → Prop := fun i => tube δ (x i) (v i) ⊆ V
  let S : Fin M → Prop := fun j => tube r (z j) (w j) ⊆ U
  have himp : ∀ i j, S j → R i j → P i := by
    intro i j hj hij p hp
    refine ⟨hball i hp, ?_⟩
    exact (smul_mem_slab_iff hκ u p t s).mp (hj (hcontain i j hij ⟨p, hp, rfl⟩)).2
  have hc := bounded_incidence_count R P S hD (fun j _ => hlower j) hupper himp
  have hv : volume V ≤ ENNReal.ofReal (κ⁻¹ ^ 3) * volume U := by
    rw [← volume_smul_preimage hκ]
    exact measure_mono (original_slab_subset_smul_preimage hκ hκ1 u t s)
  have hsl : ENNReal.ofReal (Set.ncard {i | P i} : ℝ) ≤
      ENNReal.ofReal (l * n * κ⁻¹ ^ 3) * volume U := by
    calc
      _ ≤ ENNReal.ofReal (l * n) * volume V := hslab u (t / κ) (s / κ) hu (div_pos hs hκ)
      _ ≤ ENNReal.ofReal (l * n) * (ENNReal.ofReal (κ⁻¹ ^ 3) * volume U) :=
        mul_le_mul' le_rfl hv
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hMc : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  change ENNReal.ofReal (Set.ncard {j | S j} : ℝ) ≤ _
  calc
    _ = ENNReal.ofReal N⁻¹ * ENNReal.ofReal ((Set.ncard {j | S j} : ℝ) * N) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hN.le)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal N⁻¹ * ENNReal.ofReal (D * (Set.ncard {i | P i} : ℝ)) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hc)
    _ = (ENNReal.ofReal N⁻¹ * ENNReal.ofReal D) *
        ENNReal.ofReal (Set.ncard {i | P i} : ℝ) := by
      rw [ENNReal.ofReal_mul hD, mul_assoc]
    _ ≤ (ENNReal.ofReal N⁻¹ * ENNReal.ofReal D) *
        (ENNReal.ofReal (l * n * κ⁻¹ ^ 3) * volume U) := mul_le_mul' le_rfl hsl
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hN.le),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp

end WangZahlLot.Obl.wz_nonflat_factored_improvement
