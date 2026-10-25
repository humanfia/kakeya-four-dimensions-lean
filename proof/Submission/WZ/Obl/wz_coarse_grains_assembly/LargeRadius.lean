-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.LargeRadius.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.CoverCount
import Submission.WZ.Obl.wz_separated_scales_gain.Geometry
import Submission.WZ.Obl.wz_convex_container_tube_packing.Packing
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory Metric

/-- Every coarse tube of a balanced positive-mass cover meets the original
unit ball, hence lies in the ball of radius five. -/
theorem coarse_tubes_subset_ball_five {δ η ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hρ1 : ρ ≤ 1) (hn : 0 < n)
    (hmassY : O (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hball : ∀ i, T δ (x i) (v i) ⊆ I)
    (hC : C δ η n x v Y S Z ρ N y w f b) :
    ∀ k, T ρ (y k) (w k) ⊆ ball (0 : V) 5 := by
  classical
  obtain ⟨k₀, hne, _, _⟩ := exists_dense_cover_fibre hδ hn hmassY hC
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨hi₀S, hi₀f⟩ := Finset.mem_filter.mp hi₀
  have hq₀ : 0 < q n {i | i ∈ S ∧ f i = k₀} := by
    apply Nat.cast_pos.mpr
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨i₀, hi₀S, hi₀f⟩
  intro k
  have hbal := hC.2.2.2.2.2.2.1 k₀ k
  have hqk : 0 < q n {i | i ∈ S ∧ f i = k} := by
    have he := hq₀.trans_le hbal
    exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos hδ _)).mp he
  obtain ⟨i, hi, hfi⟩ := (Set.ncard_pos (Set.toFinite _)).mp (Nat.cast_pos.mp hqk)
  have hp : x i ∈ T δ (x i) (v i) :=
    self_subset_thickening hδ _ (left_mem_segment ℝ _ _)
  apply WangZahlLot.Obl.wz_separated_scales_gain.tube_subset_ball_five hρ1 (hC.2.2.1 k)
  refine ⟨x i, ?_, hball i hp⟩
  rw [← hfi]
  exact hC.2.2.2.1 i hi hp

/-- A polynomial bound on the number of occupied coarse tubes, with an
absolute constant independent of the input error. -/
theorem coarse_card_radius_four {δ η ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hn : 0 < n)
    (hmassY : O (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hball : ∀ i, T δ (x i) (v i) ⊆ I)
    (hC : C δ η n x v Y S Z ρ N y w f b) :
    (N : ℝ) * ρ ^ 4 ≤ 1000000000000 := by
  have hsub := coarse_tubes_subset_ball_five hδ hρ1 hn hmassY hball hC
  have hpack := WangZahlLot.Obl.wz_convex_container_tube_packing.packing hρ y w
    (W := ball (0 : V) 5) measure_ball_lt_top.ne (hC.2.2.1) hsub hC.2.2.2.2.2.2.2.1
  have hvol : μ (ball (0 : V) 5) ≤ O 1000 := by
    calc
      _ ≤ μ (closedBall (0 : V) 5) := measure_mono ball_subset_closedBall
      _ ≤ O (8 * (5 : ℝ) ^ 3) :=
        WangZahlLot.Obl.wz_clustered_cover_volume_gain.closedBall_volume_upper _ (by norm_num)
      _ = O 1000 := by norm_num
  have hh : O ((N : ℝ) * ρ ^ 4) ≤ O 1000000000000 := by
    calc
      _ ≤ O 1000000 * μ (ball (0 : V) 5) ^ 2 := hpack
      _ ≤ O 1000000 * (O 1000) ^ 2 := by gcongr
      _ = O 1000000000000 := by norm_num [O]
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hh

/-- At radii at least one half, the number of coarse carriers is bounded by
one fixed constant. -/
theorem coarse_card_large_radius {δ η ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hρhalf : 1 / 2 ≤ ρ) (hρ1 : ρ ≤ 1) (hn : 0 < n)
    (hmassY : O (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hball : ∀ i, T δ (x i) (v i) ⊆ I)
    (hC : C δ η n x v Y S Z ρ N y w f b) :
    (N : ℝ) ≤ 16000000000000 := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by norm_num) hρhalf
  have hc := coarse_card_radius_four hδ hρ hρ1 hn hmassY hball hC
  have h4 : (1 / 16 : ℝ) ≤ ρ ^ 4 := by nlinarith [sq_nonneg (ρ ^ 2 - 1 / 4)]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end WangZahlLot.Obl.wz_coarse_grains_assembly
