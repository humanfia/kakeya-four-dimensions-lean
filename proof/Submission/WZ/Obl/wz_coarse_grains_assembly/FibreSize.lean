-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.FibreSize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.CoverCount
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FiberMass
import Submission.WZ.Obl.wz_separated_scales_gain.UniformOuter

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open Set MeasureTheory

/-- A largest fibre of a balanced cover is positive and bounded by the
balanced average over the original fine family. -/
theorem maximum_cover_fibre {δ θ ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N} {b : Prop}
    (hδ : 0 < δ) (hn : 0 < n)
    (hmassY : O (δ ^ θ * n * δ ^ 2) ≤ ∑ i, μ (Y i))
    (hC : C δ θ n x v Y S Z ρ N y w f b) :
    ∃ D : ℝ, 0 < D ∧ (∀ k, ((S.filter (fun i => f i = k)).card : ℝ) ≤ D) ∧
      (N : ℝ) * D ≤ δ ^ (-θ) * n := by
  classical
  obtain ⟨k₁, hne, _, _⟩ := exists_dense_cover_fibre hδ hn hmassY hC
  let size (k : Fin N) := (S.filter (fun i => f i = k)).card
  have hU : (Finset.univ : Finset (Fin N)).Nonempty := ⟨k₁, Finset.mem_univ _⟩
  obtain ⟨k₀, _, hmax⟩ := Finset.exists_max_image Finset.univ size hU
  have hD : 0 < size k₀ := lt_of_lt_of_le hne.card_pos (hmax k₁ (Finset.mem_univ _))
  refine ⟨size k₀, Nat.cast_pos.mpr hD, fun k => Nat.cast_le.mpr (hmax k (Finset.mem_univ _)), ?_⟩
  have hq (k : Fin N) : q n {i | i ∈ S ∧ f i = k} = (size k : ℝ) := by
    have he : {i | i ∈ S ∧ f i = k} = (↑(S.filter (fun i => f i = k)) : Set (Fin n)) := by
      ext i
      simp
    simp only [q, he, Set.ncard_coe_finset, size]
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.balanced_fiber_card_le
    S f (L := δ ^ (-θ)) (fun k k' => by simpa only [hq] using hC.2.2.2.2.2.2.1 k k') k₀
  have hh' : (N : ℝ) * size k₀ ≤ δ ^ (-θ) * S.card := by
    simpa only [Fintype.card_fin, mul_comm] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S))
    (Real.rpow_nonneg hδ.le _))

/-- Essential distinctness gives the polynomial count needed by the
small-power size-coloring API; no Katz--Tao hypothesis is used. -/
theorem fine_count_power_seven {δ : ℝ} {n : ℕ} {x v : Fin n → V}
    (hδ : 0 < δ) (hconstant : (1000000000000 : ℝ) ≤ δ ^ (-3 : ℝ))
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, T δ (x i) (v i) ⊆ I)
    (hX : X δ n x v) : (n : ℝ) ≤ δ ^ (-7 : ℝ) := by
  have hpack := WangZahlLot.Obl.wz_separated_scales_gain.outer_packing_bound hδ x v hv
    (fun i => (hball i).trans (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5))) hX
  apply (mul_le_mul_iff_of_pos_right (pow_pos hδ 4)).mp
  calc
    (n : ℝ) * δ ^ 4 ≤ 1000000000000 := hpack
    _ ≤ δ ^ (-3 : ℝ) := hconstant
    _ = δ ^ (-7 : ℝ) * δ ^ 4 := by
      rw [← Real.rpow_natCast δ 4, ← Real.rpow_add hδ]
      norm_num

end WangZahlLot.Obl.wz_coarse_grains_assembly
