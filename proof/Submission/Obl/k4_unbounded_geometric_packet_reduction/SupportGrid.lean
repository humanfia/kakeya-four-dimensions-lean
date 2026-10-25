import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportOscillation

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory

noncomputable section

/-- Bounded affine scalar trajectories have a finite common set of base
mesh cells, independent of the packet and of the number of trajectories. -/
theorem scalar_base_cells {K σ : ℝ} (hK : 0 ≤ K) (hσ : 0 < σ) :
    ∃ cells : Finset (Fin 2 → ℤ),
      (cells.card : ℝ) ≤ (2 / σ + 2) * (8 * K / σ + 2) ∧
      ∀ b : Fin 5 → ℝ, (∀ i, |b i| ≤ K) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        scalarZ b t σ ∈ cells := by
  classical
  have ht := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Set.Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≤ 1) hσ 0 (by
      intro x hx y hy
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
  have hy := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Set.Icc (-2 * K) (2 * K)) (by positivity : 0 ≤ 4 * K) hσ 0 (by
      intro x hx y hy
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2])
  let T : Finset ℤ := ht.1.toFinset
  let Y : Finset ℤ := hy.1.toFinset
  let cells : Finset (Fin 2 → ℤ) := (T.product Y).image (fun p => ![p.1, p.2])
  have hT : (T.card : ℝ) ≤ 2 / σ + 2 := by
    simpa only [Set.ncard_eq_toFinset_card _ ht.1, mul_one] using ht.2
  have hY : (Y.card : ℝ) ≤ 8 * K / σ + 2 := by
    have hh := hy.2
    rw [Set.ncard_eq_toFinset_card _ hy.1] at hh
    convert hh using 1 <;> ring
  refine ⟨cells, ?_, ?_⟩
  · calc
      _ ≤ ((T.product Y).card : ℝ) := by
        exact_mod_cast (Finset.card_image_le : cells.card ≤ (T.product Y).card)
      _ = (T.card : ℝ) * (Y.card : ℝ) := by
        rw [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
      _ ≤ _ := mul_le_mul hT hY (Nat.cast_nonneg _) (by positivity)
  · intro b hb t ht'
    have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht'.1]; exact ht'.2
    have hyAbs : |scalarY b t| ≤ 2 * K := by
      calc
        _ ≤ |b 0| + |t * b 1| := abs_add_le _ _
        _ = |b 0| + |t| * |b 1| := by rw [abs_mul]
        _ ≤ K + 1 * K := add_le_add (hb 0)
          (mul_le_mul htAbs (hb 1) (abs_nonneg _) zero_le_one)
        _ = _ := by ring
    have htm : ⌊t / σ⌋ ∈ T := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨t, ht', by simp⟩
    have hym : ⌊scalarY b t / σ⌋ ∈ Y := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨scalarY b t, by simpa only [Set.mem_Icc, neg_mul] using abs_le.mp hyAbs, by simp⟩
    exact Finset.mem_image.mpr
      ⟨(⌊t / σ⌋, ⌊scalarY b t / σ⌋), Finset.mem_product.mpr ⟨htm, hym⟩, rfl⟩

/-- The oscillation pieces yield an actual finite occupied joint support.
This explicit bound separates base-cell count, earlier labels, partition
pieces, and native oscillation, ready for power-loss absorption. -/
theorem OscillationPieces.finite_support
    {N χ d s m : ℝ} {C Cpart : ℕ} {R : Fin C → ENNReal}
    {μ : Fin C → Measure Inc} {b : Fin C → Traj → Fin 5 → ℝ}
    (o : OscillationPieces N χ d s m C Cpart R μ b) (hN : 0 < N)
    (hcoeff : ∀ a l i, |b a l i| ≤ N ^ χ) :
    ∃ F : Fin C → Finset ((Fin 2 → ℤ) × ℤ), ∀ a,
      ((F a).card : ℝ) ≤
        ((2 / N ^ (-m) + 2) * (8 * N ^ χ / N ^ (-m) + 2)) *
          N ^ (d * s + χ) * (N ^ χ) ^ Cpart *
            (4 * (N ^ χ) ^ Cpart * N ^ (-s + χ) / N ^ (-s) + 2) ∧
      ∀ p, p ∈ (⋃ e, ⋃ i, o.piece a e i) → p.2 ∈ Set.Icc (0 : ℝ) 1 →
        (scalarZ (b a p.1) p.2 (N ^ (-m)),
          ⌊scalarX (b a p.1) p.2 / N ^ (-s)⌋) ∈ F a := by
  classical
  obtain ⟨cells, hcells, hcell_mem⟩ := scalar_base_cells
    (Real.rpow_nonneg hN.le χ) (Real.rpow_pos_of_pos hN (-m))
  let values (a : Fin C) (q : Fin 2 → ℤ) (e : Fin o.labels) (i : Fin (o.parts e)) : Set ℝ :=
    {x | ∃ p, p ∈ o.piece a e i ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
      scalarZ (b a p.1) p.2 (N ^ (-m)) = q ∧ scalarX (b a p.1) p.2 = x}
  have hosc a q e i : ∀ x ∈ values a q e i, ∀ y ∈ values a q e i,
      dist x y ≤ 2 * (N ^ χ) ^ Cpart * N ^ (-s + χ) := by
    rintro x ⟨p, hp, ht, hq, hx⟩ y ⟨p', hp', ht', hq', hy⟩
    simpa only [Real.dist_eq, hx, hy] using
      o.native_oscillation a e i p hp p' hp' (hq.trans hq'.symm)
  have hfamily a := finite_support_of_colored_oscillation cells (o.tags a) o.parts (values a)
    (Real.rpow_nonneg hN.le _) (pow_nonneg (Real.rpow_nonneg hN.le _) _)
    (show 0 ≤ 2 * (N ^ χ) ^ Cpart * N ^ (-s + χ) by positivity)
    (Real.rpow_pos_of_pos hN (-s)) 0 (fun q _ => o.tag_bound a q) o.part_bound (hosc a)
  choose F hF hcover using hfamily
  refine ⟨F, fun a => ⟨?_, ?_⟩⟩
  · have hbin : 2 * (2 * (N ^ χ) ^ Cpart * N ^ (-s + χ)) / N ^ (-s) + 2 =
        4 * (N ^ χ) ^ Cpart * N ^ (-s + χ) / N ^ (-s) + 2 := by ring
    have hH : 0 ≤ N ^ (d * s + χ) := Real.rpow_nonneg hN.le _
    have hG : 0 ≤ (N ^ χ) ^ Cpart := pow_nonneg (Real.rpow_nonneg hN.le _) _
    have hB : 0 ≤ 4 * (N ^ χ) ^ Cpart * N ^ (-s + χ) / N ^ (-s) + 2 := by positivity
    have hh := hF a
    rw [hbin] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcells hH) hG) hB
  · intro p hp ht
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    have hh := hcover a (scalarZ (b a p.1) p.2 (N ^ (-m)))
      (hcell_mem (b a p.1) (hcoeff a p.1) p.2 ht) e (o.listed a e i p hi) i
      (scalarX (b a p.1) p.2) ⟨p, hi, ht, rfl, rfl⟩
    simpa only [sub_zero] using hh

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
