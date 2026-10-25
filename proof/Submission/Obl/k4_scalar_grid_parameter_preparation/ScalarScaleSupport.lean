/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarScaleSupport.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarScalePackets
import Submission.Obl.k4_scalar_grid_parameter_preparation.LowGradientSupport
import Submission.Obl.k4_scalar_grid_parameter_preparation.PacketCount
import Submission.Obl.k4_scalar_grid_parameter_preparation.PacketGradient

/-! Physical support of the measurable scalar core, counted in each original world. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped Classical BigOperators ENNReal

theorem scalar_row_components_le (A B v D K M : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hrow : |A + B * v| ≤ D) (hv : |v| ≤ K) (hB : |B| ≤ M) :
    |A| ≤ D + (K + 1) * M ∧ |B| ≤ D + (K + 1) * M := by
  have hA : |A| ≤ D + K * M := by
    calc
      _ = |(A + B * v) - B * v| := by congr 1; ring
      _ ≤ |A + B * v| + |B * v| := abs_sub _ _
      _ ≤ D + M * K := add_le_add hrow (by
        rw [abs_mul]
        exact mul_le_mul hB hv (abs_nonneg _) hM)
      _ = _ := by ring
  constructor <;> nlinarith [mul_nonneg hK hM]

theorem exists_scalar_scale_core_support_bound {X : Type*}
    [MeasurableSpace X] : ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ (G : Type*) [DecidableEq G] (K ξ : ℝ) (n q : ℕ) (a : X → Fin 5 → ℝ)
      (D : ScalarScalePackets X G a K ξ n q)
      (ν : Measure X), IsProbabilityMeasure ν →
    ∀ (E : Set (X × ℝ)) (g : G) (M W : ℝ),
      1 ≤ K → 0 < ξ → 0 < q → ξ ≤ K * (q : ℝ)⁻¹ → 0 ≤ M → 0 < W →
      (∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a p.1 e| ≤ K) →
      (∀ i, D.world i = g → ENNReal.ofReal (W / (K * (q : ℝ))) ≤ ν (D.labels i)) →
      (physicalScalarGridTag ξ '' (scalarPacketPosition a '' scalarScaleCore D E M g)).Finite ∧
      ((physicalScalarGridTag ξ '' (scalarPacketPosition a '' scalarScaleCore D E M g)).ncard : ℝ) ≤
        4 * K ^ 3 * (8 * K + 2) * (4 * (C₀ * K ^ 2 + (K + 1) * M + K) + 2) / (W * ξ ^ 2) := by
  obtain ⟨C₀, hC₀, hfield⟩ := exists_scalar_packet_field_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro G _ K ξ n q a D ν hν E g M W hK hξ hq hrate hM hW hE hfloor
  letI : IsProbabilityMeasure ν := hν
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let L := C₀ * K ^ 2 + (K + 1) * M
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let I := Finset.univ.filter fun i => D.world i = g
  let points (i : Fin n) := scalarPacketPosition a ''
    (scalarScaleCore D E M g ∩ (D.labels i ×ˢ scalarPacketBlock q (D.block i)))
  let cells (i : Fin n) := physicalScalarGridTag ξ '' points i
  let C := 4 * K ^ 2 * (8 * K + 2) * (4 * (L + K) + 2) * ((q : ℝ)⁻¹ / ξ) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcell (i : I) : (cells i.val).Finite ∧ ((cells i.val).ncard : ℝ) ≤ C := by
    have hgrad : ∀ r ∈ points i.val, ∀ e,
        |eval ![r 0,r 1] (pderiv e (D.predictor i.val))| ≤ L := by
      rintro r ⟨p, ⟨hpCore, hpPacket⟩, rfl⟩ e
      have hpE := scalarScaleCore_subset D E M g hpCore
      have hnot : p ∉ scalarScaleBad D E M i.val := by
        intro hb
        exact hpCore.2 (Set.mem_iUnion₂.mpr ⟨i.val,i.property,hb⟩)
      have hFy : |eval ![p.2,scalarY (a p.1) p.2] (pderiv 1 (D.predictor i.val))| ≤ M := by
        exact (lt_of_not_ge fun hge => hnot ⟨hpE,hpPacket.1,hpPacket.2,hge⟩).le
      have hd := hfield (D.predictor i.val) (a p.1) K (((D.block i.val : ℕ) : ℝ) / q)
        (q : ℝ)⁻¹ ξ (D.predictor_degree i.val) hK (hE p hpE).2
        (scalarPacketBlock_start_unit hq (D.block i.val)).1
        (scalarPacketBlock_end_le_one hq (D.block i.val)) (inv_pos.mpr hqR) hξ hrate
        (fun t ht => (D.trajectory_fit i.val p.1 hpPacket.1 t ht).2) p.2 hpPacket.2
      have hrow : |eval ![p.2,scalarY (a p.1) p.2] (pderiv 0 (D.predictor i.val)) +
          eval ![p.2,scalarY (a p.1) p.2] (pderiv 1 (D.predictor i.val)) * a p.1 1| ≤ C₀ * K ^ 2 := by
        simpa only [scalarY, mul_comm] using hd
      have hb := scalar_row_components_le _ _ _ (C₀ * K ^ 2) K M (by positivity)
        hK₀ hM hrow ((hE p hpE).2 1) hFy
      fin_cases e
      · exact hb.1
      · exact hb.2
    have hc := physical_grid_cover_of_quadratic_packet_at_rate (points i.val) (D.predictor i.val)
      (D.predictor_degree i.val) ξ (q : ℝ)⁻¹ K L (((D.block i.val : ℕ) : ℝ) / q)
      (D.centerY i.val) (D.centerV i.val) hξ (inv_pos.mpr hqR) hrate hK hL
      (by linarith [D.center_bound i.val, abs_nonneg (D.centerY i.val)])
      (by rintro _ ⟨p, ⟨hpCore,hpPacket⟩, rfl⟩; exact hpPacket.2)
      (by rintro _ ⟨p, ⟨hpCore,hpPacket⟩, rfl⟩; exact (D.trajectory_fit i.val p.1 hpPacket.1 p.2 hpPacket.2).1)
      (by rintro _ ⟨p, ⟨hpCore,hpPacket⟩, rfl⟩; exact (D.trajectory_fit i.val p.1 hpPacket.1 p.2 hpPacket.2).2)
      hgrad
    exact hc
  let Q (i : I) := (hcell i).1.toFinset
  let H := Finset.univ.biUnion Q
  have hcover : physicalScalarGridTag ξ '' (scalarPacketPosition a '' scalarScaleCore D E M g) ⊆
      (H : Set (Fin 3 → ℤ)) := by
    rintro _ ⟨r, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp hp.1.2
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨i,hi⟩, Finset.mem_univ _, ?_⟩
    exact (hcell ⟨i,hi⟩).1.mem_toFinset.mpr
      ⟨scalarPacketPosition a p, ⟨p, ⟨hp,hpi⟩, rfl⟩, rfl⟩
  have hH : (H.card : ℝ) ≤ (I.card : ℝ) * C := by
    calc
      _ ≤ ∑ i : I, ((Q i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i : I, C := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Set.ncard_eq_toFinset_card _ (hcell i).1]
        exact (hcell i).2
      _ = _ := by simp
  have hI := saturated_packet_count_le ν D.world D.block D.labels g K W hKpos hW hq
    D.labels_measurable D.labels_disjoint hfloor
  refine ⟨H.finite_toSet.subset hcover, ?_⟩
  calc
    _ ≤ (H.card : ℝ) := by exact_mod_cast Set.ncard_le_ncard hcover H.finite_toSet
    _ ≤ (I.card : ℝ) * C := hH
    _ ≤ (K * (q : ℝ) ^ 2 / W) * C := mul_le_mul_of_nonneg_right hI hC
    _ = _ := by dsimp [C, L]; field_simp

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
