/- Adapted from this LOT tree o105, session x0548, commit6ab86148e24dd228044f997c2188e8d03c811f1b,
   Submission/Obl/k4_critical_path_framework/AngularStripLists.lean. -/
import Submission.Lib.K4VelocityStrips.StripIntersections
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_raw_localized_native_systems.Deletion

open Set MeasureTheory
open scoped ENNReal

/-- A set with bounded Euclidean diameter meets only a short product grid.
The occupied bins are defined from the set, with no distributional hypothesis. -/
theorem exists_angular_bins_of_diameter {n : ℕ}
    (V : Set (EuclideanSpace ℝ (Fin n))) {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ)
    (hdiam : ∀ v ∈ V, ∀ w ∈ V, dist v w ≤ D) :
    ∃ B : Finset (Fin n → ℤ), (B.card : ℝ) ≤ (2 * D / δ + 2) ^ n ∧
      ∀ v ∈ V, (fun j => ⌊v j / δ⌋) ∈ B := by
  classical
  let S (j : Fin n) : Set ℝ := (fun v : EuclideanSpace ℝ (Fin n) => v j) '' V
  let G (j : Fin n) : Set ℤ := (fun z : ℝ => ⌊z / δ⌋) '' S j
  have hg (j : Fin n) : (G j).Finite ∧ ((G j).ncard : ℝ) ≤ 2 * D / δ + 2 := by
    have h := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      (S j) hD hδ 0 (by
        rintro x ⟨v, hv, rfl⟩ y ⟨w, hw, rfl⟩
        have hcoord : dist (v j) (w j) ≤ dist v w := by
          simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (v - w) j
        exact hcoord.trans (hdiam v hv w hw))
    simpa only [sub_zero] using h
  let L (j : Fin n) := (hg j).1.toFinset
  refine ⟨Fintype.piFinset L, ?_, ?_⟩
  · calc
      _ = ∏ j : Fin n, ((L j).card : ℝ) := by rw [Fintype.card_piFinset, Nat.cast_prod]
      _ ≤ ∏ _j : Fin n, (2 * D / δ + 2) := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro j _
        simpa only [L, ← Set.ncard_eq_toFinset_card _ (hg j).1] using (hg j).2
      _ = _ := by simp
  · intro v hv
    apply Fintype.mem_piFinset.mpr
    intro j
    exact (hg j).1.mem_toFinset.mpr ⟨v j, ⟨v, hv, rfl⟩, rfl⟩

/-- Two transverse thin velocity strips determine at most sixteen bins once
their intersection diameter is smaller than the angular mesh. -/
theorem exists_angular_bins_of_transverse_strips
    {n m : EuclideanSpace ℝ (Fin 2)} {b c r d δ : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hr : 0 ≤ r) (hd : 0 < d) (hδ : 0 < δ)
    (hdet : d ≤ |Submission.Lib.K4VelocityStrips.stripWedge n m|)
    (hsmall : 8 * r ≤ d * δ) :
    ∃ B : Finset (Fin 2 → ℤ), B.card ≤ 16 ∧
      ∀ v ∈ Submission.Lib.K4VelocityStrips.affineStrip n b r ∩
        Submission.Lib.K4VelocityStrips.affineStrip m c r,
        (fun j => ⌊v j / δ⌋) ∈ B := by
  obtain ⟨B, hB, hmem⟩ := exists_angular_bins_of_diameter
    (Submission.Lib.K4VelocityStrips.affineStrip n b r ∩
      Submission.Lib.K4VelocityStrips.affineStrip m c r)
    (show 0 ≤ 8 * r / d by positivity) hδ (by
      intro v hv w hw
      exact Submission.Lib.K4VelocityStrips.strip_intersection_diameter hn hm hd hdet
        hv.1 hv.2 hw.1 hw.2)
  refine ⟨B, ?_, hmem⟩
  have hD : 8 * r / d ≤ δ := (div_le_iff₀ hd).mpr (by simpa [mul_comm] using hsmall)
  have hC : 2 * (8 * r / d) / δ + 2 ≤ 4 := by
    have h := (div_le_iff₀ hδ).mpr (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have hC0 : 0 ≤ 2 * (8 * r / d) / δ + 2 := by positivity
  have hpow := pow_le_pow_left₀ hC0 hC 2
  have hbound : (B.card : ℝ) ≤ 16 := hB.trans (by norm_num at hpow ⊢; exact hpow)
  exact_mod_cast hbound

end Submission.Obl.k4_raw_localized_native_systems.Deletion
