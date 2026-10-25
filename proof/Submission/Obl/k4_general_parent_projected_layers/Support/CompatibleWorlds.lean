/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/CompatibleWorlds.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldRepresentatives
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedGroupLists
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedParentBand
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Only a bounded number of transverse crops meet a true tilted parent packet. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Set

noncomputable section

theorem compatible_parent_world_lists {K q g chi tmid : ℝ} (c : Fin 5 → ℝ)
    (hK : 1 ≤ K) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hg : 0 < g) (hc : 0 < chi)
    (hcq : chi ≤ q) (hcqg : chi ≤ q * g) (ht : tmid ∈ Icc (0 : ℝ) 1)
    (hc₄ : |c 4| ≤ K) :
    ∃ (V : Finset ℤ) (I : ℤ → Finset ℤ) (G : ℤ → ℤ → Finset (ℤ × ℤ)),
      (∀ v, ((I v).card : ℝ) * chi ≤ 10 * K * q) ∧
      (∀ v z, ((G v z).card : ℝ) ≤ 180 * K ^ 2) ∧
      ∀ b : Fin 6 → ℝ, |b 0| + |b 1| + |b 3| + |b 4| ≤ K →
        |b 0 + tmid * b 3 - (c 0 + tmid * c 1)| ≤ K * q →
        |b 1 + tmid * b 4 - c 2 - tmid * c 3 - c 4 * (b 0 + tmid * b 3)| ≤ K * q * g →
        |b 4 - c 3 - c 4 * b 3| ≤ K * g →
        let u := projectedWorldTag chi g b
        u 0 ∈ V ∧ u 1 ∈ I (u 0) ∧ (u 2, u 3) ∈ G (u 0) (u 1) := by
  classical
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hcg : chi ≤ g := hcqg.trans (by nlinarith [mul_le_mul_of_nonneg_right hq1 hg.le])
  obtain ⟨V, _hVcard, hVcover⟩ := interval_mesh_cover hc hK0 0
  choose I hI hIcover using fun v : ℤ => major_intercept_mesh_cover hK hq hc hcq ht
    (center := c 0 + tmid * c 1) (velocity := boundedBinRepresentative K chi v)
  choose S hS hScover using fun v : ℤ => transverse_slope_mesh_cover hK hg hcg hc₄
    (c₃ := c 3) (velocity := boundedBinRepresentative K chi v)
  choose U hU hUcover using fun (v z w : ℤ) => transverse_intercept_mesh_cover hK hq1 hg hcqg ht hc₄
    (c₂ := c 2) (c₃ := c 3) (z₀ := boundedBinRepresentative K chi z)
    (z₁ := boundedBinRepresentative K chi v) (y₁ := boundedBinRepresentative K g w)
  let G (v z : ℤ) := (S v).biUnion (fun w => (U v z w).image (fun u => (u, w)))
  have hG (v z : ℤ) : ((G v z).card : ℝ) ≤ 180 * K ^ 2 := by
    calc
      _ ≤ ∑ w ∈ S v, (((U v z w).image (fun u => (u, w))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ w ∈ S v, ((U v z w).card : ℝ) := by
        exact_mod_cast Finset.sum_le_sum (fun w hw => Finset.card_image_le)
      _ ≤ ∑ _w ∈ S v, 18 * K := Finset.sum_le_sum (fun w hw => hU v z w)
      _ = ((S v).card : ℝ) * (18 * K) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (10 * K) * (18 * K) := mul_le_mul_of_nonneg_right (hS v) (by positivity)
      _ = _ := by ring
  refine ⟨V, I, G, hI, hG, ?_⟩
  intro b hb hmajor htrans hslope
  let u := projectedWorldTag chi g b
  have hrep := projectedWorldRepresentatives_gap hc hg b hb (q := u) rfl
  have hvel : |b 3 - boundedBinRepresentative K chi (u 0)| ≤ chi := hrep.1.2
  have hcrop : |b 4 - boundedBinRepresentative K g (u 3)| ≤ g := hrep.2.2
  have hb3 : |b 3| ≤ K := by linarith [abs_nonneg (b 0), abs_nonneg (b 1), abs_nonneg (b 4)]
  have hv : u 0 ∈ V := hVcover _ (by simpa only [sub_zero] using hb3)
  have hi : u 1 ∈ I (u 0) := hIcover (u 0) (b 0) (b 3) hmajor hvel
  have hw : u 3 ∈ S (u 0) := hScover (u 0) (b 3) (b 4) hvel hslope
  have hmotion := major_motion_error hc.le b ht hrep.1
  have hmotion' : |b 0 + tmid * b 3 -
      (boundedBinRepresentative K chi (u 1) + tmid * boundedBinRepresentative K chi (u 0))| ≤
      2 * chi := by
    simpa only [basePoint, Submission.Lib.K4MovingMeshBoxes.basePoint,
      Matrix.cons_val_one, Matrix.cons_val_zero, projectedWorldRepresentatives,
      sub_add_eq_sub_sub] using hmotion
  have hu : u 2 ∈ U (u 0) (u 1) (u 3) :=
    hUcover (u 0) (u 1) (u 3) (b 0) (b 1) (b 3) (b 4) htrans hmotion' hcrop
  exact ⟨hv, hi, Finset.mem_biUnion.mpr ⟨u 3, hw, Finset.mem_image.mpr ⟨u 2, hu, rfl⟩⟩⟩

end

end Submission.Obl.k4_general_parent_projected_layers
