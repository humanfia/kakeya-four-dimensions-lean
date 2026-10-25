/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarHierarchyCurrentTaylor.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarHierarchyCurrentTaylor.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyTaylor

/-! Current original cell floors turn every stored row into the finest Taylor row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarGridHierarchy

theorem slopes_close_to_finest_on_current_floor_set {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {J : Fin (n + 1) → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin (n + 1) → ℝ} {B K : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (hB : 0 ≤ B) (hK : 0 < K)
    (hmesh : Antitone (fun i => 1 / (J i : ℝ)))
    (hlower : ∀ j : Fin n,
      (1 / (J j.castSucc : ℝ)) ^ (33 / 32 : ℝ) / 2 ≤ 1 / (J j.succ : ℝ))
    (hreading : ∀ i, p i ≤ 2 * (1 / (J i : ℝ)) ^ (1 / 4 : ℝ))
    (hnesting : ∀ i j, i ≤ j → ∀ t ∈ G.times, ∀ u ∈ G.times,
      scalarTimeBlockCode (J j) (hJ j) t = scalarTimeBlockCode (J j) (hJ j) u →
      scalarTimeBlockCode (J i) (hJ i) t = scalarTimeBlockCode (J i) (hJ i) u)
    {R : Set (Λ × ℝ)} (hR : R ⊆ E ∩ (univ ×ˢ G.times))
    (hfloor : ∀ q ∈ R, ∀ i,
      ENNReal.ofReal ((1 / (J i : ℝ)) / K) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (J i) (scalarTimeBlockCode (J i) (hJ i) q.2)))) :
    ∀ q ∈ R, ∀ i,
      |G.slope i q.2 - G.slope (Fin.last n) q.2| ≤
        (32 * (n : ℝ) * B * K) * (1 / (J i : ℝ)) ^ (7 / 32 : ℝ) := by
  have hH i : 0 < 1 / (J i : ℝ) := by exact one_div_pos.mpr (Nat.cast_pos.mpr (hJ i))
  have herror i : B * (1 / (J i : ℝ)) * p i ≤ (2 * B) * (1 / (J i : ℝ)) ^ (5 / 4 : ℝ) := by
    calc
      _ ≤ B * (1 / (J i : ℝ)) * (2 * (1 / (J i : ℝ)) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hreading i) (by positivity)
      _ = (2 * B) * ((1 / (J i : ℝ)) ^ (1 : ℝ) * (1 / (J i : ℝ)) ^ (1 / 4 : ℝ)) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add (hH i)]; norm_num
  have hlink q (hq : q ∈ R) (j : Fin n) :
      |G.slope j.castSucc q.2 - G.slope j.succ q.2| ≤
        32 * B * K * (1 / (J j.castSucc : ℝ)) ^ (7 / 32 : ℝ) := by
    have hqtime : q.2 ∈ G.times := (hR hq).2.2
    have hjs : j.castSucc ≤ j.succ := by change j.val ≤ j.val + 1; omega
    have hf : ENNReal.ofReal ((1 / (J j.succ : ℝ)) / K) ≤
        (ν.prod volume) ((E ∩ (univ ×ˢ G.times)) ∩
          (univ ×ˢ timeCell (J j.succ) (scalarTimeBlockCode (J j.succ) (hJ j.succ) q.2))) :=
      (hfloor q hq j.succ).trans (measure_mono (fun z hz => ⟨hR hz.1, hz.2⟩))
    have hh := G.slopes_close_on_original_child j.castSucc j.succ hqtime
      (div_pos (hH j.succ) hK) hf
      (fun t ht he => hnesting j.castSucc j.succ hjs t ht q.2 hqtime he)
    have hsum := add_le_add (herror j.castSucc) (herror j.succ)
    have hnum := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
    have hquot := div_le_div_of_nonneg_right hnum (div_nonneg (hH j.succ).le hK.le)
    have hpower := scalar_hierarchy_link_bound (hH j.castSucc) (hH j.succ)
      (hmesh hjs) (show 0 ≤ 2 * B by positivity) hK (hlower j)
    exact (hh.trans hquot).trans (by convert hpower using 1 <;> ring)
  intro q hq i
  let C := 32 * (n : ℝ) * B * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hslope : |G.slope i q.2 - G.slope (Fin.last n) q.2| ≤
      C * (1 / (J i : ℝ)) ^ (7 / 32 : ℝ) := by
    have hh := finite_scalar_slope_chain (fun j => G.slope j q.2) i
      (C := 32 * B * K * (1 / (J i : ℝ)) ^ (7 / 32 : ℝ)) (by positivity) (fun j hj => by
        have hij : i ≤ j.castSucc := hj
        have hp := Real.rpow_le_rpow (hH j.castSucc).le (hmesh hij) (by norm_num : (0 : ℝ) ≤ 7 / 32)
        exact (hlink q hq j).trans (mul_le_mul_of_nonneg_left hp (by positivity)))
    convert hh using 1 <;> dsimp [C] <;> ring
  exact hslope

theorem taylor_on_current_floor_set {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {J : Fin (n + 1) → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin (n + 1) → ℝ} {B K : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (hB : 0 ≤ B) (hK : 0 < K)
    (hmesh : Antitone (fun i => 1 / (J i : ℝ)))
    (hlower : ∀ j : Fin n,
      (1 / (J j.castSucc : ℝ)) ^ (33 / 32 : ℝ) / 2 ≤ 1 / (J j.succ : ℝ))
    (hreading : ∀ i, p i ≤ 2 * (1 / (J i : ℝ)) ^ (1 / 4 : ℝ))
    (hnesting : ∀ i j, i ≤ j → ∀ t ∈ G.times, ∀ u ∈ G.times,
      scalarTimeBlockCode (J j) (hJ j) t = scalarTimeBlockCode (J j) (hJ j) u →
      scalarTimeBlockCode (J i) (hJ i) t = scalarTimeBlockCode (J i) (hJ i) u)
    {R : Set (Λ × ℝ)} (hR : R ⊆ E ∩ (univ ×ˢ G.times))
    (hfloor : ∀ q ∈ R, ∀ i,
      ENNReal.ofReal ((1 / (J i : ℝ)) / K) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (J i) (scalarTimeBlockCode (J i) (hJ i) q.2)))) :
    ∀ q ∈ R, ∀ q' ∈ R, ∀ i,
      scalarTimeBlockCode (J i) (hJ i) q.2 = scalarTimeBlockCode (J i) (hJ i) q'.2 →
      |F q'.2 - F q.2 - (q'.2 - q.2) * G.slope (Fin.last n) q.2| ≤
        (4 * B + 32 * (n : ℝ) * B * K) * (1 / (J i : ℝ)) ^ (11 / 10 : ℝ) := by
  intro q hq q' hq' i hcode
  let C := 32 * (n : ℝ) * B * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hslope := G.slopes_close_to_finest_on_current_floor_set hB hK hmesh hlower hreading hnesting hR hfloor q hq i
  exact G.taylor_of_slope_comparison i (Fin.last n) hB hC (hreading i)
    (hR hq).2.2 (hR hq').2.2 hcode hslope

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
