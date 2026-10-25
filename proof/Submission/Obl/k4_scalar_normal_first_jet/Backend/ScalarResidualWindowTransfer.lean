/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualWindowTransfer.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualWindowTransfer.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualObservations
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarResidualReadingScales

/-! Transfer fixed anchor windows to actual first-jet interval covers at every time. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

theorem original_first_jet_covers_of_block_windows {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (s a slope : ℝ)
    (A : Set Λ) (center : ℤ → ℝ) {H K B d anchor : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hB : 1 ≤ B) (hKB : 23 * K ^ 2 ≤ B)
    (hd0 : 0 ≤ d) (hd : d < 1) (hanchor : anchor ∈ Icc (0 : ℝ) 1)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hblock : E ⊆ univ ×ˢ Icc s (s + H))
    (hcoeff : ∀ q ∈ E, D.Bounded K q.1) (hF : ∀ t, |F t| ≤ K) (hslope : |slope| ≤ K)
    (hrow : ∀ q ∈ E, |F q.2 - (a + slope * q.2)| ≤ K * H * H ^ (1 / 8 : ℝ))
    (hA : A ⊆ ((fun l => (l, s + H * anchor)) ⁻¹' E))
    (hwindow : ∀ l ∈ A,
      |scalarFirstJet D F (fun _ => slope) l (s + H * anchor) -
        center ⌊D.scalar F l (s + H * anchor) / H⌋| ≤
        (H ^ (1 / 8 : ℝ)) ^ ((1 - d) / 4) + B * H ^ (1 / 8 : ℝ)) :
    ∀ r : ℝ, H ^ ((1 - d) / 32) ≤ r →
      ∃ L : ℝ → ℤ → Finset ℝ, (∀ t z, ((L t z).card : ℝ) ≤ 1000 * B ^ 2) ∧
        ∀ l ∈ A, ∀ t, (l, t) ∈ E →
          ∃ v ∈ L t ⌊D.scalar F l t / H⌋, |scalarFirstJet D F (fun _ => slope) l t - v| ≤ r := by
  classical
  let c := s + H * anchor
  let code := fun l => (⌊D.scalar F l c / H⌋ : ℤ)
  have hp : 0 < H ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hH _
  have hp1 : H ^ (1 / 8 : ℝ) ≤ 1 := Real.rpow_le_one hH.le hH1 (by norm_num)
  have hHp : H ≤ H ^ (1 / 8 : ℝ) := Real.self_le_rpow_of_le_one hH.le hH1 (by norm_num)
  have hpoint l (hl : l ∈ A) t (ht : (l, t) ∈ E) :
      |(code l : ℝ) - (⌊D.scalar F l t / H⌋ : ℤ)| ≤ 23 * K ^ 2 + 1 ∧
      |scalarFirstJet D F (fun _ => slope) l t - center (code l)| ≤
        (H ^ (1 / 8 : ℝ)) ^ ((1 - d) / 4) + B * H ^ (1 / 8 : ℝ) + 6 * K ^ 2 * H := by
    let u := (t - s) / H
    have hut : s + H * u = t := by dsimp [u]; field_simp; ring
    have hq : (l, u) ∈ scalarLeftBlockEvent E
        {l | (l, c) ∈ E ∧ (⌊D.scalar F l c / H⌋ : ℤ) = code l} s H := by
      exact ⟨by simpa only [hut] using ht, hA hl, rfl⟩
    have hobs := original_left_residual_observations D E F s a slope (code l) hH hHp hp1 hK hanchor
      hunit hblock hcoeff hF hslope hrow l u hq
    have hbound : |(D.scalar F l t - H * code l) / H| ≤ 23 * K ^ 2 := by
      simpa only [scalarLeftObservation, hut] using hobs.1
    have hnear := normalized_scalar_bin_near_start hH (code l) hbound
    have hjet : |scalarFirstJet D F (fun _ => slope) l t -
        scalarFirstJet D F (fun _ => slope) l c| ≤ 6 * K ^ 2 * H := by
      simpa only [hut] using hobs.2.2
    refine ⟨by simpa only [abs_sub_comm] using hnear, ?_⟩
    exact (abs_sub_le _ (scalarFirstJet D F (fun _ => slope) l c) _).trans
      (by linarith [hwindow l hl])
  intro r hr
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hH _).trans_le hr
  have htime t : ∃ L : ℤ → Finset ℝ, (∀ z, ((L z).card : ℝ) ≤ 1000 * B ^ 2) ∧
      ∀ l ∈ {l | l ∈ A ∧ (l, t) ∈ E}, ∃ v ∈ L ⌊D.scalar F l t / H⌋,
        |scalarFirstJet D F (fun _ => slope) l t - v| ≤ r := by
    obtain ⟨J, hJ, hcover⟩ := scalar_first_jet_grid_covers_of_residual_windows
      {l | l ∈ A ∧ (l, t) ∈ E} code (fun l => ⌊D.scalar F l t / H⌋)
      (fun l => scalarFirstJet D F (fun _ => slope) l t) center
      hH hH1 hd0 hd hB hKB hr
      (fun l hl => (hpoint l hl.1 t hl.2).1) (fun l hl => (hpoint l hl.1 t hl.2).2)
    exact scalar_interval_covers_of_grid_covers _ _ _ J hrpos hJ hcover
  choose L hLcard hLcover using htime
  exact ⟨L, hLcard, fun l hl t ht => hLcover t l ⟨hl, ht⟩⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
