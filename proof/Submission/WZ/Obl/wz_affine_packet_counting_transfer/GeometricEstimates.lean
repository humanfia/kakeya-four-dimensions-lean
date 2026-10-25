-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_packet_counting_transfer.GeometricEstimates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic

namespace WangZahlLot.Obl.wz_affine_packet_counting_transfer

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- The slab theorem applied to a whole affine cell bounds its assigned indices. -/
theorem slab_cell {Cs δ ρ h t l : ℝ} (hCs : 0 ≤ Cs)
    (hcover : ∀ (s : ℝ) (W : Set Space), 0 < s → Convex ℝ W → W ⊆ Ball →
      volume W ≤ ENNReal.ofReal s →
      (∃ x v : Space, ‖v‖ = 1 ∧ segment ℝ x (x + v) ⊆ W) →
      ∃ (u : Space) (a r : ℝ), ‖u‖ = 1 ∧ 0 < r ∧
        W ⊆ (Ball ∩ {p | |inner ℝ u p - a| ≤ r}) ∧
        volume (Ball ∩ {p | |inner ℝ u p - a| ≤ r}) ≤ ENNReal.ofReal (Cs * s ^ (1/2 : ℝ)))
    (hδ : 0 < δ) (hh : 0 < h) (ht : 0 < t) (hl : 0 ≤ l)
    {n N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (x v : Fin n → Space) (z w : Fin N → Space)
    (F : Fin N → Finset (Fin n)) (f : AffineEquiv ℝ Space Space)
    (hcard : ∀ a, (F a).card = q)
    (hdisj : ∀ a b, a ≠ b → Disjoint (F a) (F b))
    (hv : ∀ i, ‖v i‖ = 1)
    (hB : ∀ i, Tube δ (x i) (v i) ⊆ Ball)
    (houtB : ∀ a, Tube ρ (z a) (w a) ⊆ Ball)
    (hsub : ∀ a i, i ∈ F a → Tube δ (x i) (v i) ⊆ f '' Tube ρ (z a) (w a))
    (hvol : ∀ Q : Set Space, Convex ℝ Q →
      volume (f '' Q ∩ Ball) ≤ ENNReal.ofReal (t / h) * volume Q)
    (hL : SlabCount δ l n x v) :
    (N : ℝ) * (q : ℝ) ≤ (l * (n : ℝ)) * (Cs * (16 * (t / h)) ^ (1/2 : ℝ)) := by
  let W : Set Space := f '' Ball ∩ Ball
  have hW : Convex ℝ W := convex_pullback f (convex_ball _ _)
  have hWsub : ∀ a i, i ∈ F a → Tube δ (x i) (v i) ⊆ W := by
    intro a i hi p hp
    exact ⟨Set.image_mono (houtB a) (hsub a i hi hp), hB i hp⟩
  have hWvol : volume W ≤ ENNReal.ofReal (16 * (t / h)) := by
    calc
      _ ≤ ENNReal.ofReal (t / h) * volume Ball := hvol _ (convex_ball _ _)
      _ ≤ ENNReal.ofReal (t / h) * ENNReal.ofReal 16 := by
        gcongr
        exact ball_volume_upper
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hseg : ∃ x v : Space, ‖v‖ = 1 ∧ segment ℝ x (x + v) ⊆ W := by
    let a : Fin N := ⟨0, hN⟩
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (F a).card by rw [hcard]; exact hq)
    exact ⟨x i, v i, hv i, (self_subset_thickening hδ _).trans (hWsub a i hi)⟩
  obtain ⟨u, a, r, hu, hr, hWS, hSvol⟩ :=
    hcover (16 * (t / h)) W (by positivity) hW inter_subset_right hWvol hseg
  let A : Set (Fin n) := {i | Tube δ (x i) (v i) ⊆ Ball ∩ {p | |inner ℝ u p - a| ≤ r}}
  have hc : N * q ≤ A.ncard := by
    have hc := fiber_count F hcard hdisj Set.univ A (by
      intro b hb i hi
      exact (hWsub b i hi).trans hWS)
    simpa using hc
  have hc' : (N : ℝ) * (q : ℝ) ≤ (A.ncard : ℝ) := by exact_mod_cast hc
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc
    _ ≤ ENNReal.ofReal (A.ncard : ℝ) := ENNReal.ofReal_le_ofReal hc'
    _ ≤ ENNReal.ofReal (l * (n : ℝ)) * volume (Ball ∩ {p | |inner ℝ u p - a| ≤ r}) :=
      hL u a r hu hr
    _ ≤ ENNReal.ofReal (l * (n : ℝ)) * ENNReal.ofReal (Cs * (16 * (t / h)) ^ (1/2 : ℝ)) := by
      gcongr
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- Reindex a single fiber injectively before applying the supplied packing estimate. -/
theorem packing_fiber {Cp δ ρ h t : ℝ} (hCp : 0 ≤ Cp)
    (hpacking : ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (W : Set Space), Convex ℝ W → W ⊆ Ball →
      (∀ i, ‖v i‖ = 1) → (∀ i, Tube δ (x i) (v i) ⊆ W) →
      (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1/2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) →
      ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal Cp * (volume W) ^ 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/100) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hh : 0 < h) (ht : 0 < t) {n q : ℕ}
    (x v : Fin n → Space) (z w : Space)
    (F : Finset (Fin n)) (f : AffineEquiv ℝ Space Space)
    (hcard : F.card = q) (hv : ∀ i, ‖v i‖ = 1) (hw : ‖w‖ = 1)
    (hB : ∀ i, Tube δ (x i) (v i) ⊆ Ball)
    (hsub : ∀ i, i ∈ F → Tube δ (x i) (v i) ⊆ f '' Tube ρ z w)
    (hdist : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1/2 : ℝ≥0∞) * volume (Tube δ (x i) (v i)))
    (hvol : ∀ Q : Set Space, Convex ℝ Q →
      volume (f '' Q ∩ Ball) ≤ ENNReal.ofReal (t / h) * volume Q) :
    (q : ℝ) * δ ^ 4 ≤ Cp * ((t / h) * (384 * ρ ^ 2)) ^ 2 := by
  classical
  let W : Set Space := f '' Tube ρ z w ∩ Ball
  let e : Fin q ≃ {i // i ∈ F} :=
    (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  have hinj : Function.Injective (fun i : Fin q => (e i).val) :=
    Subtype.val_injective.comp e.injective
  have hWvol : volume W ≤ ENNReal.ofReal ((t / h) * (384 * ρ ^ 2)) := by
    calc
      _ ≤ ENNReal.ofReal (t / h) * volume (Tube ρ z w) := hvol _ (convex_tube _ _ _)
      _ ≤ ENNReal.ofReal (t / h) * ENNReal.ofReal (384 * ρ ^ 2) := by
        gcongr
        exact tube_volume_upper hρ hρ1 z w hw
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hp := hpacking δ hδ hδ1 q (fun i => x (e i).val) (fun i => v (e i).val) W
    (convex_pullback f (convex_tube _ _ _)) inter_subset_right
    (fun i => hv (e i).val)
    (fun i p hp => ⟨hsub (e i).val (e i).property hp, hB (e i).val hp⟩)
    (fun i j hij => hdist _ _ (fun he => hij (hinj he)))
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc
    _ ≤ ENNReal.ofReal Cp * volume W ^ 2 := hp
    _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal ((t / h) * (384 * ρ ^ 2))) ^ 2 := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hCp]

end WangZahlLot.Obl.wz_affine_packet_counting_transfer
