/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/ContactPairs.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_intercept_concentration.Inherited.InterceptBinCount

namespace Submission.Obl.k4_critical_intercept_concentration

open Finset Set
open Inherited

noncomputable section

/-- A true contact box occupies fourth-power volume, and an affine hidden
prediction permits only boundedly many intercept bins in each fine base cell. -/
theorem contact_intercept_pair_count
    (F : Finset (ℤ × (Fin 3 → ℤ)))
    (point : ℤ × (Fin 3 → ℤ) → Fin 3 → ℝ)
    (value : ℤ × (Fin 3 → ℤ) → ℝ)
    (A : Fin 4 → ℝ) (p : Fin 3 → ℝ) (m H K δ a M : ℝ)
    (hH : 0 < H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hδ : 0 < δ)
    (hδH : δ ≤ H ^ 2) (ha : 0 < a) (hM : 0 ≤ M)
    (hm : |m| ≤ 1) (hv : |p 2| ≤ K) (hcenter : |p 0 + m * p 2| ≤ K)
    (hA : ∀ i : Fin 3, |A i.succ| ≤ M) (hmesh : 3 * M * δ ≤ K * a)
    (hpoint : ∀ u ∈ F, point u ∈ contactGridCell δ u.2 ∧
      point u ∈ contactOuterBox m p H (8 * K * H) (32 * K ^ 2 * H ^ 2))
    (hbin : ∀ u ∈ F, ⌊value u / a⌋ = u.1)
    (hfit : ∀ u ∈ F, |value u - affineBaseEval A (point u)| ≤ 2 * K * a) :
    (F.card : ℝ) * δ ^ 3 ≤ 4194304 * K ^ 4 * H ^ 4 := by
  classical
  have hfiber (j : Fin 3 → ℤ) :
      ((F.filter (fun u => u.2 = j)).card : ℝ) ≤ 256 * K := by
    let S := F.filter (fun u => u.2 = j)
    have hbins := hidden_intercept_bin_count_per_base_cell S value point A a K M δ j
      ha hK hM hδ hA hmesh
      (by
        intro u hu
        have hu' := Finset.mem_filter.mp hu
        simpa only [hu'.2] using (hpoint u hu'.1).1)
      (fun u hu => hfit u (Finset.mem_filter.mp hu).1)
    have himage : S.image (fun u => ⌊value u / a⌋) = S.image Prod.fst := by
      apply Finset.image_congr
      intro u hu
      exact hbin u (Finset.mem_filter.mp hu).1
    have hinj : Set.InjOn Prod.fst (S : Set (ℤ × (Fin 3 → ℤ))) := by
      intro u hu v hv huv
      apply Prod.ext huv
      exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    rw [himage, Finset.card_image_of_injOn hinj] at hbins
    exact hbins
  have hcard : (F.card : ℝ) ≤ ((F.image Prod.snd).card : ℝ) * (256 * K) := by
    calc
      _ = ∑ j ∈ F.image Prod.snd, ((F.filter (fun u => u.2 = j)).card : ℝ) := by
        exact_mod_cast Finset.card_eq_sum_card_image Prod.snd F
      _ ≤ ∑ _j ∈ F.image Prod.snd, 256 * K := Finset.sum_le_sum (fun j _ => hfiber j)
      _ = _ := by simp
  have hcells := contactGrid_count hH hH1 hK hδ hδH hm hv hcenter
    (F.image Prod.snd) (by
      intro j hj
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨point u, (hpoint u hu).1, (hpoint u hu).2⟩)
  have hK0 : 0 ≤ K := by linarith
  calc
    (F.card : ℝ) * δ ^ 3 ≤ (((F.image Prod.snd).card : ℝ) * (256 * K)) * δ ^ 3 := by gcongr
    _ = (256 * K) * (((F.image Prod.snd).card : ℝ) * δ ^ 3) := by ring
    _ ≤ (256 * K) * (16384 * K ^ 3 * H ^ 4) :=
      mul_le_mul_of_nonneg_left hcells (by positivity)
    _ = _ := by ring

end

end Submission.Obl.k4_critical_intercept_concentration
