/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file DiscoveryPieces.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryScaleGrid

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set
open Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- The all-real piece map selects from exactly the finite family used
for global original floors. Interpolation is performed after raw common
choice, so its additional `N^(1/J)` cost never enters the raw lists. -/
theorem exists_discovery_piece_selector {N H a : ℝ} (hN : 1 < N) (ha : 0 ≤ a)
    (M J C : ℕ) (hM : 1 ≤ M) (hJ : 1 ≤ J) (hcost : N ^ (1 / (M : ℝ)) ≤ H) :
    let β := fun i : Fin (C * J + 1) => N ^ (-upperGridExponent M (a + (i : ℝ) / J))
    ∃ pick : ℝ → Fin (C * J + 1),
      (∀ r, 0 < β (pick r)) ∧
      (∀ r, Measurable (fun l : ScalarLine => cell (β (pick r)) l.2)) ∧
      ∀ r, N ^ (-(C : ℝ)) ≤ r → r ≤ 1 →
        β (pick r) ≤ N ^ (-a) * r ∧
          N ^ (-a) * r ≤ (H * N ^ (1 / (J : ℝ))) * β (pick r) ∧
          ∀ (q : Fin 5 → ℤ) (l l' : ScalarLine),
            cell (β (pick r)) l.2 = cell (β (pick r)) l'.2 →
              ‖Zoom.coeff (N ^ (-a)) q l - Zoom.coeff (N ^ (-a)) q l'‖ ≤ r := by
  classical
  dsimp only
  let β := fun i : Fin (C * J + 1) => N ^ (-upperGridExponent M (a + (i : ℝ) / J))
  have hN₀ : 0 < N := by linarith
  have hρ : 0 < N ^ (-a) := Real.rpow_pos_of_pos hN₀ _
  have hQ : 0 ≤ N ^ (1 / (J : ℝ)) := Real.rpow_nonneg hN₀.le _
  have hselect : ∀ r : Icc (N ^ (-(C : ℝ))) 1,
      ∃ i : Fin (C * J + 1), β i ≤ N ^ (-a) * r ∧
        N ^ (-a) * r ≤ (H * N ^ (1 / (J : ℝ))) * β i := by
    intro r
    obtain ⟨_, ⟨i, rfl⟩, _, hle, hge⟩ :=
      (discovery_scale_rounding hN J C hJ).finer r r.property.1 r.property.2
    have hw := discovery_prepared_scale hN.le ha hM hJ hcost i
    refine ⟨i, hw.2.2.1.trans (mul_le_mul_of_nonneg_left hle hρ.le), ?_⟩
    calc
      _ ≤ N ^ (-a) * (N ^ (1 / (J : ℝ)) * powerWidth N J i) :=
        mul_le_mul_of_nonneg_left hge hρ.le
      _ = N ^ (1 / (J : ℝ)) * (N ^ (-a) * powerWidth N J i) := by ring
      _ ≤ N ^ (1 / (J : ℝ)) * (H * β i) := mul_le_mul_of_nonneg_left hw.2.2.2 hQ
      _ = _ := by ring
  choose selected hle hge using hselect
  let pick (r : ℝ) : Fin (C * J + 1) :=
    if hr : r ∈ Icc (N ^ (-(C : ℝ))) 1 then selected ⟨r, hr⟩ else ⟨0, by omega⟩
  refine ⟨pick, fun _ => Real.rpow_pos_of_pos hN₀ _,
    fun _ => measurable_cell _ measurable_snd, ?_⟩
  intro r hr hr₁
  have heq : pick r = selected ⟨r, hr, hr₁⟩ := dite_eq_left ⟨hr, hr₁⟩
  have hw : β (pick r) ≤ N ^ (-a) * r ∧
      N ^ (-a) * r ≤ (H * N ^ (1 / (J : ℝ))) * β (pick r) := by
    rw [heq]
    exact ⟨hle ⟨r, hr, hr₁⟩, hge ⟨r, hr, hr₁⟩⟩
  refine ⟨hw.1, hw.2, ?_⟩
  intro q l l' hbin
  apply (pi_norm_le_iff_of_nonneg ((Real.rpow_pos_of_pos hN₀ _).trans_le hr).le).mpr
  intro e
  exact Zoom.coeff_piece_diameter hρ (Real.rpow_pos_of_pos hN₀ _) hw.1 q hbin e

end

end Submission.Obl.k4_scalar_graph_residual_discovery
