/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/NativeComparison.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.ChildComparison
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeGeometry

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Original nested assignments supply every witness and geometry hypothesis
of the finite-mesh affine comparison.  Neither assignment is restricted to the
current residual law.  The affine tables may be those chosen by `affine_table`. -/
theorem compare_nested_affine_tables {k : ℕ} {s t r : ℝ}
    (parent : cfg.AssignmentLevel k s) (child : cfg.AssignmentLevel k t)
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 1 ≤ cfg.N k) (hK : 1 ≤ cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (hst : s ≤ t)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (i : Fin (cfg.n k t)) (j : Fin (cfg.n k s))
    (hA : cfg.A k t i ⊆ cfg.A k s j)
    (hI : Data.I (cfg.T k t) (cfg.j k t i) ⊆ Data.I (cfg.T k s) (cfg.j k s j))
    (L P : Fin 4 → ℝ) (hL : ∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4)
    (hchild : ∀ l ∈ cfg.B k t i, ∀ u ∈ Data.I (cfg.T k t) (cfg.j k t i),
      |(cfg.x k l u) 3 - (L 0 + ∑ e : Fin 3, L e.succ *
        cfg.originalBasePoint k (l, u) e)| ≤ cfg.K k * cfg.N k ^ (-t))
    (hparent : ∀ l ∈ cfg.B k s j, ∀ u ∈ Data.I (cfg.T k s) (cfg.j k s j),
      |(cfg.x k l u) 3 - (P 0 + ∑ e : Fin 3, P e.succ *
        cfg.originalBasePoint k (l, u) e)| ≤ cfg.K k * cfg.N k ^ (-s))
    (hcap : ∀ (p : Fin 3 → ℤ) (v : ℤ),
      cfg.μ k {ω | cfg.z k (cfg.N k) r ω = p ∧
        ⌊(cfg.x k ω.1 ω.2) 3 / (cfg.N k ^ (-t))⌋ = v} ≤
          ENNReal.ofReal (cfg.K k * cfg.N k ^ (-3 * r - cfg.d * t)))
    {H : ℕ} (hH : 0 < H)
    (hmesh : cfg.N k ^ (-r) ≤ cfg.timeLength k t / H)
    (hmesh' : (2 * cfg.K k + 1) * cfg.N k ^ (-r) ≤
      2 * cfg.K k * cfg.timeLength k t * cfg.N k ^ (-cfg.ℓ * t) / H)
    (hfitmesh : 24 * cfg.K k ^ 4 * cfg.N k ^ (-r) ≤ cfg.N k ^ (-t))
    (hfine : 69120 * cfg.K k ^ 8 ≤ (H : ℝ)) :
    (∀ v ∈ cfg.originalTrueBox k t i,
      |(L 0 - P 0) + ∑ e : Fin 3, (L e.succ - P e.succ) * v e| ≤
        262144 * cfg.K k ^ 9 * cfg.N k ^ (-s)) ∧
    (∀ v ∈ cfg.originalTrueBox k t i,
      |L 3 - P 3| ≤ (262144 * cfg.K k ^ 9 * cfg.N k ^ (-s)) / cfg.timeLength k t ^ 2 ∧
      |L 1 - P 1 - v 1 * (L 3 - P 3)| + |L 2 - P 2 + v 0 * (L 3 - P 3)| ≤
        8 * cfg.K k * (262144 * cfg.K k ^ 9 * cfg.N k ^ (-s)) / cfg.timeLength k t) := by
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hq : 0 < cfg.timeLength k t := by unfold Data.timeLength; positivity
  have hg : 0 < cfg.N k ^ (-cfg.ℓ * t) := Real.rpow_pos_of_pos hNp _
  let tc := cfg.originalTimeCenter k t i
  let zc := cfg.c k t i 0 + tc * cfg.c k t i 1
  let yc := cfg.c k t i 2 + tc * cfg.c k t i 3 + cfg.c k t i 4 * zc
  let E := (cfg.B k t i ∩ cfg.B k s j) ×ˢ Data.I (cfg.T k t) (cfg.j k t i)
  have hmass : ENNReal.ofReal (cfg.timeLength k t ^ 4 * (cfg.N k ^ (-t)) ^ cfg.d /
      cfg.K k ^ 3) ≤ cfg.μ k E := by
    rw [show cfg.μ k E = cfg.μ k (cfg.B k t i ×ˢ Data.I (cfg.T k t) (cfg.j k t i)) from
      cfg.inherited_witness_mass parent child hdom i j hA hI]
    exact cfg.original_witness_floor child hν hNp hKp hℓ i
  have htime := time_length_comparison hNp hKp child.time_lower child.time_upper
  have hqg : cfg.timeLength k t ≤ cfg.K k * cfg.N k ^ (-cfg.ℓ * t) := by
    rw [hℓ]
    simpa only [Data.timeLength, mul_comm] using (div_le_iff₀ hKp).mp htime.1
  have hgq : cfg.N k ^ (-cfg.ℓ * t) ≤ cfg.K k * cfg.timeLength k t := by
    rw [hℓ]
    exact htime.2
  have hslopes : ∑ e : Fin 3, |L e.succ| ≤ 24 * cfg.K k ^ 4 := by
    calc
      _ ≤ ∑ _e : Fin 3, 8 * cfg.K k ^ 4 := Finset.sum_le_sum (fun e _ => hL e)
      _ = _ := by simp; ring
  have hresolve : cfg.N k ^ (-r) * ∑ e : Fin 3, |L e.succ| ≤ cfg.N k ^ (-t) := by
    calc
      _ ≤ cfg.N k ^ (-r) * (24 * cfg.K k ^ 4) :=
        mul_le_mul_of_nonneg_left hslopes (Real.rpow_nonneg hNp.le _)
      _ = 24 * cfg.K k ^ 4 * cfg.N k ^ (-r) := by ring
      _ ≤ _ := hfitmesh
  have hmesh₁ : (|cfg.c k t i 1| + 1) * cfg.N k ^ (-r) ≤
      2 * (cfg.K k * cfg.timeLength k t) / H := by
    calc
      _ ≤ (2 * cfg.K k) * cfg.N k ^ (-r) := by
        gcongr
        linarith [child.coefficient_bound i 1]
      _ ≤ (2 * cfg.K k) * (cfg.timeLength k t / H) :=
        mul_le_mul_of_nonneg_left hmesh (by positivity)
      _ = _ := by ring
  have hmesh₂ : (|cfg.c k t i 3| + |cfg.c k t i 4| + 1) * cfg.N k ^ (-r) ≤
      2 * (cfg.K k * cfg.timeLength k t * cfg.N k ^ (-cfg.ℓ * t)) / H := by
    calc
      _ ≤ (2 * cfg.K k + 1) * cfg.N k ^ (-r) := by
        gcongr
        linarith [child.coefficient_bound i 3, child.coefficient_bound i 4]
      _ ≤ _ := by simpa only [mul_assoc] using hmesh'
  have hplane := child.plane_center i
  have hplane₁ : |cfg.c k t i 3 + zc| ≤ cfg.K k * cfg.timeLength k t := by
    have heq : cfg.c k t i 3 + zc = cfg.c k t i 3 + cfg.c k t i 0 +
        (((cfg.j k t i : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k t * cfg.c k t i 1 := by
      dsimp [zc, tc, originalTimeCenter]
      ring
    rw [heq]
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans hplane
  have hplane₂ : |cfg.c k t i 4 - tc| ≤ cfg.K k * cfg.timeLength k t := by
    dsimp [tc, originalTimeCenter]
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans hplane
  have hbox (ω : α × ℝ) (hω : ω ∈ E) :
      |cfg.originalBasePoint k ω 0 - tc| ≤ cfg.timeLength k t / 2 ∧
      |cfg.originalBasePoint k ω 1 - zc - cfg.c k t i 1 *
        (cfg.originalBasePoint k ω 0 - tc)| ≤ cfg.K k * cfg.timeLength k t ∧
      |cfg.originalBasePoint k ω 2 - yc - cfg.c k t i 3 *
        (cfg.originalBasePoint k ω 0 - tc) - cfg.c k t i 4 *
        (cfg.originalBasePoint k ω 1 - zc)| ≤
          cfg.K k * cfg.timeLength k t * cfg.N k ^ (-cfg.ℓ * t) :=
    cfg.original_trueBox_centered i _ (cfg.original_witness_mem_trueBox child i ω ⟨hω.1.1, hω.2⟩)
  obtain ⟨hbound, hjet⟩ := original_child_affine_comparison (cfg.μ k) E
    (cfg.originalBasePoint k) (fun ω => (cfg.x k ω.1 ω.2) 3) L P tc zc yc
    (cfg.c k t i 1) (cfg.c k t i 3) (cfg.c k t i 4) (cfg.K k)
    (cfg.timeLength k t) (cfg.N k ^ (-cfg.ℓ * t)) (cfg.N k ^ (-r))
    (cfg.N k ^ (-t)) (cfg.N k ^ (-s)) cfg.d hH hK hq hg
    (Real.rpow_pos_of_pos hNp _) (Real.rpow_pos_of_pos hNp _) (Real.rpow_pos_of_pos hNp _)
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hqg hgq
    (child.coefficient_bound i 1) hplane₁ hplane₂ hmass hmesh hmesh₁ hmesh₂ hresolve
    (cfg.original_hidden_cell_cap hNp hcap)
    hbox (fun ω hω => hchild ω.1 hω.1.1 ω.2 hω.2)
    (fun ω hω => hparent ω.1 hω.1.2 ω.2 (hI hω.2)) hfine
  constructor
  · intro v hv
    have hvc := cfg.original_trueBox_centered i v hv
    exact hbound v hvc.1 hvc.2.1 hvc.2.2
  · intro v hv
    have hvc := cfg.original_trueBox_centered i v hv
    exact hjet (v 0) (v 1) hvc.1 hvc.2.1

/-- The genuine-box first jets give ordinary spatial gradient bounds, with
only one extra power of the original slack.  The comparison point may be any
point of the entire child box. -/
theorem ordinary_spatial_slopes_at_trueBox_point {k : ℕ} {s E : ℝ}
    (hK : 1 ≤ cfg.K k) (hE : 0 ≤ E) (i : Fin (cfg.n k s))
    (L P : Fin 4 → ℝ) (v : Fin 3 → ℝ) (hv : v ∈ cfg.originalTrueBox k s i)
    (hjet : |L 3 - P 3| ≤ E / cfg.timeLength k s ^ 2 ∧
      |L 1 - P 1 - v 1 * (L 3 - P 3)| + |L 2 - P 2 + v 0 * (L 3 - P 3)| ≤
        8 * cfg.K k * E / cfg.timeLength k s) :
    |L 2 - P 2| ≤ 9 * cfg.K k * E / cfg.timeLength k s ^ 2 ∧
      |L 3 - P 3| ≤ 9 * cfg.K k * E / cfg.timeLength k s ^ 2 := by
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hq1 : cfg.timeLength k s ≤ 1 := by
    unfold Data.timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have ht := cfg.original_trueBox_time_unit i v hv
  have ht1 : |v 0| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  exact spatial_slopes_of_native_jet hK hq hq1 hE ht1 hjet.1
    (by linarith [hjet.2, abs_nonneg (L 1 - P 1 - v 1 * (L 3 - P 3))])

end NativeModel
end Submission.Obl.k4_horizontal_strict_parameter_step
