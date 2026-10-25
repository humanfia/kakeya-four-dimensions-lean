/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ScalarSupportLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarStripLists
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarCovering

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set

/-- Combine the normal-strip counts in the finitely many coarse physical
cells of a coefficient world. This is the final list used for local
finite-grid scalar support covers. -/
theorem scalar_support_bins_of_cell_strip_lists {X Q : Type*} [DecidableEq Q]
    (E : Set X) (S : X → ℝ) (coarse : X → Q) (n : Q → X → ℝ) (shift : Q → ℝ)
    {ρ r B : ℝ} (hr : 0 < r) (cells : Finset Q)
    (hcell : ∀ x ∈ E, coarse x ∈ cells)
    (hnear : ∀ x ∈ E, |S x - (n (coarse x) x / ρ - shift (coarse x))| ≤ r)
    (strips : Q → Finset ℤ) (hcount : ∀ q ∈ cells, ((strips q).card : ℝ) ≤ B)
    (hstrip : ∀ x ∈ E, ⌊n (coarse x) x / (ρ * r)⌋ ∈ strips (coarse x)) :
    ∃ L : Finset ℤ, (L.card : ℝ) ≤ 8 * (cells.card : ℝ) * B ∧
      ∀ x ∈ E, ⌊S x / r⌋ ∈ L := by
  classical
  have hlocal (q : Q) := scalar_bins_of_normal_strip_list {x ∈ E | coarse x = q} S (n q)
    hr (shift q)
    (fun x hx => by simpa only [hx.2] using hnear x hx.1)
    (strips q) (fun x hx => by simpa only [hx.2] using hstrip x hx.1)
  choose L hL hmem using hlocal
  refine ⟨cells.biUnion L, ?_, ?_⟩
  · calc
      ((cells.biUnion L).card : ℝ) ≤ ∑ q ∈ cells, ((L q).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ cells, (8 * ((strips q).card : ℝ)) := Finset.sum_le_sum (fun q _ => hL q)
      _ ≤ ∑ _q ∈ cells, (8 * B) := Finset.sum_le_sum
        (fun q hq => mul_le_mul_of_nonneg_left (hcount q hq) (by norm_num))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨coarse x, hcell x hx, hmem _ x ⟨hx, rfl⟩⟩

end Submission.Obl.k4_scalar_graph_residual_discovery
