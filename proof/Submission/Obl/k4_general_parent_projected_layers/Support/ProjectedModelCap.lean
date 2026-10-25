/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ProjectedModelCap.lean.
   The palette integration uses the checked local projected_cap_with_palette. -/
import Submission.Obl.k4_general_parent_projected_layers.Model
import Submission.Obl.k4_general_parent_projected_layers.Caps
import Submission.Obl.k4_general_parent_projected_layers.Support.ProjectedCellCap

/-! Applying moving-box integration to the exact prepared-model joint cap. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set MvPolynomial

noncomputable section

theorem prepared_projected_cell_cap {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) (k : ℕ)
    (hN : 0 < p.N k) (hK : 0 ≤ p.K k) (hpi : IsProbabilityMeasure (a.pi k))
    (r s v sigma g L y₀ y₁ z₀ z₁ : ℝ)
    (hs : 0 < sigma) (hg : 0 < g)
    (hdr : p.N k ^ (-r) ≤ sigma)
    (hdz : p.N k ^ (-r) ≤ 2 * p.N k ^ (-v))
    (hdy : p.N k ^ (-r) ≤ g * sigma)
    (hL : 0 ≤ L) (hz₁ : |z₁| ≤ L) (hy₁ : |y₁| ≤ L)
    (hmz : L * p.N k ^ (-r) ≤ 2 * p.N k ^ (-v))
    (hmy : L * p.N k ^ (-r) ≤ g * sigma)
    (hcap : ∀ (q : Fin 3 → ℤ) (j v₀ : ℤ),
      a.mu k {w | a.cell (p.N k) r k w = q ∧
        ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-s)⌋ = j ∧
        ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
          ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * s)) *
            a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = v₀})
    (q : Fin 2 → ℤ) (j v₀ : ℤ) :
    a.mu k {w | w.2 ∈ Icc (0 : ℝ) 1 ∧
      a.b k w.1 ∈ majorGroup (p.N k ^ (-v)) z₀ z₁ ∧
      projectedCell sigma g y₀ y₁ (a.b k w.1) w.2 = q ∧
      ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-s)⌋ = j ∧
      ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
      ENNReal.ofReal (1200 * p.K k * sigma ^ 2 * p.N k ^ (-v) * g *
        (p.N k ^ (-s)) ^ p.d) * a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = v₀} := by
  letI := hpi
  have hd : 0 < p.N k ^ (-r) := Real.rpow_pos_of_pos hN _
  have hpower : p.K k * p.N k ^ (-3 * r - p.d * s) =
      (p.K k * (p.N k ^ (-s)) ^ p.d) * (p.N k ^ (-r)) ^ 3 := by
    calc
      _ = p.K k * p.N k ^ ((-s) * p.d + (-r) * (3 : ℕ)) := by
        congr 2
        norm_num
        ring
      _ = _ := by
        rw [Real.rpow_add hN, Real.rpow_mul hN.le (-s) p.d,
          Real.rpow_mul_natCast hN.le (-r) 3]
        ring

  let condition : α × ℝ → Prop := fun w =>
    ⌊eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-s)⌋ = j ∧
      ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀
  have hc (q' : Fin 3 → ℤ) :
      a.mu k {w | baseMesh (p.N k ^ (-r)) (basePoint (a.b k w.1) w.2) = q' ∧ condition w} ≤
        ENNReal.ofReal ((p.K k * (p.N k ^ (-s)) ^ p.d) * (p.N k ^ (-r)) ^ 3) *
          a.pi k {w | ⌊w / p.N k ^ (-v)⌋ = v₀} := by
    have hh := hcap q' j v₀
    change a.mu k {w | baseMesh (p.N k ^ (-r)) (basePoint (a.b k w.1) w.2) = q' ∧ condition w} ≤ _ at hh
    simpa only [hpower] using hh
  have H := projected_cap_with_palette (a.mu k) (a.b k) condition
    (y₀ := y₀) (z₀ := z₀) (measure_ne_top (a.pi k) _) hd hs hg
    (Real.rpow_nonneg hN.le _) hdr hdz hdy hL
    (mul_nonneg hK (Real.rpow_nonneg (Real.rpow_nonneg hN.le _) _))
    hz₁ hy₁ hmz hmy hc q
  have heq : 1200 * (p.K k * (p.N k ^ (-s)) ^ p.d) * sigma ^ 2 * p.N k ^ (-v) * g =
      1200 * p.K k * sigma ^ 2 * p.N k ^ (-v) * g * (p.N k ^ (-s)) ^ p.d := by ring
  simpa only [heq] using H

end

end Submission.Obl.k4_general_parent_projected_layers
