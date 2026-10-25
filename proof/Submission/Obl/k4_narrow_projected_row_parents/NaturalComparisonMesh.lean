import Submission.Obl.k4_narrow_projected_row_parents.ComparisonFrameBudgets
import Submission.Obl.k4_narrow_projected_row_parents.ComparisonMeshReady
import Submission.Obl.k4_narrow_projected_row_parents.NaturalCommonScales
import Submission.Obl.k4_narrow_projected_row_parents.NaturalAreaBounds

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Filter
open Submission.Obl.k4_general_parent_projected_layers
open Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open ComparisonFrame

variable {α : Type} [MeasurableSpace α]

/-- The naturally refined major width admits common time and area scales,
one fixed physical mesh, and the exact original native caps needed by the
single-index comparison. All remaining chart and error budgets are those of
`ComparisonFrame`. -/
theorem natural_comparison_mesh (p : Parameters) (hp : p.Valid)
    (a : PreparedModel α) (hcaps : a.Caps p) {s mOld B R₀ : ℝ}
    (hs : 0 < s) (hmOld : 0 < mOld) (hatlas : ∀ᶠ k in atTop, a.AtlasAt p R₀ k s)
    (H β χ : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k) (hHsub : Model.Subpow p.N H)
    (hβ : ∀ k, 0 < β k) (hβlower : ∀ᶠ k in atTop, p.N k ^ (-B - 1) ≤ β k)
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (hχ : ∀ k,
      min (p.N k ^ (-mOld)) (width p k s * a.q k s * narrow p k s) /
          (2 * stableDivisor (p.K k) n) ≤ χ k ∧
      χ k ≤ min (p.N k ^ (-mOld)) (width p k s * a.q k s * narrow p k s) /
        stableDivisor (p.K k) n) :
    ∃ sc : (k : ℕ) → CommonScaleChoice (a.q k s) (β k) (narrow p k s) (χ k)
        (nativeBound (p.K k) n)⁻¹ (stableDivisor (p.K k) n),
      ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, ∃ v : ℝ,
        χ k = p.N k ^ (-v) ∧
        (2 * p.K k + 1) * p.N k ^ (-r) ≤
          100 * (sc k).q * zoomMesh (p.N k) C (p.K k) (H k) s n ∧
        (2 * p.K k + 1) * p.N k ^ (-r) ≤
          100 * χ k * zoomMesh (p.N k) C (p.K k) (H k) s n ∧
        (2 * p.K k + 1) * p.N k ^ (-r) ≤
          100 * (sc k).m * zoomMesh (p.N k) C (p.K k) (H k) s n ∧
        ∀ t : ℝ, 0 ≤ t → t ≤ s → ∀ (z : Fin 3 → ℤ) (j v₀ : ℤ),
          a.mu k {w | a.cell (p.N k) r k w = z ∧
            ⌊MvPolynomial.eval (a.x k w.1 w.2) (a.P k) / p.N k ^ (-t)⌋ = j ∧
            ⌊a.b k w.1 3 / p.N k ^ (-v)⌋ = v₀} ≤
            ENNReal.ofReal (p.K k * p.N k ^ (-3 * r - p.d * t)) *
              a.pi k {w : ℝ | ⌊w / p.N k ^ (-v)⌋ = v₀} := by
  classical
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  have hN0 : ∀ k, 0 < p.N k := fun k => by linarith [hp.1 k]
  have hK : ∀ k, 1 ≤ p.K k := hp.2.2.1.1
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hQ : ∀ k, 0 < a.q k s := fun k => by unfold PreparedModel.q; positivity
  have hQ1 : ∀ k, a.q k s ≤ 1 := by
    intro k
    unfold PreparedModel.q
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hg : ∀ k, 0 < narrow p k s := fun k => Real.rpow_pos_of_pos (hN0 k) _
  have hg1 : ∀ k, narrow p k s ≤ 1 := by
    intro k
    exact Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by nlinarith)
  have ha0 : ∀ k, 0 ≤ width p k s := fun k => Real.rpow_nonneg (hN0 k).le _
  have ha1 : ∀ k, width p k s ≤ 1 := fun k =>
    Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (neg_nonpos.mpr hs.le)
  let R : ℕ → ℝ := fun k => stableDivisor (p.K k) n
  have hR1 : ∀ k, 1 ≤ R k := fun k => (stableDivisor_bounds (hK k) n).1
  have hRpos : ∀ k, 0 < R k := fun k => zero_lt_one.trans_le (hR1 k)
  obtain ⟨_, hRsub, _, _⟩ := subpower_budgets hN1 hp.2.1 hK hH hp.2.2.1.2 hHsub C hC n
  have hsc (k : ℕ) : Nonempty (CommonScaleChoice (a.q k s) (β k) (narrow p k s) (χ k)
      (nativeBound (p.K k) n)⁻¹ (R k)) := by
    apply natural_common_scales (hQ k) (hQ1 k) (hβ k) (hg k) (hg1 k) (hR1 k)
      (stableDivisor_bounds (hK k) n).2 (ha0 k) (ha1 k)
    exact (hχ k).2
  let sc := fun k => Classical.choice (hsc k)
  let hi : ℝ := max mOld ((p.kappa + p.ell + 1) * s + 1) + 2
  let E : ℝ := max ((p.kappa + p.ell) * s + 1) (B + 1) + 1
  have hmajor := eventually_natural_major_lower p hp a hs.le mOld R hR1 hRsub
  have harea := eventually_natural_area_lower p hp a s B β R hβlower hR1 hRsub
  have hχband : ∀ᶠ k in atTop, p.N k ^ (-hi) ≤ χ k ∧ χ k ≤ p.N k ^ (-mOld) := by
    filter_upwards [hatlas, hmajor] with k hat hm
    refine ⟨(hm R₀ hat).trans (hχ k).1, ?_⟩
    calc χ k ≤ min (p.N k ^ (-mOld)) (width p k s * a.q k s * narrow p k s) / R k :=
           (hχ k).2
         _ ≤ p.N k ^ (-mOld) / R k := div_le_div_of_nonneg_right (min_le_left _ _) (hRpos k).le
         _ ≤ p.N k ^ (-mOld) := div_le_self (Real.rpow_nonneg (hN0 k).le _) (hR1 k)
  have hmband : ∀ᶠ k in atTop, p.N k ^ (-E) ≤ (sc k).m ∧ (sc k).m ≤ (sc k).q := by
    filter_upwards [hatlas, harea] with k hat ha
    refine ⟨?_, (sc k).m_le_q⟩
    have hid : min (a.q k s * narrow p k s) (β k) / R k = (sc k).m := by
      rw [(sc k).natural_area]
      exact mul_div_cancel_left₀ _ (hRpos k).ne'
    rw [← hid]
    exact ha R₀ hat
  have hzoom := eventually_zoomMesh_bounds hN1 hp.2.1 hK hH hp.2.2.1.2 hHsub C hC n hs
  have hσ : ∀ᶠ k in atTop, p.N k ^ (-(s + 1)) ≤ zoomMesh (p.N k) C (p.K k) (H k) s n :=
    hzoom.mono fun k hk => hk.2.2.1
  obtain ⟨r, hr, hready⟩ := eventually_comparison_mesh_ready p hp a hcaps hs.le hmOld
    (fun k => (sc k).q) χ (fun k => (sc k).m)
    (fun k => zoomMesh (p.N k) C (p.K k) (H k) s n) hχband hmband hσ
  exact ⟨sc, r, hr, hready⟩

end Submission.Obl.k4_narrow_projected_row_parents
