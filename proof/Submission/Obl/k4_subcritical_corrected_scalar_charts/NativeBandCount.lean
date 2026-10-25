/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeBandCount.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeBandCaps
import Submission.Obl.k4_subcritical_corrected_scalar_charts.OriginalCapUse

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Count the full original child entries in one common native box and one
old affine band. The original q⁴ and hidden-width factors cancel exactly. -/
theorem NativeLevel.count_in_old_band (h : cfg.Prepared) {k : ℕ} {s₀ s δ H R : ℝ}
    (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
    (ip : Fin (cfg.n k s₀)) (S : Finset (Fin (cfg.n k s)))
    (hδ : 0 < δ) (hH : 1 ≤ H) (hR : 0 ≤ R)
    (hmesh : 108 * cfg.K k ^ 4 * δ ≤ cfg.N k ^ (-s₀))
    (hcap : ∀ q n,
      cfg.μ k {p | baseMesh δ (originalBase (cfg.b k p.1) p.2) = q ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / cfg.N k ^ (-s₀)⌋ = n} ≤
        ENNReal.ofReal ((cfg.K k * (cfg.N k ^ (-s₀)) ^ cfg.d) * δ ^ 3))
    (t₀ p r v z τ : ℝ)
    (hresolve : ∀ e, (∑ j, |nativeFrameMatrix (cfg.timeLength k s) v z τ e j| * δ) ≤ 1)
    (hbox : ∀ i ∈ S, ∀ y ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i), ∀ e,
      |nativeFrame (cfg.timeLength k s) t₀ p r v z τ
        (originalBase (cfg.b k y.1) y.2) e| ≤ H)
    (hband : ∀ᵐ y ∂cfg.μ k, ∀ i ∈ S,
      y ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i) →
      |cfg.b k y.1 2 + y.2 * cfg.b k y.1 5 -
        affineField (parent.L ip) (originalBase (cfg.b k y.1) y.2)| ≤
          R * cfg.N k ^ (-s₀)) :
    (S.card : ℝ) ≤ 16200 * (4 * R + 6) * cfg.K k ^ 4 * H ^ 3 *
      ((cfg.N k ^ (-s₀)) / (cfg.N k ^ (-s))) ^ cfg.d := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  let W := fun i : Fin (cfg.n k s) => cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)
  let x := fun y : α × ℝ => originalBase (cfg.b k y.1) y.2
  let X := fun y : α × ℝ => cfg.b k y.1 2 + y.2 * cfg.b k y.1 5
  let o := affineField (parent.L ip)
  let G := {y : α × ℝ | (∀ e, |nativeFrame (cfg.timeLength k s) t₀ p r v z τ (x y) e| ≤ H) ∧
    |X y - o (x y)| ≤ R * cfg.N k ^ (-s₀)}
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hA₀ : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hN _
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  let V := cfg.K k * (cfg.N k ^ (-s₀)) ^ cfg.d
  let m := cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3
  let C := 16200 * (4 * R + 6) * V * cfg.timeLength k s ^ 4 * H ^ 3
  have hm : 0 < m := by dsimp [m]; positivity
  have hC : 0 ≤ C := by dsimp [C, V]; positivity
  have hcG : cfg.μ k G ≤ ENNReal.ofReal C := by
    apply native_band_box_cap (cfg.μ k) x X o
      (fun q => o (fun e => δ * (q e : ℝ))) hq hδ hA₀ hH
      (by positivity) hR t₀ p r v z τ hresolve ?_ hcap
    intro q y hy
    have hh := affineField_lipschitz (parent.L ip)
      (by positivity : 0 ≤ 36 * cfg.K k ^ 4) hδ.le (parent.slope ip)
      (z := x y) (w := fun e => δ * (q e : ℝ)) (by
        intro e
        have he := Submission.Obl.k4_scalar_coefficient_clustering.floor_scaled_error hδ (x y e)
        have hcode : ⌊x y e / δ⌋ = q e := congrFun hy e
        simpa only [hcode] using he)
    exact hh.trans (by convert hmesh using 1 <;> ring)
  have hcount : (S.card : ℝ) ≤ C / m := by
    apply original_witness_count_ae (cfg.μ k) W S G
      (fun i _ => (child.fitted_measurable i).prod measurableSet_Icc) ?_ ?_ hm hC
      (fun i _ => child.witness_floor i) hcG
    · filter_upwards [true_assignments_ae_unique (cfg.ν k) (cfg.μ k) (ENNReal.ofReal (cfg.K k))
        (h.basic k).2.2.2.1 (cfg.T k s) (cfg.j k s) (cfg.A k s)
        child.assignments.disjoint] with y hy
      intro i hi j hj hyi hyj
      exact hy i j (child.assignments.fitted_subset i hyi.1) hyi.2
        (child.assignments.fitted_subset j hyj.1) hyj.2
    · filter_upwards [hband] with y hy
      intro i hi hyi
      exact ⟨hbox i hi y hyi, hy i hi hyi⟩
  refine hcount.trans_eq ?_
  dsimp [C, V, m]
  rw [Real.div_rpow hA₀.le ha.le]
  have had : (cfg.N k ^ (-s)) ^ cfg.d ≠ 0 := (Real.rpow_pos_of_pos ha _).ne'
  field_simp

/-- Every original descendant retains the parent's full old band almost
everywhere. This is enough to count its whole original witness. -/
theorem NativeLevel.count_descendants_in_box (h : cfg.Prepared) {k : ℕ} {s₀ s δ H : ℝ}
    (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
    (ip : Fin (cfg.n k s₀)) (S : Finset (Fin (cfg.n k s)))
    (hδ : 0 < δ) (hH : 1 ≤ H)
    (hmesh : 108 * cfg.K k ^ 4 * δ ≤ cfg.N k ^ (-s₀))
    (hcap : ∀ q n,
      cfg.μ k {p | baseMesh δ (originalBase (cfg.b k p.1) p.2) = q ∧
        ⌊(cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) / cfg.N k ^ (-s₀)⌋ = n} ≤
        ENNReal.ofReal ((cfg.K k * (cfg.N k ^ (-s₀)) ^ cfg.d) * δ ^ 3))
    (t₀ p r v z τ : ℝ)
    (hresolve : ∀ e, (∑ j, |nativeFrameMatrix (cfg.timeLength k s) v z τ e j| * δ) ≤ 1)
    (hbox : ∀ i ∈ S, ∀ y ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i), ∀ e,
      |nativeFrame (cfg.timeLength k s) t₀ p r v z τ
        (originalBase (cfg.b k y.1) y.2) e| ≤ H)
    (hA : ∀ i ∈ S, cfg.A k s i ⊆ cfg.A k s₀ ip)
    (hI : ∀ i ∈ S, I (cfg.T k s) (cfg.j k s i) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip)) :
    (S.card : ℝ) ≤ 162000 * cfg.K k ^ 5 * H ^ 3 *
      ((cfg.N k ^ (-s₀)) / (cfg.N k ^ (-s))) ^ cfg.d := by
  classical
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hb (i : Fin (cfg.n k s)) :
      ∀ᵐ y ∂cfg.μ k, i ∈ S → y ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i) →
        |cfg.b k y.1 2 + y.2 * cfg.b k y.1 5 -
          affineField (parent.L ip) (originalBase (cfg.b k y.1) y.2)| ≤
            cfg.K k * cfg.N k ^ (-s₀) := by
    by_cases hi : i ∈ S
    · have hp := nested_assignment_parent_mem (cfg.ν k) (cfg.μ k) (ENNReal.ofReal (cfg.K k))
        (h.basic k).2.2.2.1 (cfg.T k s₀) (cfg.j k s₀) (cfg.A k s₀) (cfg.B k s₀)
        parent.assignments.disjoint parent.assignments.fitted_subset parent.assignments.covers
        (cfg.B k s i) (I (cfg.T k s) (cfg.j k s i)) ip
        ((child.assignments.fitted_subset i).trans (hA i hi)) (hI i hi)
      filter_upwards [hp] with y hy
      intro _ hyi
      exact parent.fit ip y.1 (hy hyi.1 hyi.2) y.2 (hI i hi hyi.2)
    · exact Filter.Eventually.of_forall fun _ hi' => False.elim (hi hi')
  have hcount := parent.count_in_old_band h child ip S hδ hH hK0 hmesh hcap
    t₀ p r v z τ hresolve hbox (ae_all_iff.mpr hb)
  refine hcount.trans ?_
  have hc : 16200 * (4 * cfg.K k + 6) * cfg.K k ^ 4 ≤ 162000 * cfg.K k ^ 5 := by
    calc
      _ ≤ 16200 * (10 * cfg.K k) * cfg.K k ^ 4 := by gcongr; linarith
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
