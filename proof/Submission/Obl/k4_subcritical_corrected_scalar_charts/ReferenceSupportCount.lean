/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ReferenceSupportCount.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeSupportCount

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

/-- The common contact frame needs only bounds for its reference position and
velocity. Its tilt is a unit time, so its source mesh resolves at the h² scale. -/
theorem reference_matrix_row_bound {q B δ p v τ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hp : |p| ≤ B) (hv : |v| ≤ B) (hτ : |τ| ≤ 1)
    (e : Fin 3) :
    (∑ j, |nativeFrameMatrix q v p τ e j| * δ) ≤ 9 * B * δ / q ^ 2 := by
  let c : Fin 5 → ℝ := ![0, v, 0, -p - τ * v, τ]
  have htv : |τ * v| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul hτ hv (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hcv : |-(p) - τ * v| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by rw [abs_neg]; linarith)
  have hc : ∀ e, |c e| ≤ 3 * B := by
    intro e
    fin_cases e <;> dsimp [c] <;> (try simp only [abs_zero]) <;> linarith
  have hh := atlas_matrix_row_bound hq hq1 (show 1 ≤ 3 * B by linarith) hδ c hc e
  change (∑ j, |nativeFrameMatrix q v (-(-p - τ * v) - τ * v) τ e j| * δ) ≤ _ at hh
  rw [show -(-p - τ * v) - τ * v = p by ring] at hh
  convert hh using 1 <;> ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The contact enlargement may be centered on the scalar reference motion,
rather than on a pre-existing native entry. Original descendant floors still
give the same (A0/ai)^d count with any prescribed power loss. -/
theorem Prepared.eventually_reference_descendant_count (h : cfg.Prepared) {s₀ s ε : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
        (ip : Fin (cfg.n k s₀)) (S : Finset (Fin (cfg.n k s))) (τ p r v : ℝ),
      |τ| ≤ 1 → |p| ≤ 3 * cfg.K k → |v| ≤ 3 * cfg.K k →
      (∀ i ∈ S, ∀ y ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i), ∀ e,
        |nativeFrame (cfg.timeLength k s) τ p r v p τ
          (originalBase (cfg.b k y.1) y.2) e| ≤ 320 * cfg.K k ^ 4) →
      (∀ i ∈ S, cfg.A k s i ⊆ cfg.A k s₀ ip) →
      (∀ i ∈ S, I (cfg.T k s) (cfg.j k s i) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip)) →
      (S.card : ℝ) ≤ cfg.N k ^ ε *
        ((cfg.N k ^ (-s₀)) / (cfg.N k ^ (-s))) ^ cfg.d := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hgap : -(40 * s) + 2 * cfg.κ * s < 0 := by nlinarith [h.rate_le_one]
  have hresolve := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    3 hgap (show (0 : ℝ) ≤ 27 by norm_num)
  have hcoef := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    17 (show (0 : ℝ) < ε from hε) (show (0 : ℝ) ≤ 162000 * 320 ^ 3 by norm_num)
  filter_upwards [h.eventually_native_mesh hspos,
    h.eventually_original_hidden_caps (show 0 < 40 * s by positivity) hs₀.le,
    hresolve, hcoef] with k hmesh hcap hres hcoef
  intro parent child ip S τ p r v hτ hp hv hbox hA hI
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hq1 : cfg.timeLength k s ≤ 1 := by
    unfold timeLength
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hinv : (cfg.timeLength k s)⁻¹ ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) := by
    simpa only [timeLength, inv_inv] using child.assignments.time_upper
  have hinv2 : (cfg.timeLength k s ^ 2)⁻¹ ≤ cfg.K k ^ 2 * cfg.N k ^ (2 * cfg.κ * s) := by
    calc
      _ = ((cfg.timeLength k s)⁻¹) ^ 2 := by rw [inv_pow]
      _ ≤ (cfg.K k * cfg.N k ^ (cfg.κ * s)) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hinv 2
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast (cfg.N k ^ (cfg.κ * s)) 2, ← Real.rpow_mul hN.le]
        congr 1
        norm_num
        ring
  have hδ : 0 < cfg.N k ^ (-(40 * s)) := Real.rpow_pos_of_pos hN _
  have hmat : ∀ e, (∑ j, |nativeFrameMatrix (cfg.timeLength k s) v p τ e j| *
      cfg.N k ^ (-(40 * s))) ≤ 1 := by
    intro e
    calc
      _ ≤ 9 * (3 * cfg.K k) * cfg.N k ^ (-(40 * s)) / cfg.timeLength k s ^ 2 :=
        reference_matrix_row_bound hq hq1 (by linarith) hδ.le hp hv hτ e
      _ ≤ 9 * (3 * cfg.K k) * cfg.N k ^ (-(40 * s)) *
          (cfg.K k ^ 2 * cfg.N k ^ (2 * cfg.κ * s)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv2 (by positivity)
      _ = 27 * cfg.K k ^ 3 * cfg.N k ^ (-(40 * s) + 2 * cfg.κ * s) := by
        rw [Real.rpow_add hN]
        ring
      _ ≤ 1 := by simpa only [Real.rpow_zero] using hres.le
  have hH : 1 ≤ 320 * cfg.K k ^ 4 := by nlinarith [one_le_pow₀ hK (n := 4)]
  have hm : 108 * cfg.K k ^ 4 * cfg.N k ^ (-(40 * s)) ≤ cfg.N k ^ (-s₀) :=
    (hmesh child.assignments).1.trans
      (Real.rpow_le_rpow_of_exponent_le (hN1 k) (neg_le_neg hs))
  have hc := parent.count_descendants_in_box h child ip S hδ hH hm hcap
    τ p r v p τ hmat hbox hA hI
  have heq : 162000 * cfg.K k ^ 5 * (320 * cfg.K k ^ 4) ^ 3 =
      (162000 * (320 : ℝ) ^ 3) * cfg.K k ^ 17 := by ring
  rw [heq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (by simpa only [Real.rpow_zero, mul_one] using hcoef.le) (by positivity))

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
