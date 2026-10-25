-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CoarseFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.UniformFibers
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedGeometry
import Submission.WZ.Obl.wz_separated_projection_dichotomy.LineCounting

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- A cell family with comparable positive masses inherits the normalized
Frostman bound. The parameter `L` accounts for the retained source mass. -/
theorem ClosedFiniteFrostman.coarse_cells {δ C M L : ℝ} {S T : Finset Plane}
    (hF : ClosedFiniteFrostman δ C S) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hM : 0 < M) (hL : 0 ≤ L) (f : Plane → Plane)
    (hnear : ∀ x ∈ S, dist x (f x) ≤ δ)
    (hlower : ∀ y ∈ T, M ≤ ((S.filter (fun x => f x = y)).card : ℝ))
    (hmass : (S.card : ℝ) ≤ L * M * (T.card : ℝ)) :
    ClosedFiniteFrostman δ (2 * C * L) T := by
  classical
  intro z r hr
  have hrp : 0 < r := hδ.trans_le hr
  let U := T.filter (fun y => dist y z ≤ r)
  have hl := lower_fiber_count S U f
    (fun y hy => hlower y (Finset.mem_filter.mp hy).1)
  have hsub : S.filter (fun x => f x ∈ U) ⊆ S.filter (fun x => dist x z ≤ r + δ) := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hfx := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).2).2
    exact Finset.mem_filter.mpr ⟨hxS, (dist_triangle x (f x) z).trans (by linarith [hnear x hxS])⟩
  have hc : ((S.filter (fun x => f x ∈ U)).card : ℝ) ≤
      ((S.filter (fun x => dist x z ≤ r + δ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hFr : ((S.filter (fun x => dist x z ≤ r + δ)).card : ℝ) ≤
      C * (r + δ) * (S.card : ℝ) := by
    convert hF z (r + δ) (by linarith) using 1
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp
  have hbound : M * (U.card : ℝ) ≤ (2 * C * L) * r * (T.card : ℝ) * M := by
    calc M * (U.card : ℝ) ≤ ((S.filter (fun x => f x ∈ U)).card : ℝ) := hl
      _ ≤ C * (r + δ) * (S.card : ℝ) := hc.trans hFr
      _ ≤ C * (2 * r) * (L * M * (T.card : ℝ)) := by gcongr; linarith
      _ = _ := by ring
  have hcount : (U.card : ℝ) ≤ (2 * C * L) * r * (T.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hM).mp
    simpa only [mul_comm M] using hbound
  convert hcount using 1
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [U]


private theorem subtype_filter_card (S : Finset Plane) (P : Plane → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : S => P (x : Plane))).card = (S.filter P).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_coe_sort S (fun x => if P x then (1 : ℕ) else 0)

/-- Line nonconcentration survives replacement by nearby cell centers with
uniformly positive masses. The explicit budget permits either normalization
of the line Frostman constant. -/
theorem IndexedLineFrostman.coarse_cells {δ C D M L ζ : ℝ} {S T : Finset Plane}
    (hF : IndexedLineFrostman δ C ζ (fun x : S => (x : Plane)))
    (hδ : 0 < δ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 < M) (hζ : 0 ≤ ζ)
    (f : Plane → Plane) (hnear : ∀ x ∈ S, dist x (f x) ≤ δ)
    (hlower : ∀ y ∈ T, M ≤ ((S.filter (fun x => f x = y)).card : ℝ))
    (hmass : (S.card : ℝ) ≤ L * M * (T.card : ℝ))
    (hbudget : L * (2 * C) ^ ζ ≤ D ^ ζ) :
    IndexedLineFrostman δ D ζ (fun x : T => (x : Plane)) := by
  classical
  intro u a r hu hr
  have hrp : 0 < r := hδ.trans_le hr
  let U := T.filter (fun y => |inner ℝ y u - a| < r)
  have hl := lower_fiber_count S U f
    (fun y hy => hlower y (Finset.mem_filter.mp hy).1)
  have hsub : S.filter (fun x => f x ∈ U) ⊆
      S.filter (fun x => |inner ℝ x u - a| < r + δ) := by
    intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hfx := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).2).2
    have hi : |inner ℝ x u - inner ℝ (f x) u| ≤ δ := by
      rw [← inner_sub_left]
      calc |inner ℝ (x - f x) u| ≤ ‖x - f x‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ = dist x (f x) := by rw [hu, mul_one, dist_eq_norm]
        _ ≤ δ := hnear x hxS
    refine Finset.mem_filter.mpr ⟨hxS, ?_⟩
    have ht := abs_add_le (inner ℝ x u - inner ℝ (f x) u) (inner ℝ (f x) u - a)
    have heq : (inner ℝ x u - inner ℝ (f x) u) + (inner ℝ (f x) u - a) = inner ℝ x u - a := by ring
    rw [heq] at ht
    linarith
  have hc : ((S.filter (fun x => f x ∈ U)).card : ℝ) ≤
      ((S.filter (fun x => |inner ℝ x u - a| < r + δ)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hFr := hF u a (r + δ) hu (by linarith)
  rw [subtype_filter_card S (fun x => |inner ℝ x u - a| < r + δ), Fintype.card_coe] at hFr
  have hp : (C * (r + δ)) ^ ζ ≤ (C * (2 * r)) ^ ζ := by gcongr; linarith
  have hbound : M * (U.card : ℝ) ≤ (D * r) ^ ζ * (T.card : ℝ) * M := by
    calc M * (U.card : ℝ) ≤ ((S.filter (fun x => f x ∈ U)).card : ℝ) := hl
      _ ≤ (C * (r + δ)) ^ ζ * (S.card : ℝ) := hc.trans hFr
      _ ≤ (C * (2 * r)) ^ ζ * (L * M * (T.card : ℝ)) :=
        mul_le_mul hp hmass (Nat.cast_nonneg _) (by positivity)
      _ = (L * (2 * C) ^ ζ) * r ^ ζ * (T.card : ℝ) * M := by
        rw [show C * (2 * r) = (2 * C) * r by ring, Real.mul_rpow (by positivity) hrp.le]
        ring
      _ ≤ D ^ ζ * r ^ ζ * (T.card : ℝ) * M := by gcongr
      _ = (D * r) ^ ζ * (T.card : ℝ) * M := by rw [Real.mul_rpow hD hrp.le]
  have hcount : (U.card : ℝ) ≤ (D * r) ^ ζ * (T.card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hM).mp
    simpa only [mul_comm M] using hbound
  rw [subtype_filter_card T (fun x => |inner ℝ x u - a| < r), Fintype.card_coe]
  exact hcount

end WangZahlLot.Obl.wz_separated_projection_dichotomy
