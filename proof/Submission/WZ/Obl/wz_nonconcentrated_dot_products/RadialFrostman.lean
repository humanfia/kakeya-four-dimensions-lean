-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.RadialFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.RadialGeometry

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

attribute [local instance] Classical.propDecidable

theorem radialDirection_indexedFrostman {δ K c : ℝ} (E G : Finset Plane) (b : Plane)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hc : 0 < c)
    (hne : ∀ x ∈ E, b ≠ x) (hfar : ∀ x ∈ E, ‖b - x‖ ≤ 8)
    (hret : c * (G.card : ℝ) ≤ (E.card : ℝ))
    (hthin : ∀ (u : Plane) (r : ℝ), ‖u‖ = 1 → δ ≤ r →
      ((E.filter (fun x => |inner ℝ (x - b) u| < r)).card : ℝ) ≤ K * r * (G.card : ℝ)) :
    IndexedFrostman δ (17 * K / c) (fun x : E => radialDirection b x) := by
  classical
  intro z r hδr
  have hr : 0 < r := hδ.trans_le hδr
  let B : Finset E := Finset.univ.filter (fun x => dist (radialDirection b x) z ≤ r)
  by_cases hB : B.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hB
    let u : Plane := radialDirection b x₀
    have hu : ‖u‖ = 1 := radialDirection_norm (hne x₀ x₀.property)
    have hsub : B.image Subtype.val ⊆ E.filter (fun x => |inner ℝ (x - b) (perp u)| < 17 * r) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hdist : dist (radialDirection b y) u ≤ 2 * r := by
        have ht := dist_triangle (radialDirection b y) z u
        have hy' := (Finset.mem_filter.mp hy).2
        have hx₀' : dist u z ≤ r := (Finset.mem_filter.mp hx₀).2
        rw [dist_comm z u] at ht
        linarith
      have hb := abs_inner_perp_le_radial_distance (hne y y.property) hu
      have hm : ‖b - (y : Plane)‖ * dist (radialDirection b y) u ≤ 8 * (2 * r) :=
        mul_le_mul (hfar y y.property) hdist dist_nonneg (by norm_num)
      exact Finset.mem_filter.mpr ⟨y.property, by linarith⟩
    have hcard : (B.card : ℝ) ≤
        ((E.filter (fun x => |inner ℝ (x - b) (perp u)| < 17 * r)).card : ℝ) := by
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
      exact_mod_cast hh
    have hcount := hthin (perp u) (17 * r) ((perp_norm u).trans hu) (by linarith)
    calc (B.card : ℝ) ≤ K * (17 * r) * (G.card : ℝ) := hcard.trans hcount
      _ = (17 * K / c) * r * (c * (G.card : ℝ)) := by field_simp
      _ ≤ (17 * K / c) * r * (E.card : ℝ) :=
        mul_le_mul_of_nonneg_left hret (by positivity)
      _ = (17 * K / c) * r * (Fintype.card E : ℝ) := by simp
  · have hB' : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (B.card : ℝ) ≤ _
    rw [hB', Finset.card_empty, Nat.cast_zero]
    positivity

theorem ClosedFiniteFrostman.mono_constant {δ C D : ℝ} {F : Finset Plane}
    (hF : ClosedFiniteFrostman δ C F) (hδ : 0 ≤ δ) (hCD : C ≤ D) :
    ClosedFiniteFrostman δ D F := by
  intro x r hr
  exact (hF x r hr).trans (by gcongr; exact hδ.trans hr)

theorem ClosedFiniteFrostman.mono_scale {δ ρ C : ℝ} {F : Finset Plane}
    (hF : ClosedFiniteFrostman δ C F) (hδρ : δ ≤ ρ) :
    ClosedFiniteFrostman ρ C F := fun x r hr => hF x r (hδρ.trans hr)

theorem IndexedFrostman.mono_scale {I : Type*} [Fintype I] {f : I → Plane}
    {δ ρ C : ℝ} (hf : IndexedFrostman δ C f) (hδρ : δ ≤ ρ) :
    IndexedFrostman ρ C f := fun x r hr => hf x r (hδρ.trans hr)

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
