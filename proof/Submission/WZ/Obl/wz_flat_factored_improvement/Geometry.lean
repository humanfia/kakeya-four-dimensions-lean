-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Types
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry
import Submission.WZ.Obl.wz_frostman_rigid_copies_volume

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal

abbrev StandardPrism (a b : ℝ) : Set Space :=
  {p | |p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 2}

theorem standardPrism_convex (a b : ℝ) : Convex ℝ (StandardPrism a b) := by
  have hset : StandardPrism a b =
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) ⁻¹' Icc ![-a, -b, -2] ![a, b, 2] := by
    ext p
    change (|p 0| ≤ a ∧ |p 1| ≤ b ∧ |p 2| ≤ 2) ↔
      (∀ i, ![-a, -b, -2] i ≤ p i) ∧ (∀ i, p i ≤ ![a, b, 2] i)
    simp [Fin.forall_fin_succ, abs_le]
    tauto
  rw [hset]
  exact (convex_Icc _ _).linear_preimage (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap

theorem standardPrism_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    volume (StandardPrism a b) = ENNReal.ofReal (16 * a * b) := by
  let B := EuclideanSpace.basisFun (Fin 3) ℝ
  have he : StandardPrism a b = {p : Space | ∀ i,
      ![-a, -b, -2] i ≤ B.repr (p - 0) i ∧ B.repr (p - 0) i ≤ ![a, b, 2] i} := by
    ext p
    simp [B, StandardPrism, Fin.forall_fin_succ, abs_le]
  rw [he, WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.coordinate_box_volume]
  rw [Fin.prod_univ_three]
  change ENNReal.ofReal (a - -a) * ENNReal.ofReal (b - -b) *
    ENNReal.ofReal (2 - (-2 : ℝ)) = ENNReal.ofReal (16 * a * b)
  simp only [sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem prism_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (e : AffineIsometryEquiv ℝ Space Space) :
    volume (e '' StandardPrism a b) = ENNReal.ofReal (16 * a * b) := by
  rw [WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image]
  exact standardPrism_volume ha hb

/-- The narrow coordinate determines a slab, uniformly under rigid motions. -/
theorem prism_subset_slab (a b : ℝ) (e : AffineIsometryEquiv ℝ Space Space) :
    ∃ u : Space, ‖u‖ = 1 ∧
      e '' StandardPrism a b ⊆ {p | |inner ℝ u p - inner ℝ u (e 0)| ≤ a} := by
  let u := e.linearIsometryEquiv (EuclideanSpace.basisFun (Fin 3) ℝ 0)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [LinearIsometryEquiv.norm_map, OrthonormalBasis.norm_eq_one]
  refine ⟨u, hu, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have he : e p = e.linearIsometryEquiv p + e 0 := by
    simpa using e.map_vadd (0 : Space) p
  change |inner ℝ u (e p) - inner ℝ u (e 0)| ≤ a
  rw [he, inner_add_right, add_sub_cancel_right]
  dsimp [u]
  rw [LinearIsometryEquiv.inner_map_map, EuclideanSpace.basisFun_inner]
  exact hp.1

/-- The original slab bound controls all tubes in any one flat prism. -/
theorem prism_tube_count_le {δ l a b : ℝ} {n : ℕ} {x v : Fin n → Space}
    (ha : 0 < a) (hl : 0 ≤ l) (e : AffineIsometryEquiv ℝ Space Space)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball (0 : Space) 1)
    (hslab : SlabCount δ l n x v) :
    (Set.ncard {i | Tube δ (x i) (v i) ⊆ e '' StandardPrism a b} : ℝ) ≤
      8 * a * l * n := by
  obtain ⟨u, hu, hsub⟩ := prism_subset_slab a b e
  have hcount : Set.ncard {i | Tube δ (x i) (v i) ⊆ e '' StandardPrism a b} ≤
      Set.ncard {i | Tube δ (x i) (v i) ⊆
        ball (0 : Space) 1 ∩ {p | |inner ℝ u p - inner ℝ u (e 0)| ≤ a}} := by
    apply Set.ncard_le_ncard _ (Set.toFinite _)
    intro i hi p hp
    exact ⟨hball i hp, hsub (hi hp)⟩
  have hvol := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.slab_volume_le hu
    (inner ℝ u (e 0)) a ha.le
  have h : ENNReal.ofReal
      (Set.ncard {i | Tube δ (x i) (v i) ⊆ e '' StandardPrism a b} : ℝ) ≤
      ENNReal.ofReal (8 * a * l * n) := by
    calc
      _ ≤ ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆
          ball (0 : Space) 1 ∩ {p | |inner ℝ u p - inner ℝ u (e 0)| ≤ a}} : ℝ) :=
        ENNReal.ofReal_le_ofReal (by exact_mod_cast hcount)
      _ ≤ ENNReal.ofReal (l * n) *
          volume (ball (0 : Space) 1 ∩ {p | |inner ℝ u p - inner ℝ u (e 0)| ≤ a}) :=
        hslab u (inner ℝ u (e 0)) a hu ha
      _ ≤ ENNReal.ofReal (l * n) * ENNReal.ofReal (8 * a) := mul_le_mul' le_rfl hvol
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end WangZahlLot.Obl.wz_flat_factored_improvement
