-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.Extensions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric

/-- Coordinatewise real extension gives a global unit-Lipschitz map from a map whose
Lipschitz constant on its original domain is at most one third. This avoids any appeal
to an unformalized isometric extension theorem for Hilbert-valued functions. -/
theorem extend_plane_map {E : Set Space} {P : Space → Space}
    (hP : LipschitzOnWith (1 / 3) P E) :
    ∃ Q : Space → Space, LipschitzWith 1 Q ∧ EqOn P Q E := by
  have hcoord : ∀ i : Fin 3, LipschitzOnWith (1 / 3) (fun p => P p i) E := by
    intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    apply le_trans _ (hP.dist_le_mul p hp q hq)
    simpa only [dist_eq_norm, PiLp.sub_apply] using PiLp.norm_apply_le (P p - P q) i
  choose g hg hgeq using fun i => (hcoord i).extend_real
  let Q : Space → Space := fun p => WithLp.toLp 2 (fun i => g i p)
  refine ⟨Q, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [NNReal.coe_one, one_mul]
    rw [dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) dist_nonneg).mp
    have hcoord_sq : ∀ i : Fin 3, (g i p - g i q) ^ 2 ≤ (dist p q / 3) ^ 2 := by
      intro i
      have h := (hg i).dist_le_mul p q
      norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, Real.dist_eq] at h
      have h' : |g i p - g i q| ≤ dist p q / 3 := by linarith
      nlinarith [sq_abs (g i p - g i q),
        (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ dist p q / 3)).mpr h']
    calc
      ‖Q p - Q q‖ ^ 2 = ∑ i : Fin 3, (g i p - g i q) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        rfl
      _ ≤ ∑ _ : Fin 3, (dist p q / 3) ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord_sq i
      _ ≤ dist p q ^ 2 := by simp; nlinarith [sq_nonneg (dist p q)]
  · intro p hp
    ext i
    exact hgeq i hp

theorem third_coord_mem_interval {E : Set Space} (hE : E ⊆ ball (0 : Space) 1)
    {p : Space} (hp : p ∈ E) : p 2 ∈ Icc (-1 : ℝ) 1 := by
  have hp1 : ‖p‖ < 1 := by simpa using hE hp
  have hc : |p 2| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 2
  exact abs_le.mp (hc.trans hp1.le)

theorem projectedSlice_congr_on_interval {E : Set Space} {f g : ℝ → ℝ}
    (hE : E ⊆ ball (0 : Space) 1) (hfg : EqOn f g (Icc (-1 : ℝ) 1)) (z : ℝ) :
    projectedSlice f E z = projectedSlice g E z := by
  ext u
  constructor
  · rintro ⟨p, hp, he⟩
    refine ⟨p, hp, ?_⟩
    dsimp only at he ⊢
    rwa [← hfg (third_coord_mem_interval hE hp)]
  · rintro ⟨p, hp, he⟩
    refine ⟨p, hp, ?_⟩
    dsimp only at he ⊢
    rwa [hfg (third_coord_mem_interval hE hp)]

/-- A slope defined with a Lipschitz bound only on the relevant vertical interval
has a global extension giving exactly the same twisted slices. -/
theorem extend_slope {E : Set Space} {f : ℝ → ℝ} (hE : E ⊆ ball (0 : Space) 1)
    (hf : LipschitzOnWith 1 f (Icc (-1 : ℝ) 1)) :
    ∃ g : ℝ → ℝ, LipschitzWith 1 g ∧ ∀ z, projectedSlice f E z = projectedSlice g E z := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  exact ⟨g, hg, projectedSlice_congr_on_interval hE heq⟩

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
