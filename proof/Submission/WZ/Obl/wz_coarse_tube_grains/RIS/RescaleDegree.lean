-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaleDegree.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleConflict

/-!
# Bounded conflict degree

In an essentially distinct fibre, the tubes whose rescaled tubes conflict with a given one
(in either order) are near a common axis at scale `δ`, so there are at most `M` of them for an
absolute constant `M`. This is what makes the extraction loss independent of `m`, `l`, `ρ`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

noncomputable section

/-- Reversing the orientation of a tube does not change it; the version for the midpoint. -/
theorem tube_eq_of_midpoint_orient (δ : ℝ) (x v : Space) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Tube δ ((x + (1 / 2 : ℝ) • v) - (1 / 2 : ℝ) • (σ • v)) (σ • v) = Tube δ x v := by
  rcases hσ with rfl | rfl
  · congr 1 <;> module
  · rw [tube_reverse δ x v]
    congr 1 <;> module

/-- A finset of essentially distinct tubes whose directions and midpoints are near a common
axis has bounded cardinality. -/
theorem near_axis_finset_card_bound (A B L : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∀ {δ : ℝ}, 0 < δ → ∀ {n : ℕ} (x v : Fin n → Space) (x₀ v₀ : Space)
      (J : Finset (Fin n)), (∀ i, ‖v i‖ = 1) →
      (∀ j ∈ J, pd (v j) v₀ ≤ A * δ ∧
        ∃ s : ℝ, |s| ≤ L ∧ ‖(x j + (1 / 2 : ℝ) • v j) - x₀ - s • v₀‖ ≤ B * δ) →
      (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
      J.card ≤ M := by
  classical
  obtain ⟨M, hM⟩ := near_axis_family_card_bound A (B + A) (L + 1) hA (by positivity)
    (by positivity)
  refine ⟨M, ?_⟩
  intro δ hδ n x v x₀ v₀ J hv hnear hdist
  set k := J.card with hk
  let φ : Fin k ≃ J := J.equivFin.symm
  let jj : Fin k → Fin n := fun a => (φ a : Fin n)
  have hjj_mem : ∀ a, jj a ∈ J := fun a => (φ a).2
  have hjj_inj : Function.Injective jj := fun a b h => φ.injective (Subtype.ext h)
  let σ : Fin k → ℝ := fun a => if ‖v (jj a) - v₀‖ ≤ A * δ then 1 else -1
  have hσ : ∀ a, σ a = 1 ∨ σ a = -1 := by
    intro a
    by_cases h : ‖v (jj a) - v₀‖ ≤ A * δ
    · left; simp [σ, h]
    · right; simp [σ, h]
  let vt : Fin k → Space := fun a => σ a • v (jj a)
  let xt : Fin k → Space := fun a => (x (jj a) + (1 / 2 : ℝ) • v (jj a)) - (1 / 2 : ℝ) • vt a
  have htube : ∀ a, Tube δ (xt a) (vt a) = Tube δ (x (jj a)) (v (jj a)) :=
    fun a => tube_eq_of_midpoint_orient δ (x (jj a)) (v (jj a)) (hσ a)
  have hvt : ∀ a, ‖vt a‖ = 1 := by
    intro a
    rcases hσ a with h | h <;> simp [vt, h, hv (jj a), norm_neg]
  have hdir : ∀ a, ‖vt a - v₀‖ ≤ A * δ := by
    intro a
    have hpd := (hnear (jj a) (hjj_mem a)).1
    by_cases h : ‖v (jj a) - v₀‖ ≤ A * δ
    · simp [vt, σ, h]
    · have hadd : ‖v (jj a) + v₀‖ ≤ A * δ := by
        rcases min_le_iff.mp hpd with h' | h'
        · exact absurd h' h
        · exact h'
      have hvt' : vt a = -v (jj a) := by simp [vt, σ, h]
      rw [hvt', show -v (jj a) - v₀ = -(v (jj a) + v₀) by abel, norm_neg]
      exact hadd
  let s : Fin k → ℝ := fun a => Classical.choose (hnear (jj a) (hjj_mem a)).2
  have hs : ∀ a, |s a| ≤ L ∧
      ‖(x (jj a) + (1 / 2 : ℝ) • v (jj a)) - x₀ - s a • v₀‖ ≤ B * δ :=
    fun a => Classical.choose_spec (hnear (jj a) (hjj_mem a)).2
  let tt : Fin k → ℝ := fun a => s a - 1 / 2
  have htt : ∀ a, |tt a| ≤ L + 1 := by
    intro a
    have h1 := (hs a).1
    have h2 : |tt a| ≤ |s a| + |(1 / 2 : ℝ)| := by
      simpa [tt] using abs_sub (s a) (1 / 2 : ℝ)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h2
    linarith
  have hpos : ∀ a, ‖xt a - x₀ - tt a • v₀‖ ≤ (B + A) * δ := by
    intro a
    have heq : xt a - x₀ - tt a • v₀ =
        ((x (jj a) + (1 / 2 : ℝ) • v (jj a)) - x₀ - s a • v₀) -
          (1 / 2 : ℝ) • (vt a - v₀) := by
      simp only [xt, tt]; module
    rw [heq]
    have h1 := norm_sub_le ((x (jj a) + (1 / 2 : ℝ) • v (jj a)) - x₀ - s a • v₀)
      ((1 / 2 : ℝ) • (vt a - v₀))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1
    have h2 := (hs a).2
    have h3 := hdir a
    nlinarith
  have hsep : ∀ a b, a ≠ b → volume (Tube δ (xt a) (vt a) ∩ Tube δ (xt b) (vt b)) ≤
      (1 / 2 : ENNReal) * volume (Tube δ (xt a) (vt a)) := by
    intro a b hab
    rw [htube, htube]
    exact hdist _ _ (hjj_inj.ne hab)
  exact hM hδ xt vt tt x₀ v₀ hvt htt hpos hdir hsep

/-- The conflict relation between rescaled tubes of a fibre, symmetrized. -/
def RescaledConflict (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (δ : ℝ) {n : ℕ} (x v : Fin n → Space) (i j : Fin n) : Prop :=
  ¬ volume (rescaledTube e y w hκ hρ δ (x i) (v i) ∩ rescaledTube e y w hκ hρ δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (rescaledTube e y w hκ hρ δ (x i) (v i)) ∨
    ¬ volume (rescaledTube e y w hκ hρ δ (x j) (v j) ∩ rescaledTube e y w hκ hρ δ (x i) (v i)) ≤
      (1 / 2 : ENNReal) * volume (rescaledTube e y w hκ hρ δ (x j) (v j))

/-- Angular confinement and bounded midpoint diameter give a bounded conflict degree. -/
theorem rescaled_conflict_degree_bound_of_bounds (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∀ (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}, e w = axis →
      ∀ {κ ρ δ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ), κ * 5 ≤ 1 → ρ ≤ 1 → 0 < δ →
      ∀ {n : ℕ} (x v : Fin n → Space), (∀ i, ‖v i‖ = 1) →
      (∀ i, pd (v i) w < 4 * ρ) →
      (∀ i j, ‖(x j + (1 / 2 : ℝ) • v j) - (x i + (1 / 2 : ℝ) • v i)‖ ≤ L) →
      (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
      ∀ i (J : Finset (Fin n)), (∀ j ∈ J, RescaledConflict e y w hκ hρ δ x v i j) →
        J.card ≤ M := by
  classical
  obtain ⟨M, hM⟩ := near_axis_finset_card_bound 5000000 (500015 + L * 5000000) L
    (by norm_num) (by positivity) hL
  refine ⟨M, ?_⟩
  intro e y w hew κ ρ δ hκ hρ hκ5 hρ1 hδ n x v hv hvw hmid hdist i J hJ
  have hκ1 : κ ≤ 1 := by linarith
  apply hM hδ x v (x i + (1 / 2 : ℝ) • v i) (v i) J hv _ hdist
  intro j hj
  rcases hJ j hj with hc | hc
  · obtain ⟨hpd, s, hs, hpos⟩ := near_axis_of_rescaled_conflict_of_bounds e hew hκ hκ5 hρ hρ1 hδ
      (hv i) (hv j) (hvw i) (hvw j) (hmid i j) hc
    refine ⟨?_, s, hs, ?_⟩
    · rw [pd_symm]
      calc pd (v i) (v j) ≤ 5000000 * κ * δ := hpd
        _ ≤ 5000000 * δ := by nlinarith
    · calc _ ≤ 500015 * δ := hpos
        _ ≤ (500015 + L * 5000000) * δ := by nlinarith
  · obtain ⟨hpd, s, hs, hpos⟩ := near_axis_of_rescaled_conflict_of_bounds e hew hκ hκ5 hρ hρ1 hδ
      (hv j) (hv i) (hvw j) (hvw i) (hmid j i) hc
    have hpd' : pd (v j) (v i) ≤ 5000000 * δ := by
      calc pd (v j) (v i) ≤ 5000000 * κ * δ := hpd
        _ ≤ 5000000 * δ := by nlinarith
    refine ⟨hpd', ?_⟩
    -- orient `v j` along `v i`
    obtain ⟨τ, hτ, hτv⟩ : ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧ ‖v j - τ • v i‖ ≤ 5000000 * δ := by
      rcases min_le_iff.mp hpd' with h | h
      · exact ⟨1, Or.inl rfl, by simpa using h⟩
      · exact ⟨-1, Or.inr rfl, by simpa using h⟩
    refine ⟨-(s * τ), ?_, ?_⟩
    · rcases hτ with rfl | rfl <;> simpa using hs
    · have heq : (x j + (1 / 2 : ℝ) • v j) - (x i + (1 / 2 : ℝ) • v i) - (-(s * τ)) • v i =
          -((x i + (1 / 2 : ℝ) • v i) - (x j + (1 / 2 : ℝ) • v j) - s • v j) -
            s • (v j - τ • v i) := by module
      rw [heq]
      have h1 := norm_sub_le (-((x i + (1 / 2 : ℝ) • v i) - (x j + (1 / 2 : ℝ) • v j) - s • v j))
        (s • (v j - τ • v i))
      rw [norm_neg, norm_smul, Real.norm_eq_abs] at h1
      have h2 : |s| * ‖v j - τ • v i‖ ≤ L * (5000000 * δ) :=
        mul_le_mul hs hτv (norm_nonneg _) hL
      linarith

/-- The conflict degree for unit carriers is bounded by an absolute constant. -/
theorem rescaled_conflict_degree_bound :
    ∃ M : ℕ, ∀ (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}, e w = axis → ‖w‖ = 1 →
      ∀ {κ ρ δ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ), κ * 5 ≤ 1 → ρ ≤ 1 → 0 < δ →
      ∀ {n : ℕ} (x v : Fin n → Space), (∀ i, ‖v i‖ = 1) →
      (∀ i, Tube δ (x i) (v i) ⊆ Tube ρ y w) →
      (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube δ (x i) (v i))) →
      ∀ i (J : Finset (Fin n)), (∀ j ∈ J, RescaledConflict e y w hκ hρ δ x v i j) →
        J.card ≤ M := by
  obtain ⟨M, hM⟩ := rescaled_conflict_degree_bound_of_bounds 3 (by norm_num)
  refine ⟨M, ?_⟩
  intro e y w hew hw κ ρ δ hκ hρ hκ5 hρ1 hδ n x v hv hsub hdist i J hJ
  exact hM e hew hκ hρ hκ5 hρ1 hδ x v hv
    (fun j => pd_lt_of_tube_subset hδ (hv j) hw (hsub j))
    (fun j k => (midpoint_dist_lt hδ hρ1 hw (hsub j) (hsub k)).le) hdist i J hJ

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
