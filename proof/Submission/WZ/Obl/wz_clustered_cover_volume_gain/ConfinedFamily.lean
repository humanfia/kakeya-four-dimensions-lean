-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ConfinedFamily.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.ConfinedDichotomy
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RotationRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FiberAssembly

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (TubeEstimate)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (enumerate enumerate_mem sum_enumerate)

/-- Apply the confined packet estimate independently in the frames of all
coarse boxes, keeping one fixed density alternative for the ambient set. -/
theorem confined_family_density_or_refinement {σ ω : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : TubeEstimate σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ C η d₀ : ℝ, 0 < C ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (L N J A : ℕ),
    1 ≤ A → (L : ℝ) ≤ δ ^ (-100 : ℝ) →
    ∀ ρ a c s m D R lam a₀ b₀ : ℝ,
    0 < ρ → ρ ≤ 1 → ρ ≤ a₀ → a₀ ≤ b₀ → 0 < a → a ≤ ρ * c →
    0 < c → c ≤ 1 → 0 < s → s ≤ 1 → a ≤ s * ρ * c → s * ρ * c ≤ A * a →
    1 ≤ m → 0 < D → 1536 * δ ^ η ≤ D / 8 → δ ≤ a / 20000 →
    256 * δ ^ 2 ≤ a * ρ / (800000000 * (min 1 b₀) ^ 2 * s * c) →
    0 < R → (s = 1 ∨ R ≤ (s / 2) * ρ * c) → 0 ≤ lam →
    ∀ (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (Y : Fin L → Set V)
      (γ : Fin L → Fin N) (y w : Fin N → V) (g : Fin N → Fin J)
      (z₀ : Fin J → V) (e₀ : Fin J → V ≃ₗᵢ[ℝ] V) (Z U : Set V),
    (∀ j, MeasurableSet (Y j)) → (∀ j, Y j ⊆ P a (ρ * c) c (z j) (e j)) →
    (∀ j, Y j ⊆ Z) → Z ⊆ U → U ⊆ ball 0 1 →
    (∀ j, Y j ≠ ∅ → O D * volume (P a (ρ * c) c (z j) (e j)) ≤ volume (Y j)) →
    (∀ j, Y j ≠ ∅ → ‖w (γ j)‖ = 1) →
    (∀ j, Y j ≠ ∅ → (e j (w (γ j)) 0) ^ 2 + (e j (w (γ j)) 1) ^ 2 ≤ (10 * ρ) ^ 2) →
    (∀ j, Y j ≠ ∅ → T ρ (y (γ j)) (w (γ j)) ⊆ P a₀ b₀ 8 (z₀ (g (γ j))) (e₀ (g (γ j)))) →
    (∀ p ∈ Z, volume (U ∩ ball p R) ≤ O (lam * R ^ 3)) →
    (∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) →
    confinementDensity a ρ c D s ≤ 46080 * lam ∨
    ∃ W : Fin L → Set V, (∀ j, MeasurableSet (W j) ∧ W j ⊆ Y j) ∧
      (1 / 16 : ℝ≥0∞) * ∑ j, volume (Y j) ≤ ∑ j, volume (W j) ∧
      ∀ k p, fiberBodyCount (g ∘ γ) W k p ≤ C * δ ^ (-ε) * (D / 8)⁻¹ *
        ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * m) ^ (1 + σ / 2) *
        (a * ρ / (800000000 * (min 1 b₀) ^ 2 * s * c)) ^ (-(ω + σ) / 2) := by
  classical
  intro ε hε
  obtain ⟨C, η, d₀, hC, hη, hd₀, hd₀small, H⟩ :=
    confined_grain_density_or_refinement hσ hσhalf hω hE ε hε
  refine ⟨C, η, d₀, hC, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd L N J A hA hL ρ a c s m D R lam a₀ b₀ hρ hρ1 hρa₀ ha₀b₀ ha hac
    hc hc1 hs hs1 has hAs hm hD hDη hδa hscale hR hRs hlam z e Y γ y w g z₀ e₀ Z U
    hYm hYU hYZ hZU hUball hdense hw halign hcover hupper hlocal
  by_cases hden : confinementDensity a ρ c D s ≤ 46080 * lam
  · exact Or.inl hden
  right
  apply combine_fiber_refinements (g ∘ γ) Y
  intro k
  let I : Finset (Fin L) := Finset.univ.filter fun j => g (γ j) = k ∧ Y j ≠ ∅
  let ι := enumerate I
  have hI (i : Fin I.card) : g (γ (ι i)) = k ∧ Y (ι i) ≠ ∅ :=
    (Finset.mem_filter.mp (enumerate_mem I i)).2
  have hcard : (I.card : ℝ) ≤ δ ^ (-100 : ℝ) := by
    have hh : I.card ≤ L := by simpa only [Fintype.card_fin] using Finset.card_le_univ I
    exact (Nat.cast_le.mpr hh).trans hL
  let Rk := e₀ k
  let θ : ℝ := min 1 b₀
  have hρθ : ρ ≤ θ := le_min hρ1 (hρa₀.trans ha₀b₀)
  have hθ : 0 < θ := hρ.trans_le hρθ
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have haxes (i : Fin I.card) :
      ‖dualLinear θ (boxAxis (rotatedFrame Rk (e (ι i))) 0)‖ ≤ 25 * θ ∧
      ‖dualLinear θ (boxAxis (rotatedFrame Rk (e (ι i))) 1)‖ ≤ 25 * θ ∧
      ‖coarseLinear θ (boxAxis (rotatedFrame Rk (e (ι i))) 2)‖ ≤ 43 := by
    have hcv : T ρ (y (γ (ι i))) (w (γ (ι i))) ⊆ P a₀ b₀ 8 (z₀ k) Rk := by
      simpa only [(hI i).1, Rk] using hcover (ι i) (hI i).2
    have hcoord := parent_direction_coordinates Rk hρ ha₀b₀ (hw (ι i) (hI i).2) hcv
    apply frozen_coarse_axis_bounds hθ hθ1 hρ.le hρθ _ (Rk (w (γ (ι i))))
    · simpa only [Rk.norm_map] using hw (ι i) (hI i).2
    · exact hcoord.1
    · exact hcoord.2
    · simpa only [rotatedFrame_apply] using halign (ι i) (hI i).2
  have hdense' (i : Fin I.card) :
      O D * volume (P a (ρ * c) c (Rk (z (ι i))) (rotatedFrame Rk (e (ι i)))) ≤
        volume (Rk '' Y (ι i)) := by
    rw [← rotated_prism, rotation_volume, rotation_volume]
    exact hdense (ι i) (hI i).2
  have hupper' : ∀ p ∈ Rk '' Z,
      volume (Rk '' U ∩ ball p R) ≤ O (lam * R ^ 3) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [rotation_ball_inter]
    exact hupper p hp
  have hYprism (i : Fin I.card) : Rk '' Y (ι i) ⊆
      P a (ρ * c) c (Rk (z (ι i))) (rotatedFrame Rk (e (ι i))) := by
    rw [← rotated_prism]
    exact image_mono (hYU (ι i))
  rcases H δ hδ hδd I.card L A ι hA (enumerate I).injective hcard θ ρ a c s m D R lam
    hθ hθ1 hρ hρθ ha hac hc hc1 hs hs1 has hAs hm hD hDη hδa hscale hR hRs hlam
    (Rk ∘ z) (rotatedFrame Rk ∘ e) (fun i => Rk '' Y (ι i)) (Rk '' Z) (Rk '' U)
    (fun i => (haxes i).1) (fun i => (haxes i).2.1) (fun i => (haxes i).2.2)
    (fun i => rotation_measurable Rk (hYm (ι i))) hYprism
    (fun i => image_mono (hYZ (ι i))) (image_mono hZU) (rotation_subset_unit_ball Rk hUball)
    hdense' hupper' (rotated_local_grain_count z e Rk hlocal) with hh | hh
  · exact (hden hh).elim
  obtain ⟨W, hW, hmass, hcount⟩ := hh
  obtain ⟨W', hW', hmass', hcount'⟩ := rotation_refinement Rk (Y ∘ ι) W hW hmass hcount
  obtain ⟨Q, hQ, hQmass, hQcount⟩ := extend_subfamily_mass_count I Y W' hW' hmass' hcount'
  refine ⟨Q, fun i => ⟨(hQ i).1, (hQ i).2.1, ?_⟩, ?_, hQcount⟩
  · intro hi
    apply (hQ i).2.2
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hh => hi hh.1
  · convert hQmass using 2
    symm
    apply Finset.sum_subset
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩
    · intro i hi hni
      have he : Y i = ∅ := by
        by_contra hne
        exact hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2, hne⟩)
      rw [he, measure_empty]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
