-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WindowIncidenceAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WindowIncidenceAssembly.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WindowBlockRows
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.RowFamilies
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.UniformIncidenceAssembly

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (extendSets enumerate enumerate_mem enumerate_surj extendSets_enumerate extendSets_outside)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

noncomputable section

/-- The actual windows of every retained high carrier assemble into the
accepted per-incidence stage-zero predicate. This includes the global
mass estimate and the exact lifting from local block indices. -/
theorem incidence_prisms_of_window_blocks_uniform
    {ω ζ ξ e t τ₂ widthJump fillExp h' : ℝ}
    (hβ : 0 ≤ ω * ζ / 100) (hξ : 0 ≤ ξ)
    (hr : 0 ≤ 2 * e + 3 * t + τ₂ + ξ / 4 + ξ / 40)
    (hmassgap : ξ / 4 + (2 * e + 3 * t + τ₂ + ξ / 4 + ξ / 40) < h')
    (hdengap : fillExp < h') :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ,
      ∀ hδ : 0 < δ, δ ≤ d₀ →
      ∀ {σ b ρ c β τ Cnet ν loss q₀ jump : ℝ} {p n d : ℕ}
        {x v : Fin n → V} {Y : Fin n → Set V}
        (D : ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y)
        (F : AngularBlockFamily D β τ)
        (H : ∀ R : F.blocks, WindowHighNetBlock (F.angular R) hδ σ Cnet e t ν loss
          (ω * ζ / 100) q₀ jump τ₂ widthJump fillExp d),
      τ + 21 * ξ / 40 ≤ t → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ I) →
      ∃ ρ', δ ^ (-widthJump) * ρ ≤ ρ' ∧
        WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ h' ρ' c n x v Y 0 := by
  classical
  let massD := 17 * firstFillingMassConstant ^ 2 / 48
  have hmassD : 0 < massD := by norm_num [massD, firstFillingMassConstant]
  obtain ⟨d₀, hd₀, hd₀1, HA⟩ := uniform_incidence_prisms_of_occupied_rows
    (h₀ := ξ / 4) (h' := h') (r := 2 * e + 3 * t + τ₂ + ξ / 4 + ξ / 40)
    (dens := fillExp) (B := 8) (C₀ := 2) (K := 21474836480) (D := massD)
    hβ (by norm_num) (by norm_num) (by norm_num) hmassD hr hmassgap hdengap
  refine ⟨d₀, hd₀, hd₀1, ?_⟩
  intro δ hδ hδ0 σ b ρ c β τ Cnet ν loss q₀ jump p n d x v Y D F H hmass hv hTI
  have hδ1 := hδ0.trans hd₀1
  obtain ⟨ha, hρ, hρ1, hc, hc1⟩ := D.dimensions hδ
  have hδρ : δ ≤ ρ := D.grains.1.trans
    (D.grains.2.1.trans (mul_le_of_le_one_right hρ.le hc1))
  let κ := Σ R : F.blocks, (H R).RowLabels
  let W : κ → Fin D.L → Set V := fun k => extendSets k.1.val ((H k.1).row k.2)
  let z' : κ → V := fun k => ((H k.1).rows k.2.1).center k.2.2
  let e' : κ → V ≃ₗᵢ[ℝ] V := fun k => ((H k.1).rows k.2.1).frame k.2.2
  let aRow : κ → ℝ := fun k => ((H k.1).rows k.2.1).short k.2.2
  let bRow : κ → ℝ := fun k => ((H k.1).rows k.2.1).middle k.2.2
  let θ : κ → ℝ := fun k => ((H k.1).packet k.2.1).scale
  let rot : κ → V ≃ₗᵢ[ℝ] V := fun k => ((H k.1).box k.2.1).frame
  let dirs : κ → Fin D.L → V := fun k j =>
    unit ((((H k.1).box k.2.1).map hδ).linear (boxAxis (D.e j) 2))
  have hFdisj : Pairwise fun R R' : F.blocks => Disjoint R.val R'.val :=
    fun R R' hne => F.disjoint R.property R'.property (Subtype.coe_injective.ne hne)
  obtain ⟨hW, hdisj, hsum⟩ := extend_disjoint_block_rows
    (fun R : F.blocks => R.val) (fun R => (H R).row) D.Hg hFdisj
    (fun R => (H R).row_measurable) (fun R => (H R).row_subset) (fun R => (H R).row_disjoint)
  have hunion (k : κ) : (⋃ j, W k j) = ⋃ i, (H k.1).row k.2 i :=
    iUnion_extendSets_univ _ _
  have hocc (k : κ) (hk : (⋃ j, W k j).Nonempty) :
      (⋃ i, ((H k.1).rows k.2.1).shade k.2.2 i).Nonempty := by
    rw [hunion] at hk
    exact hk
  have hmassW : O (δ ^ (2 * e + 3 * t + τ₂ + ξ / 4 + ξ / 40) / massD) *
      ∑ j, μ (D.Hg j) ≤ ∑ k : κ, ∑ j, μ (W k j) := by
    calc
      _ = O (δ ^ τ₂ / 68) *
          (O (192 / firstFillingMassConstant ^ 2 * δ ^ (2 * e + 3 * t + ξ / 4 + ξ / 40)) *
            ∑ j, μ (D.Hg j)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [show 2 * e + 3 * t + τ₂ + ξ / 4 + ξ / 40 =
          τ₂ + (2 * e + 3 * t + ξ / 4 + ξ / 40) by ring, Real.rpow_add hδ]
        dsimp only [massD]
        ring
      _ ≤ O (δ ^ τ₂ / 68) *
          (∑ R : F.blocks, ∑ l ∈ (H R).high.nets.highLabels,
            ∑ j, ∑ i, μ ((H R).high.nets.physicalPiece l j i)) :=
        mul_le_mul' le_rfl (F.physical_carrier_mass (fun R => (H R).high) hδ hδ1 hmass)
      _ = ∑ R : F.blocks, O (δ ^ τ₂ / 68) *
          (∑ l ∈ (H R).high.nets.highLabels, ∑ j, ∑ i, μ ((H R).high.nets.physicalPiece l j i)) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ R : F.blocks, ∑ k : (H R).RowLabels, ∑ i, μ ((H R).row k i) :=
        Finset.sum_le_sum fun R _ => (H R).row_mass
      _ = _ := hsum.symm
  obtain ⟨j₀, hj₀⟩ := D.selected_nonempty
  have hjpos : 0 < μ (D.Hg j₀) :=
    ENNReal.toReal_pos_iff.mp (D.selected_mass_pos hδ j₀ hj₀) |>.1
  have hHgpos : 0 < ∑ j, μ (D.Hg j) := hjpos.trans_le
    (Finset.single_le_sum (f := fun j => μ (D.Hg j)) (fun _ _ => zero_le) (Finset.mem_univ j₀))
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hjpos.ne'
  have hmult := D.grains.2.2.2.2.2.2.2.2.1 (D.γ j₀) p₀
    ((D.grains.2.2.2.2.2.2.1 (D.γ j₀)).subset ⟨j₀, rfl, hp₀⟩)
  have hm : 0 ≤ D.m := by
    have hn : 0 ≤ q n {i | i ∈ D.S ∧ D.f i = D.γ j₀ ∧ p₀ ∈ D.Z i} := Nat.cast_nonneg _
    linarith only [hn, hmult.2]
  have hWpos : 0 < ∑ k : κ, ∑ j, μ (W k j) :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hHgpos.ne').trans_le hmassW
  apply HA W z' e' aRow bRow dirs rot θ hδ hδ0 (by positivity) le_rfl hδρ hm
    hv hTI D.cover D.broad D.grains
  · intro k hk
    have hh := ((H k.1).rows k.2.1).dimensions k.2.2 (hocc k hk)
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  · intro k hk
    exact ((H k.1).rows k.2.1).dimensions k.2.2 (hocc k hk) |>.2.2.2.1
  · exact fun k j => (hW k j).1
  · exact fun k j => (hW k j).2
  · exact hdisj
  · intro k j
    by_cases hj : j ∈ k.1.val
    · obtain ⟨i, rfl⟩ := enumerate_surj k.1.val hj
      change extendSets _ _ (enumerate _ i) ⊆ _
      rw [extendSets_enumerate]
      exact ((H k.1).rows k.2.1).contained k.2.2 i
    · change extendSets _ _ j ⊆ _
      rw [extendSets_outside _ _ hj]
      exact empty_subset _
  · exact hmassW
  · exact hWpos
  · intro k hk
    rw [hunion]
    exact ((H k.1).rows k.2.1).dense k.2.2 (hocc k hk)
  · intro i hi k j hf hne
    by_cases hj : j ∈ k.1.val
    · obtain ⟨i', rfl⟩ := enumerate_surj k.1.val hj
      change (D.Z i ∩ extendSets _ _ (enumerate _ i')).Nonempty at hne
      rw [extendSets_enumerate] at hne
      exact ((H k.1).rows k.2.1).crosses i hi k.2.2 i' hf hne
    · change (D.Z i ∩ extendSets _ _ j).Nonempty at hne
      rw [extendSets_outside _ _ hj, inter_empty] at hne
      exact False.elim (not_nonempty_empty hne)
  · intro k _
    exact hδ.trans_le ((H k.1).packet k.2.1).lower
  · intro k j hne
    by_cases hj : j ∈ k.1.val
    · obtain ⟨i, rfl⟩ := enumerate_surj k.1.val hj
      change (extendSets _ _ (enumerate _ i)).Nonempty at hne
      rw [extendSets_enumerate] at hne
      exact ((H k.1).rows k.2.1).axis_close k.2.2 i hne
    · change (extendSets _ _ j).Nonempty at hne
      rw [extendSets_outside _ _ hj] at hne
      exact False.elim (not_nonempty_empty hne)
  · intro k p u rad _ hrad
    change q D.L {j | p ∈ extendSets k.1.val ((H k.1).row k.2) j ∧ pd (dirs k j) u ≤ rad} ≤ _
    rw [predicate_count_extendSets]
    have hcount : q D.L {j | p ∈ W k j} =
        q k.1.val.card {i | p ∈ (H k.1).row k.2 i} := by
      simpa only [and_true] using predicate_count_extendSets k.1.val ((H k.1).row k.2)
        (fun _ => True) p
    rw [hcount]
    exact ((H k.1).rows k.2.1).broad k.2.2 p u rad hrad
  · intro k hk
    have hh := ((H k.1).rows k.2.1).dimensions k.2.2 (hocc k hk) |>.2.2.2.2
    change 2 * ((H k.1).rows k.2.1).middle k.2.2 ≤
      21474836480 * c * ((H k.1).packet k.2.1).scale
    nlinarith only [hh]

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
