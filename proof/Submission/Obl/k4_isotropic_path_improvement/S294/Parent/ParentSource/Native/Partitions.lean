-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.Partitions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/Partitions.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/Partitions.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/Partitions.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/Partitions.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PacketLaws
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

/-! Exact original residual mass decompositions at a fixed path level. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Distinct closed dyadic time blocks overlap only on a null time slice.
The endpoint inclusion is imported from the accepted scalar packet API. -/
theorem dyadic_product_blocks_aedisjoint {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (T : ℕ) {j j' : Fin (2 ^ T)} (hjj : j ≠ j') (A A' : Set X) :
    AEDisjoint (ν.prod volume)
      (A ×ˢ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T j)
      (A' ×ˢ Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block T j') := by
  change (ν.prod volume) ((_ ×ˢ _) ∩ (_ ×ˢ _)) = 0
  rcases lt_or_gt_of_ne hjj with hlt | hgt
  · apply measure_mono_null _ (show (ν.prod volume) (univ ×ˢ {((j' : ℕ) : ℝ) / (2 : ℝ) ^ T}) = 0 by
      simp [Measure.prod_prod])
    rintro ⟨l, t⟩ ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩
    exact ⟨mem_univ _,
      Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_inter_subset T hlt ⟨ht, ht'⟩⟩
  · apply measure_mono_null _ (show (ν.prod volume) (univ ×ˢ {((j : ℕ) : ℝ) / (2 : ℝ) ^ T}) = 0 by
      simp [Measure.prod_prod])
    rintro ⟨l, t⟩ ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩
    exact ⟨mem_univ _,
      Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block_inter_subset T hgt ⟨ht', ht⟩⟩

/-- A finite family of packets disjoint in each world is counted exactly once
by the original world mixture. -/
theorem weighted_packet_union_mass {ι Γ X : Type*} [Fintype Γ] [MeasurableSpace X]
    (μ : Γ → Measure X) (weight : Γ → ENNReal) (γ : ι → Γ)
    (F : ι → Set X) (ids : Finset ι)
    (hmeas : ∀ b ∈ ids, MeasurableSet (F b))
    (hdisj : ∀ b ∈ ids, ∀ b' ∈ ids, b ≠ b' → γ b = γ b' →
      AEDisjoint (μ (γ b)) (F b) (F b')) :
    (∑ w, weight w * μ w {z | ∃ b ∈ ids, γ b = w ∧ z ∈ F b}) =
      ∑ b ∈ ids, weight (γ b) * μ (γ b) (F b) := by
  classical
  have hworld (w : Γ) : μ w {z | ∃ b ∈ ids, γ b = w ∧ z ∈ F b} =
      ∑ b ∈ ids, if γ b = w then μ w (F b) else 0 := by
    let sw := ids.filter (fun b => γ b = w)
    have hunion : {z | ∃ b ∈ ids, γ b = w ∧ z ∈ F b} = ⋃ b ∈ sw, F b := by
      ext z
      simp only [mem_ofPred_eq, mem_iUnion, sw, Finset.mem_filter]
      aesop
    have hd : (↑sw : Set ι).Pairwise (fun b b' => AEDisjoint (μ w) (F b) (F b')) := by
      intro b hb b' hb' hne
      obtain ⟨hbi, hbw⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb'i, hb'w⟩ := Finset.mem_filter.mp hb'
      simpa only [hbw] using hdisj b hbi b' hb'i hne (hbw.trans hb'w.symm)
    calc
      _ = μ w (⋃ b ∈ sw, F b) := congrArg (μ w) hunion
      _ = ∑ b ∈ sw, μ w (F b) :=
        measure_biUnion_finset₀ hd (fun b hb => (hmeas b (Finset.mem_filter.mp hb).1).nullMeasurableSet)
      _ = _ := by
        simpa only [sw] using (Finset.sum_filter (s := ids) (fun b => γ b = w) (fun b => μ w (F b)))
  calc
    _ = ∑ w, ∑ b ∈ ids, if γ b = w then weight w * μ w (F b) else 0 := by
      simp_rw [hworld, Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ b ∈ ids, ∑ w, if γ b = w then weight w * μ w (F b) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      simp

section ValidPath

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.packet_aedisjoint
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b b' : Fin p.C) (hne : b ≠ b') (hlev : p.lev b = p.lev b') (hγ : p.γ b = p.γ b') :
    AEDisjoint ((ν (p.γ b)).prod volume) (p.F b) (p.F b') := by
  rcases h.2.2.2.2.2.2.2 b with ⟨_, hj, _, _, _, _, _, _, _, _, _, _, hFb, _⟩
  rcases h.2.2.2.2.2.2.2 b' with ⟨_, hj', _, _, _, _, _, _, _, _, _, _, hFb', _⟩
  by_cases htime : p.j b = p.j b'
  · apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hA := h.2.2.2.2.2.2.1 b b' hne hlev hγ htime
    exact Set.disjoint_left.mp hA (hFb z hz).2.1 (hFb' z hz').2.1
  · let T := p.T (p.lev b)
    have hj'' : p.j b' < 2 ^ T := by simpa only [T, hlev] using hj'
    let j : Fin (2 ^ T) := ⟨p.j b, hj⟩
    let j' : Fin (2 ^ T) := ⟨p.j b', hj''⟩
    have hjne : j ≠ j' := fun heq => htime (congrArg Fin.val heq)
    have hrect := dyadic_product_blocks_aedisjoint (ν (p.γ b)) T hjne (p.A b) (p.A b')
    apply hrect.mono
    · intro z hz
      exact ⟨(hFb z hz).2.1, (hFb z hz).2.2.1⟩
    · intro z hz
      refine ⟨(hFb' z hz).2.1, ?_⟩
      simpa only [Submission.Obl.k4_scalar_terminal_chart_packet_extraction.block, j', T, hlev]
        using (hFb' z hz).2.2.1

/-- Closed endpoint overlaps are null, so the earlier-level packet mixture
accounts for precisely the original residual mass. -/
theorem PathData.Valid.residual_mass_eq_sum
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hmeas : ∀ w, MeasurableSet (H w))
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) :
    (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w)) =
      ∑ b, if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) *
        ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) else 0 := by
  classical
  have hcover := h.covered_at_level H i hi hH
  have hworld (w : Fin W) : ((ν w).prod volume) (H w) =
      ∑ b, if p.lev b = i ∧ p.γ b = w then
        ((ν w).prod volume) (H w ∩ p.F b) else 0 := by
    let ids : Finset (Fin p.C) := Finset.univ.filter (fun b => p.lev b = i ∧ p.γ b = w)
    have hunion : H w = ⋃ b ∈ ids, H w ∩ p.F b := by
      ext z
      constructor
      · intro hz
        obtain ⟨b, hbi, hbw, hbz⟩ := hcover w hz
        exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨by simp [ids, hbi, hbw], hz, hbz⟩⟩
      · intro hz
        obtain ⟨b, hzb⟩ := mem_iUnion.mp hz
        obtain ⟨_, hz⟩ := mem_iUnion.mp hzb
        exact hz.1
    have hd : (↑ids : Set (Fin p.C)).Pairwise
        (fun b b' => AEDisjoint ((ν w).prod volume) (H w ∩ p.F b) (H w ∩ p.F b')) := by
      intro b hb b' hb' hne
      obtain ⟨hbi, hbw⟩ := (Finset.mem_filter.mp hb).2
      obtain ⟨hb'i, hb'w⟩ := (Finset.mem_filter.mp hb').2
      have hp := h.packet_aedisjoint b b' hne (hbi.trans hb'i.symm) (hbw.trans hb'w.symm)
      rw [hbw] at hp
      exact hp.mono inter_subset_right inter_subset_right
    have hm (b : Fin p.C) (_ : b ∈ ids) :
        NullMeasurableSet (H w ∩ p.F b) ((ν w).prod volume) := by
      rcases h.2.2.2.2.2.2.2 b with ⟨_, _, _, _, _, _, _, _, _, hF, _⟩
      exact ((hmeas w).inter hF).nullMeasurableSet
    conv_lhs => rw [hunion]
    rw [measure_biUnion_finset₀ hd hm]
    simpa only [ids] using (Finset.sum_filter (s := Finset.univ)
      (fun b : Fin p.C => p.lev b = i ∧ p.γ b = w)
      (fun b => ((ν w).prod volume) (H w ∩ p.F b)))
  calc
    _ = ∑ w, ENNReal.ofReal (ω w) *
        ∑ b, if p.lev b = i ∧ p.γ b = w then ((ν w).prod volume) (H w ∩ p.F b) else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      rw [hworld w]
    _ = _ := sum_packet_mixture p.lev p.γ i _ _

end ValidPath

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
