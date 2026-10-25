-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathMass

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection
open scoped Classical

noncomputable section

/-- A label is retained exactly when the fixed incidence restriction meets
its original counted set. Original full trajectory assignments are kept. -/
abbrev PathData.ActiveLabel {W : ℕ} (p : PathData W) (H : Fin W → Set Incidence) (i : ℕ) :=
  {b : Fin p.C // p.lev b = i ∧ (H (p.world b) ∩ p.counted b).Nonempty}

noncomputable def PathData.activeCount {W : ℕ} (p : PathData W) (H : Fin W → Set Incidence) (i : ℕ) : ℕ :=
  Fintype.card (p.ActiveLabel H i)

noncomputable def PathData.activeEquiv {W : ℕ} (p : PathData W) (H : Fin W → Set Incidence) (i : ℕ) :
    Fin (p.activeCount H i) ≃ p.ActiveLabel H i :=
  (Fintype.equivFin (p.ActiveLabel H i)).symm

noncomputable def PathData.activeLabel {W : ℕ} (p : PathData W) (H : Fin W → Set Incidence) (i : ℕ) :
    Fin (p.activeCount H i) ↪ Fin p.C :=
  (p.activeEquiv H i).toEmbedding.trans (Function.Embedding.subtype _)

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

lemma PathData.activeLabel_level (H : Fin W → Set Incidence) (i : ℕ) (b : Fin (p.activeCount H i)) :
    p.lev (p.activeLabel H i b) = i := (p.activeEquiv H i b).property.1

lemma PathData.activeLabel_nonempty (H : Fin W → Set Incidence) (i : ℕ) (b : Fin (p.activeCount H i)) :
    (H (p.world (p.activeLabel H i b)) ∩ p.counted (p.activeLabel H i b)).Nonempty := (p.activeEquiv H i b).property.2

include hp

/-- Full assignments are nested along the supplied actual ancestor chain. -/
lemma PathData.Valid.ancestor_assignment_subset (b : Fin p.C) (i : ℕ) (hi : i ≤ p.lev b) :
    p.assigned b ⊆ p.assigned (forestAncestor p.lev p.par b i) :=
  (Submission.Obl.k4_fixed_menu_density_pruning.forestAncestor_incidence_subset
    p.lev p.par p.world p.assigned (fun b hb => (hp.parent b hb).1)
    (fun b hb => (hp.parent b hb).2.1)
    (fun b hb => (hp.parent b hb).2.2.1) b i hi).2

/-- The actual closed time blocks are nested along the same ancestor chain. -/
lemma PathData.Valid.ancestor_time_subset (b : Fin p.C) (i : ℕ) (hi : i ≤ p.lev b) :
    Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
        (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) ⊆
      Icc ((p.bin (forestAncestor p.lev p.par b i) : ℝ) / (2 : ℝ) ^ p.T i)
        (((p.bin (forestAncestor p.lev p.par b i) : ℝ) + 1) / (2 : ℝ) ^ p.T i) := by
  let I : Fin p.C → Set ℝ := fun b =>
    Icc ((p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b))
      (((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))
  have hsub : ∀ b, 0 < p.lev b → I b ⊆ I (p.par b) := by
    intro b hb t ht
    have hp := hp.parent b hb
    exact ⟨hp.2.2.2.2.1.trans ht.1, ht.2.trans hp.2.2.2.2.2⟩
  have h := (Submission.Obl.k4_fixed_menu_density_pruning.forestAncestor_incidence_subset
    p.lev p.par p.world I (fun b hb => (hp.parent b hb).1)
    (fun b hb => (hp.parent b hb).2.1) hsub b i hi).2
  simpa only [I, (hp.ancestor b i hi).1] using h

/-- Every active descendant has an active actual ancestor at each earlier
level. The conclusion uses the full old assignments and actual time blocks. -/
lemma PathData.Valid.active_labels_nested
    (H : Fin W → Set Incidence) {i j : ℕ} (hij : i ≤ j)
    (b : Fin (p.activeCount H j)) :
    ∃ a : Fin (p.activeCount H i),
      p.assigned (p.activeLabel H j b) ⊆ p.assigned (p.activeLabel H i a) ∧
      Icc ((p.bin (p.activeLabel H j b) : ℝ) / (2 : ℝ) ^ p.T j)
          (((p.bin (p.activeLabel H j b) : ℝ) + 1) / (2 : ℝ) ^ p.T j) ⊆
        Icc ((p.bin (p.activeLabel H i a) : ℝ) / (2 : ℝ) ^ p.T i)
          (((p.bin (p.activeLabel H i a) : ℝ) + 1) / (2 : ℝ) ^ p.T i) := by
  let old := p.activeLabel H j b
  have hold : p.lev old = j := p.activeLabel_level H j b
  have hi : i ≤ p.lev old := by omega
  let anc := forestAncestor p.lev p.par old i
  have hanc := hp.ancestor old i hi
  have haworld : p.world anc = p.world old := hanc.2.1
  have hne : (H (p.world anc) ∩ p.counted anc).Nonempty := by
    obtain ⟨z, hzH, hzF⟩ := p.activeLabel_nonempty H j b
    exact ⟨z, by simpa only [haworld] using hzH, hanc.2.2 hzF⟩
  let a : Fin (p.activeCount H i) := (p.activeEquiv H i).symm ⟨anc, hanc.1, hne⟩
  have hea : p.activeLabel H i a = anc := by
    exact congrArg Subtype.val ((p.activeEquiv H i).apply_symm_apply ⟨anc, hanc.1, hne⟩)
  refine ⟨a, ?_, ?_⟩
  · rw [hea]
    exact hp.ancestor_assignment_subset old i hi
  · rw [hea]
    simpa only [hold] using hp.ancestor_time_subset old i hi

/-- The retained terminal incidences are covered by active labels at EVERY
earlier level, for the same fixed restriction H. -/
lemma PathData.Valid.active_labels_cover
    (H : Fin W → Set Incidence) (w : Fin W)
    (hH : ∀ w, H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    (i : ℕ) (hi : i < m) {z : Incidence} (hz : z ∈ H w) :
    ∃ b : Fin (p.activeCount H i),
      p.world (p.activeLabel H i b) = w ∧ z ∈ p.counted (p.activeLabel H i b) := by
  obtain ⟨old, hold, hw, hzold⟩ := hH w hz
  have hilev : i ≤ p.lev old := by omega
  let anc := forestAncestor p.lev p.par old i
  have hanc := hp.ancestor old i hilev
  have hzanc : z ∈ p.counted anc := hanc.2.2 hzold
  have haworld : p.world anc = w := hanc.2.1.trans hw
  let b : Fin (p.activeCount H i) := (p.activeEquiv H i).symm
    ⟨anc, hanc.1, ⟨z, by simpa only [haworld] using hz, hzanc⟩⟩
  have heb : p.activeLabel H i b = anc :=
    congrArg Subtype.val ((p.activeEquiv H i).apply_symm_apply _)
  refine ⟨b, ?_, ?_⟩
  · rw [heb]
    exact hanc.2.1.trans hw
  · rwa [heb]

end

end

end Submission.Obl.k4_finite_affine_parent_sources
