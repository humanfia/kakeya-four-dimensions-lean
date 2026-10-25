/- Adapted from this LOT tree, o152, session x0513,
   Submission/Obl/k4_finite_width_path_realization/Raw/Layers.lean.
   Uses the accepted o153 Data/Atlas and our forest packaging. -/
import Submission.Obl.k4_raw_critical_segment_forests.Preparation
import Submission.Obl.k4_raw_critical_segment_forests.AtlasDepth

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def Forest.layerLabels {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ) : Finset (Fin a.C) :=
  Finset.univ.filter (fun b => a.lev b = i)

abbrev Forest.layerEmb {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ) :
    Fin (a.layerLabels i).card ↪ Fin a.C :=
  ((a.layerLabels i).orderEmbOfFin rfl).toEmbedding

lemma Forest.layerEmb_lev {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ)
    (b : Fin (a.layerLabels i).card) : a.lev (a.layerEmb i b) = i := by
  have hm := (a.layerLabels i).orderEmbOfFin_mem rfl b
  exact (Finset.mem_filter.mp hm).2

abbrev Forest.layerLists {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C))
    (γ : Fin (p.W k)) (o : Observation) : Finset (Fin (a.layerLabels i).card) :=
  Finset.univ.filter (fun b => a.layerEmb i b ∈ lst i γ o)

abbrev Forest.layerAtlas {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ)
    (hj : ∀ b, a.lev b = i → a.j b < 2 ^ a.T i)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)) : Atlas p k where
  T := a.T i
  C := (a.layerLabels i).card
  γ b := a.γ (a.layerEmb i b)
  j b := ⟨a.j (a.layerEmb i b), hj _ (a.layerEmb_lev i b)⟩
  c b := a.c (a.layerEmb i b)
  u b := a.u (a.layerEmb i b)
  Q b := a.Q (a.layerEmb i b)
  R b := a.R (a.layerEmb i b)
  A b := a.A (a.layerEmb i b)
  F b := a.F (a.layerEmb i b)
  lst := a.layerLists i lst

lemma Forest.Core.j_lt {p : Data} {k M D m : ℕ} {r : ℕ → ℝ} {a : Forest p k}
    (ha : a.Core M D m r) {i : ℕ} (b : Fin a.C) (hb : a.lev b = i) :
    a.j b < 2 ^ a.T i := by
  have hj := (ha.2.2.2.2.2 b).2.1
  rwa [hb] at hj

lemma Forest.layer_mass {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ) :
    (∑ b : Fin (a.layerLabels i).card,
      ENNReal.ofReal (p.ω k (a.γ (a.layerEmb i b))) *
        priorMass p k (a.γ (a.layerEmb i b)) (a.F (a.layerEmb i b))) =
    ∑ b, if a.lev b = i then
      ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b) else 0 := by
  classical
  rw [← Finset.sum_filter]
  change (∑ b : Fin (a.layerLabels i).card, _) = ∑ b ∈ a.layerLabels i, _
  rw [Finset.sum_subtype (a.layerLabels i) (fun _ => Iff.rfl)]
  exact Fintype.sum_equiv ((a.layerLabels i).orderIsoOfFin rfl).toEquiv _ _ (fun _ => rfl)

lemma Forest.layer_trueDepth {p : Data} {k M D m : ℕ} {r : ℕ → ℝ} {a : Forest p k}
    (ha : a.Core M D m r) {i : ℕ} (hi : i < m)
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)) :
    TrueDepth (a.layerAtlas i (ha.j_lt · ·) lst) M D a.κ (r i) := by
  obtain ⟨hκ, hK, hC, hmass, hsep, hchart⟩ := ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : (a.layerLabels i).card ≤ a.C := by
      simpa using Finset.card_le_univ (a.layerLabels i)
    exact (show ((a.layerLabels i).card : ℝ) ≤ (a.C : ℝ) by exact_mod_cast hc).trans hC
  · intro b b' hbb' hγ hj
    exact hsep _ _ (fun he => hbb' ((a.layerEmb i).injective he))
      ((a.layerEmb_lev i b).trans (a.layerEmb_lev i b').symm) hγ (congrArg Fin.val hj)
  · intro b
    have hc := (hchart (a.layerEmb i b)).2.2.1
    simpa only [a.layerEmb_lev i b] using hc
  · change ENNReal.ofReal (a.κ⁻¹) ≤ ∑ b : Fin (a.layerLabels i).card, _
    rw [a.layer_mass]
    exact hmass i hi

lemma Forest.layer_prepared {p : Data} {k : ℕ} {r : ℕ → ℝ} {a : Forest p k}
    (lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C))
    (ha : a.Prepared r lst) (i : ℕ)
    (hj : ∀ b, a.lev b = i → a.j b < 2 ^ a.T i) :
    (∀ γ o, (((a.layerAtlas i hj lst).lst γ o).card : ℝ) ≤ a.κ) ∧
    (∀ b, p.ν k ((a.layerAtlas i hj lst).γ b) ((a.layerAtlas i hj lst).A b) ≤
      ENNReal.ofReal (a.κ * p.N k ^ (-p.f (r i)) *
        |Matrix.det ((a.layerAtlas i hj lst).Q b)|) ∧
      ∀ z ∈ (a.layerAtlas i hj lst).F b,
        b ∈ (a.layerAtlas i hj lst).lst ((a.layerAtlas i hj lst).γ b)
          (obs (p.B k ((a.layerAtlas i hj lst).γ b)) (δ (p.N k) (r i)) z)) := by
  classical
  constructor
  · intro γ o
    have hc : ((a.layerAtlas i hj lst).lst γ o).card ≤ (lst i γ o).card := by
      apply Finset.card_le_card_of_injOn (a.layerEmb i)
      · intro b hb
        exact (Finset.mem_filter.mp hb).2
      · exact (a.layerEmb i).injective.injOn
    exact (show (((a.layerAtlas i hj lst).lst γ o).card : ℝ) ≤ ((lst i γ o).card : ℝ)
      by exact_mod_cast hc).trans (ha.1 i γ o)
  · intro b
    have hb := ha.2 (a.layerEmb i b)
    rw [a.layerEmb_lev i b] at hb
    refine ⟨hb.1, ?_⟩
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb.2 z hz⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
