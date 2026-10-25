-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_endpoint_bootstrap.Estimates

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

abbrev Tube (d : ℝ) (x v : Space) : Set Space :=
  Metric.thickening d (segment ℝ x (x + v))

abbrev Katz := WangZahlLot.Obl.wz_endpoint_bootstrap.Katz
abbrev Frostman := WangZahlLot.Obl.wz_endpoint_bootstrap.Frostman
abbrev Dense := WangZahlLot.Obl.wz_endpoint_bootstrap.Dense

/-- The geometric hypotheses shared by all the estimates. -/
def Admissible {n : ℕ} (d : ℝ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
    (∀ i, ‖v i‖ = 1 ∧ Tube d (x i) (v i) ⊆ Metric.ball 0 1 ∧
      MeasurableSet (Y i) ∧ Y i ⊆ Tube d (x i) (v i)) ∧
    ∀ i j, i ≠ j → volume (Tube d (x i) (v i) ∩ Tube d (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (Tube d (x i) (v i))

/-- The predicate `A` in the frozen statement. -/
def Hypotheses (d η m l : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  Admissible d x v Y ∧ Dense d η Y ∧ Katz d m x v ∧ Frostman d l x v

/-- The input estimate `E(σ,ω)`, with all family hypotheses bundled. -/
def Estimate (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ n x v Y,
      Hypotheses δ η m l n x v Y →
      ENNReal.ofReal (a * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) *
        (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i)

theorem hypotheses_iff {d η m l : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} :
    Hypotheses d η m l n x v Y ↔
      0 < n ∧
      (∀ i, ‖v i‖ = 1 ∧ Tube d (x i) (v i) ⊆ Metric.ball 0 1 ∧
        MeasurableSet (Y i) ∧ Y i ⊆ Tube d (x i) (v i)) ∧
      (∀ i j, i ≠ j → volume (Tube d (x i) (v i) ∩ Tube d (x j) (v j)) ≤
        (1 / 2 : ENNReal) * volume (Tube d (x i) (v i))) ∧
      ENNReal.ofReal (d ^ η * n * d ^ 2) ≤ ∑ i, volume (Y i) ∧
      Katz d m x v ∧ Frostman d l x v := by
  simp only [Hypotheses, Admissible, Dense, wz_endpoint_bootstrap.Dense, and_assoc]

theorem Hypotheses.mono {δ η η' m m' l l' : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Hypotheses δ η m l n x v Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : η ≤ η') (hm : m ≤ m') (hl : l ≤ l') :
    Hypotheses δ η' m' l' n x v Y := by
  exact ⟨h.1, h.2.1.mono hδ hδ1 hη, h.2.2.1.mono hm, h.2.2.2.mono hl⟩

theorem Hypotheses.mono_normalized {δ η η' : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Hypotheses δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') :
    Hypotheses δ η' (δ ^ (-η')) (δ ^ (-η')) n x v Y := by
  have hp : δ ^ (-η) ≤ δ ^ (-η') :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)
  exact h.mono hδ hδ1 hη hp hp

/-- All shadings and their union have finite volume. -/
theorem Admissible.volume_union_lt_top {δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ x v Y) : volume (⋃ i, Y i) < ⊤ := by
  have hsub : (⋃ i, Y i) ⊆ Metric.ball (0 : Space) 1 :=
    Set.iUnion_subset fun i => (h.2.1 i).2.2.2.trans (h.2.1 i).2.1
  exact lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top

/-- Positive density forces positive union volume; this uses no geometric decomposition. -/
theorem Hypotheses.volume_union_pos {δ η m l : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Hypotheses δ η m l n x v Y) (hδ : 0 < δ) :
    0 < volume (⋃ i, Y i) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr h.1.1
  have hm : 0 < ∑ i, volume (Y i) :=
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < δ ^ η * n * δ ^ 2)).trans_le h.2.1
  obtain ⟨i, -, hi⟩ := Finset.sum_pos_iff.mp hm
  exact hi.trans_le (measure_mono (Set.subset_iUnion Y i))

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
