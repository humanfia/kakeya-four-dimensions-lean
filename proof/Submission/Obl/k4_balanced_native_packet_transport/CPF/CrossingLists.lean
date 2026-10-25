/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/CrossingLists.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/CrossingLists.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.FullCrossingFormat
import Submission.Obl.k4_balanced_native_packet_transport.CPF.FiniteCrossingPruning

/-! Finite chart-label lists, with their exact Boolean-format selection guard. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set MeasureTheory
open scoped Classical

noncomputable section

def Atlas.crossingSets {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (γ : Fin (p.W k))
    (b : Fin a.C) : Set Observation :=
  {o | a.γ b = γ ∧ BoundedChartCrosses a.κ a.T (a.j b : ℝ) (δ (p.N k) r)
    (p.B k γ) (a.c b) (a.u b) (a.Q b) (a.R b) m (bins γ) o}

def Atlas.crossingList {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (γ : Fin (p.W k)) (o : Observation) :
    Finset (Fin a.C) := finiteCrossingList (a.crossingSets r bins m γ) o

def Atlas.shortCrossingList {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (H : ℝ)
    (γ : Fin (p.W k)) (o : Observation) : Finset (Fin a.C) :=
  if ((a.crossingList r bins m γ o).card : ℝ) ≤ H then a.crossingList r bins m γ o else ∅

theorem Atlas.shortCrossingList_card {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) {H : ℝ} (hH : 0 ≤ H)
    (γ : Fin (p.W k)) (o : Observation) :
    ((a.shortCrossingList r bins m H γ o).card : ℝ) ≤ H := by
  unfold shortCrossingList
  split_ifs with h
  · exact h
  · simpa using hH

def Atlas.crossingKeep {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (H : ℝ) (b : Fin a.C) : Set Incidence :=
  {q | ((a.crossingList r bins m (a.γ b)
    (obs (p.B k (a.γ b)) (δ (p.N k) r) q)).card : ℝ) ≤ H}

theorem Atlas.mem_shortCrossingList {p : Data} {k : ℕ} (a : Atlas p k)
    {r : ℝ} {bins : Fin (p.W k) → Finset ℤ} {m : ℕ} {H : ℝ}
    {b : Fin a.C} {q : Incidence}
    (hc : ChartCrosses a.κ a.T (a.j b : ℝ) (δ (p.N k) r) (p.B k (a.γ b))
      (a.c b) (a.u b) (a.Q b) (a.R b) m
        (obs (p.B k (a.γ b)) (δ (p.N k) r) q))
    (hbin : (obs (p.B k (a.γ b)) (δ (p.N k) r) q).2 ∈ bins (a.γ b))
    (hkeep : q ∈ a.crossingKeep r bins m H b) :
    b ∈ a.shortCrossingList r bins m H (a.γ b)
      (obs (p.B k (a.γ b)) (δ (p.N k) r) q) := by
  change ((a.crossingList r bins m (a.γ b)
    (obs (p.B k (a.γ b)) (δ (p.N k) r) q)).card : ℝ) ≤ H at hkeep
  rw [shortCrossingList, if_pos hkeep]
  change b ∈ (Finset.univ : Finset (Fin a.C)).filter
    (fun b' => obs (p.B k (a.γ b)) (δ (p.N k) r) q ∈ a.crossingSets r bins m (a.γ b) b')
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hbin, hc⟩

/-- The finite count guard is polynomial even though it counts all chart labels. -/
theorem Atlas.format_crossingCount {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (H : ℝ) (γ : Fin (p.W k))
    (hκ : 0 ≤ a.κ) (hR : ∀ b, (a.R b).totalDegree ≤ 2) (i : ℕ) :
    fmt 7 ((a.C : ℝ) * ((bins γ).card * (5 + 4 * m))) 4
      {z : Fin 7 → ℝ | ((a.crossingList r bins m γ
        (obs (p.B k γ) (δ (p.N k) r) (rawIncidence i z))).card : ℝ) ≤ H} := by
  let S : Fin a.C → Set (Fin 7 → ℝ) := fun b =>
    {z | obs (p.B k γ) (δ (p.N k) r) (rawIncidence i z) ∈ a.crossingSets r bins m γ b}
  have hS (b : Fin a.C) : fmt 7 ((bins γ).card * (5 + 4 * m)) 4 (S b) := by
    by_cases hb : a.γ b = γ
    · simpa only [S, crossingSets, mem_ofPred_eq, hb, true_and] using
        format_boundedChartCrosses (a.R b) (hR b) hκ a.T (a.j b : ℝ)
          (δ (p.N k) r) (p.B k γ) (a.c b) (a.u b) (a.Q b) m (bins γ) i
    · have hs : S b = ∅ := by ext z; simp [S, crossingSets, hb]
      rw [hs]
      exact Submission.Obl.k4_quadratic_atlas_normalization.fmt_empty 7 4 (by positivity)
  have h := fmt.count_le S (fun _ => (bins γ).card * (5 + 4 * m)) hS H
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    crossingList, finiteCrossingList, S, Set.mem_ofPred_eq] using h

theorem Atlas.format_crossingKeep {p : Data} {k : ℕ} (a : Atlas p k) (r : ℝ)
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (H : ℝ)
    (hκ : 0 ≤ a.κ) (hR : ∀ b, (a.R b).totalDegree ≤ 2) (b : Fin a.C) (i : ℕ) :
    fmt 7 ((a.C : ℝ) * ((bins (a.γ b)).card * (5 + 4 * m))) 4
      {z : Fin 7 → ℝ | rawIncidence i z ∈ a.crossingKeep r bins m H b} :=
  a.format_crossingCount r bins m H (a.γ b) hκ hR i

end
end Submission.Obl.k4_balanced_native_packet_transport.CPF
