/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file TimeRow.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Lib.K4CommonLocalChoice

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

/-- Inside one coefficient block, physical proximity to the central curve
turns the selected physical row into a measurable row depending only on time.
The construction retains every original active incidence. -/
theorem exists_time_only_row {α : Type*} {D : ℕ}
    (E : Set (α × ℝ)) (Z : α × ℝ → Fin D → ℝ) (c : ℝ → Fin D → ℝ)
    (g : α × ℝ → ℝ) {K B ρ : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hg : ∀ p ∈ E, |g p| ≤ B)
    (hclose : ∀ p ∈ E, ‖Z p - c p.2‖ ≤ K * ρ)
    (hcenter : ∀ p ∈ E, ∀ q ∈ E, ‖c p.2 - c q.2‖ ≤ K * |p.2 - q.2|)
    (hcompare : ∀ p ∈ E, ∀ q ∈ E, |g p - g q| ≤ K * (‖Z p - Z q‖ + ρ)) :
    ∃ F : ℝ → ℝ, Measurable F ∧ (∀ t, |F t| ≤ B) ∧
      (∀ p ∈ E, |F p.2 - g p| ≤ 4 * K ^ 2 * ρ) ∧
      ∀ p ∈ E, ∀ q ∈ E,
        |F p.2 - F q.2| ≤ 12 * K ^ 2 * (|p.2 - q.2| + ρ) := by
  classical
  have hK0 : 0 ≤ K := by linarith
  let bin : ℝ → ℤ := fun t => ⌊t / ρ⌋
  let fbin : ℤ → ℝ := fun n =>
    if hn : ∃ p : α × ℝ, p ∈ E ∧ bin p.2 = n then g (Classical.choose hn) else 0
  let F : ℝ → ℝ := fun t => fbin (bin t)
  have hbin : Measurable bin := (measurable_id.div_const ρ).floor
  have hFmeas : Measurable F := (measurable_of_countable fbin).comp hbin
  have hFbound (t : ℝ) : |F t| ≤ B := by
    dsimp [F, fbin]
    split_ifs with hn
    · exact hg _ (Classical.choose_spec hn).1
    · simpa using hB
  have hposition (p : α × ℝ) (hp : p ∈ E) (q : α × ℝ) (hq : q ∈ E) :
      ‖Z p - Z q‖ ≤ K * (|p.2 - q.2| + 2 * ρ) := by
    calc
      _ ≤ ‖Z p - c p.2‖ + ‖c p.2 - Z q‖ := by
        simpa only [dist_eq_norm] using dist_triangle (Z p) (c p.2) (Z q)
      _ ≤ ‖Z p - c p.2‖ + (‖c p.2 - c q.2‖ + ‖c q.2 - Z q‖) := by
        gcongr
        simpa only [dist_eq_norm] using dist_triangle (c p.2) (c q.2) (Z q)
      _ ≤ K * ρ + (K * |p.2 - q.2| + K * ρ) := by
        gcongr
        · exact hclose p hp
        · exact hcenter p hp q hq
        · simpa only [norm_sub_rev] using hclose q hq
      _ = _ := by ring
  have happ (p : α × ℝ) (hp : p ∈ E) : |F p.2 - g p| ≤ 4 * K ^ 2 * ρ := by
    have hn : ∃ q : α × ℝ, q ∈ E ∧ bin q.2 = bin p.2 := ⟨p, hp, rfl⟩
    let q : α × ℝ := Classical.choose hn
    have hq : q ∈ E := (Classical.choose_spec hn).1
    have hqp : bin q.2 = bin p.2 := (Classical.choose_spec hn).2
    have hcell : cell ρ (fun _ : Fin 1 => q.2) = cell ρ (fun _ : Fin 1 => p.2) := by
      ext i
      exact hqp
    have hnorm := norm_sub_lt_of_cell_eq hρ hcell
    have hdt : |q.2 - p.2| ≤ ρ := by
      have hh := norm_le_pi_norm ((fun _ : Fin 1 => q.2) - (fun _ : Fin 1 => p.2))
        (0 : Fin 1)
      exact hh.trans hnorm.le
    have hpos : ‖Z q - Z p‖ ≤ 3 * K * ρ :=
      (hposition q hq p hp).trans (by nlinarith)
    have hh := (hcompare q hq p hp).trans
      (mul_le_mul_of_nonneg_left (add_le_add hpos le_rfl) hK0)
    have hfinal : |g q - g p| ≤ 4 * K ^ 2 * ρ := by
      have hnonneg : 0 ≤ K * ρ * (K - 1) := by positivity
      nlinarith
    simpa only [F, fbin, dite_eq_left hn, q] using hfinal
  refine ⟨F, hFmeas, hFbound, happ, ?_⟩
  intro p hp q hq
  have hdist0 : 0 ≤ |p.2 - q.2| := abs_nonneg _
  have hrows := (hcompare p hp q hq).trans
    (mul_le_mul_of_nonneg_left (add_le_add (hposition p hp q hq) le_rfl) hK0)
  have htriangle : |F p.2 - F q.2| ≤
      |F p.2 - g p| + |g p - g q| + |g q - F q.2| := by
    calc
      _ ≤ |F p.2 - g p| + |g p - F q.2| := abs_sub_le _ _ _
      _ ≤ |F p.2 - g p| + (|g p - g q| + |g q - F q.2|) := by
        gcongr
        exact abs_sub_le _ _ _
      _ = _ := by ring
  have h1 := happ p hp
  have h2 := happ q hq
  rw [abs_sub_comm (F q.2)] at h2
  have hK1 : 0 ≤ K * ρ * (K - 1) := by positivity
  have hK2 : 0 ≤ K ^ 2 * |p.2 - q.2| := by positivity
  have hK3 : 0 ≤ K ^ 2 * ρ := by positivity
  nlinarith only [htriangle, h1, h2, hrows, hK1, hK2, hK3]

end Submission.Obl.k4_scalar_graph_residual_discovery
