-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/EntryBudgets.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0674 via x0672,
-- commit69d09a7b, Submission/Obl/k4_greedy_cover_graph_atlas/EntryBudgets.lean.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.EntryPartition
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.EntryPruning
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set Finset

/-- Normalizing by the number of time blocks gives a unit original-prior budget. -/
theorem normalized_assignment_budget {X ι Γ : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype Γ] {J : ℕ} (hJ : 0 < J)
    (ν : Γ → Measure X) (w : Γ → ℝ) (γ : ι → Γ) (j : ι → Fin J) (A : ι → Set X)
    (hprob : ∀ g, IsProbabilityMeasure (ν g))
    (hw0 : ∀ g, 0 ≤ w g) (hw : ∑ g, w g = 1)
    (hA : ∀ b, MeasurableSet (A b))
    (hdisj : ∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) :
    (∑ b, ENNReal.ofReal (w (γ b)) *
      (ENNReal.ofReal ((J : ℝ)⁻¹) * ν (γ b) (A b))) ≤ 1 := by
  have hb := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget_ofReal
    ν w γ j A hprob hw0 hw hA hdisj
  rw [Fintype.card_fin] at hb
  have hunit : ENNReal.ofReal ((J : ℝ)⁻¹) * (J : ENNReal) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hJ), ENNReal.ofReal_natCast,
      ENNReal.inv_mul_cancel (by exact_mod_cast hJ.ne') (ENNReal.natCast_ne_top J)]
  calc
    _ = ENNReal.ofReal ((J : ℝ)⁻¹) * ∑ b, ENNReal.ofReal (w (γ b)) * ν (γ b) (A b) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ ENNReal.ofReal ((J : ℝ)⁻¹) * (J : ENNReal) := mul_le_mul' le_rfl hb
    _ = 1 := hunit

/-- The old packets at one path level spend at most one unit of prior times block length. -/
theorem normalized_level_assignment_budget {X Γ : Type*} [MeasurableSpace X] [Fintype Γ]
    {C Ti i : ℕ} (lev j : Fin C → ℕ) (γ : Fin C → Γ) (A : Fin C → Set X)
    (ν : Γ → Measure X) (w : Γ → ℝ)
    (hprob : ∀ g, IsProbabilityMeasure (ν g))
    (hw0 : ∀ g, 0 ≤ w g) (hw : ∑ g, w g = 1)
    (hj : ∀ b, lev b = i → j b < 2 ^ Ti)
    (hA : ∀ b, lev b = i → MeasurableSet (A b))
    (hdisj : ∀ b b', lev b = i → lev b' = i → b ≠ b' →
      γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) :
    (∑ b : {b : Fin C // lev b = i}, ENNReal.ofReal (w (γ b.val)) *
      (ENNReal.ofReal (((2 : ℝ) ^ Ti)⁻¹) * ν (γ b.val) (A b.val))) ≤ 1 := by
  classical
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    normalized_assignment_budget (J := 2 ^ Ti) (by positivity) ν w
      (fun b : {b : Fin C // lev b = i} => γ b.val)
      (fun b => (⟨j b.val, hj b.val b.property⟩ : Fin (2 ^ Ti))) (fun b => A b.val)
      hprob hw0 hw (fun b => hA b.val b.property)
      (fun b b' hne hγ hjj => hdisj b.val b'.val b.property b'.property
        (fun h => hne (Subtype.ext h)) hγ (congrArg Fin.val hjj))

/-- Uniform geometric entry tables cost their exact size in a packet-relative count. -/
theorem card_Entry_packet_le {n C s₀ K : ℕ} (old : Fin n → Fin C) (b : Fin C)
    {count : ℝ} (hcount : ((univ.filter (fun a => old a = b)).card : ℝ) ≤ count) :
    ((univ.filter (fun e : Entry n s₀ K => old e.1 = b)).card : ℝ) ≤
      count * ((2 : ℝ) ^ s₀ * ((2 * K + 2 : ℕ) : ℝ) ^ 2 * 4) := by
  rw [card_Entry_packet]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hcount
    (by positivity : 0 ≤ (2 : ℝ) ^ s₀ * ((2 * (K : ℝ) + 2) ^ 2) * 4)]

/-- Discarding only packet-relative light entries retains half the covered mass. -/
theorem heavy_entries_retain_half {α Γ : Type*} [Fintype α] [Fintype Γ] [DecidableEq Γ]
    (packet : α → Γ) (mass : α → ENNReal) (scale weight : Γ → ENNReal)
    (count threshold : ENNReal)
    (hcount : ∀ g, ((univ.filter (fun a => packet a = g)).card : ENNReal) ≤ count)
    (hbudget : (∑ g, weight g * scale g) ≤ 1)
    {m : ℝ} (hm : 0 ≤ m) (hmass : ENNReal.ofReal m ≤ ∑ a, weight (packet a) * mass a)
    (hloss : count * threshold ≤ ENNReal.ofReal (m / 2)) :
    ENNReal.ofReal (m / 2) ≤
      ∑ a ∈ univ.filter (fun a => scale (packet a) * threshold ≤ mass a),
        weight (packet a) * mass a := by
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    _ _ (count * threshold * ∑ g, weight g * scale g) m hm hmass
    (weighted_heavy_entry_floor packet mass scale weight count threshold hcount)
  calc
    _ ≤ count * threshold := by
      simpa only [mul_one] using mul_le_mul' (le_rfl : count * threshold ≤ count * threshold) hbudget
    _ ≤ _ := hloss

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
