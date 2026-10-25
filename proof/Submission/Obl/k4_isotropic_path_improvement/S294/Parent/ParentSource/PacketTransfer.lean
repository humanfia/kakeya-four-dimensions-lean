-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketTransfer.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Candidates
import Submission.Obl.k4_quadratic_finite_greedy_cover.ScaleTransfer

/-!
# Moving a candidate to finer path packets

The possible anisotropic route needs a capacity-weighted choice of a finer
packet, rather than a choice by the number of finer packets. These lemmas keep
all masses under the original law. They do not assert the geometric capacity
bound needed to apply them.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

/-- A capacity-weighted pigeonhole retains the ratio of the two global bounds.
Zero-capacity packets cannot be selected. -/
theorem exists_packet_of_capacity_bound {ι : Type*} (s : Finset ι)
    (capacity mass : ι → ℝ) {reference α β : ℝ}
    (href : 0 < reference) (hα : 0 < α) (hβ : 0 < β)
    (hcap : ∀ b ∈ s, 0 ≤ capacity b)
    (hmass : ∀ b ∈ s, 0 ≤ mass b)
    (hdom : ∀ b ∈ s, mass b ≤ capacity b)
    (hlower : α * reference ≤ ∑ b ∈ s, mass b)
    (hupper : ∑ b ∈ s, capacity b ≤ β * reference) :
    ∃ b ∈ s, 0 < capacity b ∧ (α / β) * capacity b ≤ mass b := by
  classical
  let t := s.filter (fun b => 0 < capacity b)
  have hmzero : ∀ b ∈ s, b ∉ t → mass b = 0 := by
    intro b hb hbt
    have hc : capacity b = 0 := by
      have : ¬ 0 < capacity b := by simpa [t, hb] using hbt
      exact le_antisymm (le_of_not_gt this) (hcap b hb)
    exact le_antisymm ((hdom b hb).trans_eq hc) (hmass b hb)
  have hm : (∑ b ∈ t, mass b) = ∑ b ∈ s, mass b :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun b hb hbt => hmzero b hb hbt)
  have hc : (∑ b ∈ t, capacity b) ≤ ∑ b ∈ s, capacity b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b hb _ => hcap b hb)
  have ht : t.Nonempty := by
    by_contra h
    have hsum : (∑ b ∈ s, mass b) = 0 := by
      rw [← hm, Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty]
    have := hlower
    rw [hsum] at this
    exact (not_le_of_gt (mul_pos hα href)) this
  have htotal : (∑ b ∈ t, (α / β) * capacity b) ≤ ∑ b ∈ t, mass b := by
    rw [← Finset.mul_sum, hm]
    calc
      (α / β) * (∑ b ∈ t, capacity b) ≤ (α / β) * (β * reference) :=
        mul_le_mul_of_nonneg_left (hc.trans hupper) (div_pos hα hβ).le
      _ = α * reference := by field_simp
      _ ≤ _ := hlower
  obtain ⟨b, hb, hratio⟩ := Finset.exists_le_of_sum_le ht htotal
  exact ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2, hratio⟩

/-- Exponent cancellation when the finer packet capacities gain the profile
increment between the old and new depths. -/
theorem transferred_mass_factor {N : ℝ} (hN : 0 < N)
    (d oldGain depthShift error capError : ℝ) :
    N ^ (-(d * oldGain + error)) / N ^ (-d * depthShift + capError) =
      N ^ (-(d * (oldGain - depthShift) + error + capError)) := by
  rw [← Real.rpow_sub hN]
  congr 1
  ring

/-- Apply the capacity selection with the exact profile exponents. Neither the
number of fine packets nor a normalization of their laws appears in the floor. -/
theorem exists_packet_at_transferred_gain {ι : Type*} (s : Finset ι)
    (capacity mass : ι → ℝ) {reference N : ℝ} (hN : 0 < N)
    (href : 0 < reference) (d oldGain depthShift error capError : ℝ)
    (hcap : ∀ b ∈ s, 0 ≤ capacity b)
    (hmass : ∀ b ∈ s, 0 ≤ mass b)
    (hdom : ∀ b ∈ s, mass b ≤ capacity b)
    (hlower : N ^ (-(d * oldGain + error)) * reference ≤ ∑ b ∈ s, mass b)
    (hupper : ∑ b ∈ s, capacity b ≤
      N ^ (-d * depthShift + capError) * reference) :
    ∃ b ∈ s, 0 < capacity b ∧
      N ^ (-(d * (oldGain - depthShift) + error + capError)) * capacity b ≤ mass b := by
  simpa only [transferred_mass_factor hN] using
    exists_packet_of_capacity_bound s capacity mass href
      (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
      hcap hmass hdom hlower hupper

/-- The same selection in extended nonnegative mass, with finiteness assumptions
only on the reference and on the packets that occur in the finite cover. -/
theorem exists_packet_of_capacity_bound_ennreal {ι : Type*} (s : Finset ι)
    (capacity mass : ι → ENNReal) {reference : ENNReal} {α β : ℝ}
    (href : reference ≠ 0) (hreftop : reference ≠ ∞)
    (hα : 0 < α) (hβ : 0 < β)
    (hcap : ∀ b ∈ s, capacity b ≠ ∞)
    (hdom : ∀ b ∈ s, mass b ≤ capacity b)
    (hlower : ENNReal.ofReal α * reference ≤ ∑ b ∈ s, mass b)
    (hupper : ∑ b ∈ s, capacity b ≤ ENNReal.ofReal β * reference) :
    ∃ b ∈ s, capacity b ≠ 0 ∧ ENNReal.ofReal (α / β) * capacity b ≤ mass b := by
  have hmass : ∀ b ∈ s, mass b ≠ ∞ :=
    fun b hb => ne_top_of_le_ne_top (hcap b hb) (hdom b hb)
  have hmasssum := ENNReal.sum_ne_top.mpr hmass
  have hlow := ENNReal.toReal_mono hmasssum hlower
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le,
    ENNReal.toReal_sum hmass] at hlow
  have hup := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hreftop) hupper
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hβ.le,
    ENNReal.toReal_sum hcap] at hup
  obtain ⟨b, hb, hbpos, hbmass⟩ := exists_packet_of_capacity_bound s
    (fun b => (capacity b).toReal) (fun b => (mass b).toReal)
    (ENNReal.toReal_pos href hreftop) hα hβ
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun b hb => ENNReal.toReal_mono (hcap b hb) (hdom b hb)) hlow hup
  refine ⟨b, hb, ?_, ?_⟩
  · intro hzero
    simp [hzero] at hbpos
  · apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcap b hb)) (hmass b hb)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_pos hα hβ).le]
      using hbmass

/-- Covering the old counted set by finer packets and controlling their TOTAL
capacity finds a finer packet with the correct relative original-law mass.
No disjointness or measurability of the cover is needed for this step. -/
theorem exists_packet_of_measure_cover {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (packet : ι → Set X) (counted : Set X)
    {reference : ENNReal} {α β : ℝ}
    (href : reference ≠ 0) (hreftop : reference ≠ ∞)
    (hα : 0 < α) (hβ : 0 < β)
    (hfinite : ∀ b ∈ s, μ (packet b) ≠ ∞)
    (hcover : counted ⊆ ⋃ b ∈ s, packet b)
    (hlower : ENNReal.ofReal α * reference ≤ μ counted)
    (hupper : ∑ b ∈ s, μ (packet b) ≤ ENNReal.ofReal β * reference) :
    ∃ b ∈ s, μ (packet b) ≠ 0 ∧
      ENNReal.ofReal (α / β) * μ (packet b) ≤ μ (counted ∩ packet b) := by
  have hcover' : counted ⊆ ⋃ b ∈ s, counted ∩ packet b := by
    intro p hp
    obtain ⟨b, hpb⟩ := Set.mem_iUnion.mp (hcover hp)
    obtain ⟨hbs, hpb⟩ := Set.mem_iUnion.mp hpb
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hbs, hp, hpb⟩⟩
  apply exists_packet_of_capacity_bound_ennreal s (fun b => μ (packet b))
    (fun b => μ (counted ∩ packet b)) href hreftop hα hβ hfinite
    (fun _ _ => measure_mono inter_subset_right)
    (hlower.trans ((measure_mono hcover').trans (measure_biUnion_finset_le s _))) hupper

/-- The resulting floor in the exact product-law and dyadic-time units of the
frozen candidate. The old and fine references are never renormalized. -/
theorem exists_fine_packet_at_transferred_gain
    (ν : Measure (ℕ × (Fin 6 → ℝ))) {C : ℕ} (s : Finset (Fin C))
    (T : ℕ → ℕ) (lev : Fin C → ℕ) (j : Fin C → ℕ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (counted : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    {reference : ENNReal} {N : ℝ} (hN : 0 < N)
    (href : reference ≠ 0) (hreftop : reference ≠ ∞)
    (d oldGain depthShift error capError : ℝ)
    (hfinite : ∀ b ∈ s, ν (A b) ≠ ∞)
    (hcover : counted ⊆ ⋃ b ∈ s,
      k4_quadratic_finite_greedy_cover.packetRegion T lev j A b)
    (hlower : ENNReal.ofReal (N ^ (-(d * oldGain + error))) * reference ≤
      ν.prod volume counted)
    (hupper : ∑ b ∈ s,
      ν.prod volume (k4_quadratic_finite_greedy_cover.packetRegion T lev j A b) ≤
        ENNReal.ofReal (N ^ (-d * depthShift + capError)) * reference) :
    ∃ b ∈ s, ν (A b) ≠ 0 ∧
      ENNReal.ofReal (N ^ (-(d * (oldGain - depthShift) + error + capError)) /
        (2 : ℝ) ^ T (lev b)) * ν (A b) ≤
      ν.prod volume (counted ∩
        k4_quadratic_finite_greedy_cover.packetRegion T lev j A b) := by
  have hpacketfinite : ∀ b ∈ s,
      ν.prod volume (k4_quadratic_finite_greedy_cover.packetRegion T lev j A b) ≠ ∞ := by
    intro b hb
    rw [k4_quadratic_finite_greedy_cover.packetRegion_measure]
    exact ENNReal.mul_ne_top (hfinite b hb) ENNReal.ofReal_ne_top
  obtain ⟨b, hb, hbpos, hbmass⟩ := exists_packet_of_measure_cover
    (ν.prod volume) s _ counted href hreftop
    (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hN _)
    hpacketfinite hcover hlower hupper
  rw [k4_quadratic_finite_greedy_cover.packetRegion_measure] at hbpos hbmass
  refine ⟨b, hb, (mul_ne_zero_iff.mp hbpos).1, ?_⟩
  rw [transferred_mass_factor hN] at hbmass
  rw [div_eq_mul_one_div, ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)]
  convert hbmass using 1
  ring

/-- A counted certificate produces the exact residual candidate predicate. -/
theorem candidate_of_counted_data
    (Nk L : ℝ) (W C Mc : ℕ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (B : Fin W → ℝ) (d₁ ρ gain ε : ℝ) (r : ℕ → ℝ) (T : ℕ → ℕ)
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (a : k4_quadratic_finite_greedy_cover.CandidateDatum C)
    (hg : k4_quadratic_finite_greedy_cover.CandidateGeometry
      Nk L W C Mc B ρ gain ε r T lev γ j A a)
    (hc : k4_quadratic_finite_greedy_cover.CandidateCounted
      Nk L W C ν B d₁ ρ gain ε T lev γ j A H a) :
    k4_quadratic_finite_greedy_cover.candidate
      Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j A H := by
  rcases hg with ⟨hgain, hcap, hroom, hdeg, hcoeff, hAm, hAsub, hfit⟩
  refine ⟨a.parent, a.gain, hgain, hcap, hroom, a.test, a.trajectories,
    hdeg, hcoeff, hAm, hAsub, hfit, ?_⟩
  exact hc.2.2.2.trans (measure_mono (fun p hp => ⟨hc.2.1 hp, hc.2.2.1 p hp⟩))

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
