-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalStripPriorBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalStripPriorBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalStripPriorBudget.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalStripPriorBudget.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeStripStates


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open Submission.Lib.K4Homogenization

noncomputable section

def stripVisitBound (D : ℕ) (ρ b B E η K p : ℝ) : ℝ :=
  ((D : ℝ) + 1) * 7 ^ 4 * 7 ^ 4 *
    (2 * (2 * ((1 + 3 * B) * b) + (E + 3 * η * K) * (2 * ρ)) / p + 4)

/-- The positive-occupation groups of one original trajectory have
the actual geometric visit bound. The duration support supplies all
time witnesses; no measurable existential projection is used as a prior. -/
theorem original_strip_positive_count {X : Type*} [MeasurableSpace X]
    (signal : X → Polynomial ℝ) (a v : X → Fin 3 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (field : X × ℝ → Fin 3 → ℝ)
    (E : Set (X × ℝ)) (F : Finset ((Fin 4 → ℤ) × ℤ)) (l : X)
    (L ρ b B error η K p : ℝ) (hL : 0 ≤ L) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (he : 0 ≤ error) (hη : 0 ≤ η) (hK : 0 ≤ K) (hp : 0 < p)
    (D : ℕ) (hD : 1 ≤ D) (hscale : L ≤ (D : ℝ) * ρ)
    (hsignal : (signal l).natDegree ≤ 2) (ha0 : a l 0 = 0) (hv0 : v l 0 = 1)
    (hvel : ∀ j, |v l j| ≤ K)
    (hLip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ j,
      |originalPhysicalCoordinates (signal l) (a l) (v l) t j -
        originalPhysicalCoordinates (signal l) (a l) (v l) s j| ≤ L * |t - s|)
    (hrow_bound : ∀ C j, |row C j| ≤ B)
    (hunit : ∀ t, (l,t) ∈ E → t ∈ Icc (0 : ℝ) 1)
    (hgraph : ∀ t, (l,t) ∈ E →
      |(signal l).derivative.eval t - ∑ j, field (l,t) j * v l j| ≤ error)
    (hrow : ∀ t, (l,t) ∈ E → ∀ j,
      |field (l,t) j - row
        (roundedPhysicalCode b ρ (originalPhysicalCoordinates (signal l) (a l) (v l) t)) j| ≤ η) :
    ((F.filter fun i => 0 < incidenceDuration volume
      (originalStripDensity E (originalStripLabel b ρ p row signal a v) i) univ l).card : ENNReal) ≤
        ENNReal.ofReal (stripVisitBound D ρ b B error η K p) := by
  classical
  let label := originalStripLabel b ρ p row signal a v
  let G := originalStripDensity E label
  let S := F.filter fun i => 0 < incidenceDuration volume (G i) univ l
  have hex (i : (Fin 4 → ℤ) × ℤ) (hi : i ∈ S) : ∃ t, G i (l,t) ≠ 0 :=
    exists_original_occupation volume (G i) l (Finset.mem_filter.mp hi).2
  let time : ((Fin 4 → ℤ) × ℤ) → ℝ := fun i =>
    if hi : i ∈ S then Classical.choose (hex i hi) else 0
  have htime (i : (Fin 4 → ℤ) × ℤ) (hi : i ∈ S) : G i (l,time i) ≠ 0 := by
    dsimp only [time]
    rw [dif_pos hi]
    exact Classical.choose_spec (hex i hi)
  have htrace (i : (Fin 4 → ℤ) × ℤ) (hi : i ∈ S) :
      (l,time i) ∈ E ∧ label (l,time i) = i :=
    (originalStripDensity_ne_zero E label i (l,time i)).mp (htime i hi)
  have hcode (i : (Fin 4 → ℤ) × ℤ) (hi : i ∈ S) :
      (roundedPhysicalCode b ρ (originalPhysicalCoordinates (signal l) (a l) (v l) (time i)),
        ⌊originalNormalStateCenter (signal l) (a l) (v l)
          (row (roundedPhysicalCode b ρ
            (originalPhysicalCoordinates (signal l) (a l) (v l) (time i)))) b (time i) / p⌋) = i := by
    have hh := (htrace i hi).2
    change nativeStripState b ρ p row _ = i at hh
    rw [nativeStripState_original] at hh
    exact hh
  have hcoarse (i : (Fin 4 → ℤ) × ℤ) (hi : i ∈ S) :
      roundedPhysicalCode b ρ (originalPhysicalCoordinates (signal l) (a l) (v l) (time i)) = i.1 :=
    congrArg Prod.fst (hcode i hi)
  have hcount := original_normal_strip_pairs_count S (signal l) hsignal (a l) (v l) ha0 hv0
    row (fun t => field (l,t)) time L ρ b B error η K p hL hρ hb hbρ hB he hη hK hp
    D hD hscale hLip hrow_bound hvel
    (fun i hi => hunit (time i) (htrace i hi).1) hcoarse
    (fun i hi => hgraph (time i) (htrace i hi).1)
    (fun i hi j => by simpa only [hcoarse i hi] using hrow (time i) (htrace i hi).1 j)
    (fun i hi => by
      have hh := congrArg Prod.snd (hcode i hi)
      simpa only [hcoarse i hi] using hh)
  have h := ENNReal.ofReal_le_ofReal hcount
  simpa only [ENNReal.ofReal_natCast, S, G, label, stripVisitBound] using h

/-- The total supporting original priors at one normal-strip resolution
are controlled by the actual curve and normal derivative geometry. -/
theorem actual_strip_support_prior_budget {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (signal : X → Polynomial ℝ) (a v : X → Fin 3 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (field : X × ℝ → Fin 3 → ℝ)
    {E : Set (X × ℝ)} (hE : MeasurableSet E) (F : Finset ((Fin 4 → ℤ) × ℤ))
    (L ρ b B error η K p : ℝ) (hL : 0 ≤ L) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (he : 0 ≤ error) (hη : 0 ≤ η) (hK : 0 ≤ K) (hp : 0 < p)
    (D : ℕ) (hD : 1 ≤ D) (hscale : L ≤ (D : ℝ) * ρ)
    (hphys : Measurable (fun z : X × ℝ =>
      originalPhysicalCoordinates (signal z.1) (a z.1) (v z.1) z.2))
    (hline : ∀ᵐ l ∂ν, (signal l).natDegree ≤ 2 ∧ a l 0 = 0 ∧ v l 0 = 1 ∧
      (∀ j, |v l j| ≤ K) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ j,
        |originalPhysicalCoordinates (signal l) (a l) (v l) t j -
          originalPhysicalCoordinates (signal l) (a l) (v l) s j| ≤ L * |t - s|)
    (hrow_bound : ∀ C j, |row C j| ≤ B)
    (hunit : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hgraph : ∀ z ∈ E,
      |(signal z.1).derivative.eval z.2 - ∑ j, field z j * v z.1 j| ≤ error)
    (hrow : ∀ z ∈ E, ∀ j,
      |field z j - row (roundedPhysicalCode b ρ
        (originalPhysicalCoordinates (signal z.1) (a z.1) (v z.1) z.2)) j| ≤ η) :
    (∑ i ∈ F, ν (originalOccupationSupport volume
      (originalStripDensity E (originalStripLabel b ρ p row signal a v) i))) ≤
      ENNReal.ofReal (stripVisitBound D ρ b B error η K p) * ν univ := by
  have hlabel := measurable_originalStripLabel b ρ p row signal a v hphys
  apply original_support_prior_budget ν volume F _
    (fun i _ => measurable_originalStripDensity hE _ hlabel i)
  filter_upwards [hline] with l hl
  exact original_strip_positive_count signal a v row field E F l L ρ b B error η K p
    hL hρ hb hbρ hB he hη hK hp D hD hscale hl.1 hl.2.1 hl.2.2.1 hl.2.2.2.1
    hl.2.2.2.2 hrow_bound (fun t ht => hunit (l,t) ht)
    (fun t ht => hgraph (l,t) ht) (fun t ht => hrow (l,t) ht)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
