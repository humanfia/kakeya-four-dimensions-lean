/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/NativeCount.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeContact
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.FamilyCount

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- Count ACTUAL original child labels meeting one reference chart.  Their
whole original witnesses, intersected with the assigned ancestor fit set,
retain the atlas mass floors and lie in one common q-by-q-by-q-squared box.
Only the inherited parent band is used in the upper cap. -/
theorem original_contact_child_count {k : ℕ} {s t η D m : ℝ}
    (parent : cfg.AssignmentLevel k s) (child : cfg.AssignmentLevel k t)
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ)
    (hdom : cfg.μ k ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (j₀ : Fin (cfg.n k s)) (S : Finset (Fin (cfg.n k t)))
    (J : Fin (2 ^ cfg.T k t))
    (hblock : ∀ i ∈ S, cfg.j k t i = J)
    (hm : m = (((J : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k t)
    (hA : ∀ i ∈ S, cfg.A k t i ⊆ cfg.A k s j₀)
    (hI : ∀ i ∈ S, Data.I (cfg.T k t) (cfg.j k t i) ⊆
      Data.I (cfg.T k s) (cfg.j k s j₀))
    (p : Fin 3 → ℝ) (hv : |p 2| ≤ cfg.K k ^ 2)
    (hD : D ≤ cfg.timeLength k t ^ 2)
    (hcontact : ∀ i ∈ S, ∃ z₀ ∈ cfg.originalTrueBox k t i,
      |z₀ 1 - referenceZ p (z₀ 0)| ≤ cfg.K k ^ 2 * D ∧
      |z₀ 2 - referenceY p (z₀ 0)| ≤ cfg.K k ^ 2 * D)
    (P : Fin 4 → ℝ)
    (hparent : ∀ l ∈ cfg.B k s j₀, ∀ u ∈ Data.I (cfg.T k s) (cfg.j k s j₀),
      |(cfg.x k l u) 3 - (P 0 + ∑ e : Fin 3, P e.succ *
        cfg.originalBasePoint k (l, u) e)| ≤ cfg.K k * cfg.N k ^ (-s))
    (hη : 0 < η) (hmesh₀ : η ≤ cfg.timeLength k t / 2)
    (hmesh₁ : (|p 2| + 1) * η ≤ 8 * cfg.K k ^ 2 * cfg.timeLength k t)
    (hmesh₂ : (|-p 0 - m * p 2| + |m| + 1) * η ≤
      32 * cfg.K k ^ 4 * cfg.timeLength k t ^ 2)
    (hresolve : η * ∑ e : Fin 3, |P e.succ| ≤ cfg.N k ^ (-s))
    (hcap : ∀ (Q : Fin 3 → ℤ) (j : ℤ),
      cfg.μ k {ω | (fun e => ⌊cfg.originalBasePoint k ω e / η⌋) = Q ∧
        ⌊(cfg.x k ω.1 ω.2) 3 / cfg.N k ^ (-s)⌋ = j} ≤
        ENNReal.ofReal (cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d * η ^ 3)) :
    (S.card : ℝ) ≤ 73728 * cfg.K k ^ 11 *
      (cfg.N k ^ (-t) / cfg.N k ^ (-s)) ^ (-cfg.d) := by
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hq : 0 < cfg.timeLength k t := by unfold Data.timeLength; positivity
  have ha₀ : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have ha₁ : 0 < cfg.N k ^ (-t) := Real.rpow_pos_of_pos hN _
  let E : Fin (cfg.n k t) → Set (α × ℝ) :=
    fun i => (cfg.B k t i ∩ cfg.B k s j₀) ×ˢ Data.I (cfg.T k t) (cfg.j k t i)
  have hEm (i : Fin (cfg.n k t)) (_hi : i ∈ S) : MeasurableSet (E i) :=
    ((child.fitted_measurable i).inter (parent.fitted_measurable j₀)).prod measurableSet_Icc
  have hdisj : (S : Set (Fin (cfg.n k t))).PairwiseDisjoint E :=
    cfg.original_witness_family_disjoint child S (cfg.B k s j₀)
      (fun i hi j hj => (hblock i hi).trans (hblock j hj).symm)
  have hfloor (i : Fin (cfg.n k t)) (hi : i ∈ S) :
      ENNReal.ofReal (cfg.timeLength k t ^ 4 *
        ((cfg.N k ^ (-t) / cfg.N k ^ (-s)) * cfg.N k ^ (-s)) ^ cfg.d /
        cfg.K k ^ 3) ≤ cfg.μ k (E i) := by
    rw [div_mul_cancel₀ _ ha₀.ne']
    rw [show cfg.μ k (E i) = cfg.μ k
        (cfg.B k t i ×ˢ Data.I (cfg.T k t) (cfg.j k t i)) from
      cfg.inherited_witness_mass parent child hdom i j₀ (hA i hi) (hI i hi)]
    exact cfg.original_witness_floor child hν hN hKp hℓ i
  have hbox (i : Fin (cfg.n k t)) (hi : i ∈ S) (ω : α × ℝ) (hω : ω ∈ E i) :
      |cfg.originalBasePoint k ω 0 - m| ≤ cfg.timeLength k t / 2 ∧
      |cfg.originalBasePoint k ω 1 - referenceZ p m - p 2 *
        (cfg.originalBasePoint k ω 0 - m)| ≤ 8 * cfg.K k ^ 2 * cfg.timeLength k t ∧
      |cfg.originalBasePoint k ω 2 - referenceY p m - (-p 0 - m * p 2) *
        (cfg.originalBasePoint k ω 0 - m) - m *
        (cfg.originalBasePoint k ω 1 - referenceZ p m)| ≤
          32 * cfg.K k ^ 4 * cfg.timeLength k t ^ 2 := by
    obtain ⟨z₀, hz₀, hZ, hY⟩ := hcontact i hi
    have hmid : cfg.originalTimeCenter k t i = m := by
      dsimp [originalTimeCenter]
      rw [hblock i hi, hm]
    exact cfg.whole_original_child_common_box child hN hK hℓ i hmid p z₀ hv hD hz₀ hZ hY
      (cfg.originalBasePoint k ω) (cfg.original_witness_mem_trueBox child i ω ⟨hω.1.1, hω.2⟩)
  exact original_child_support_count (cfg.μ k) S E (cfg.originalBasePoint k)
    (fun ω => (cfg.x k ω.1 ω.2) 3) (fun e => P e.succ) (P 0) m
    (referenceZ p m) (referenceY p m) (p 2) (-p 0 - m * p 2) m
    (cfg.K k) (cfg.timeLength k t) η (cfg.N k ^ (-s))
    (cfg.N k ^ (-t) / cfg.N k ^ (-s)) cfg.d hK hq hη ha₀ (div_pos ha₁ ha₀)
    hmesh₀ hmesh₁ hmesh₂ hresolve hcap hEm hdisj hfloor hbox
    (fun i hi ω hω => hparent ω.1 hω.1.2 ω.2 (hI i hi hω.2))

end NativeModel
end Submission.Obl.k4_horizontal_strict_parameter_step
