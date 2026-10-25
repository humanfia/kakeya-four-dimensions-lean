-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.LipschitzCounting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.RobustTransversality
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.WeakPlaneMap

/-!
# Counting for the Lipschitz plane map (sticky Lemma 4.5)

At a point whose cones of width `β` contain at most half of the shading-tubes, at least half the
ordered pairs are transverse (`card_transPairs_ge`); with at most `B` tubes per fibre they give
at least `#pairs / B²` coarse label pairs (`card_transPairs_le`); and a covering-multiplicity
pigeonhole picks a heavy label pair on each cube (`exists_heavy_member`).
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- Transverse ordered pairs of shading-tubes at a point. -/
noncomputable def transPairs {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (β : ℝ)
    (p : Space) : Finset (Fin n × Fin n) := by
  classical exact (through Y p ×ˢ through Y p).filter fun ii => β < min ‖v ii.1 - v ii.2‖ ‖v ii.1 + v ii.2‖

/-- If every cone of width `β` through `p` contains at most half of the tubes through `p`, then at
least half of the ordered pairs of tubes through `p` are `β`-transverse. -/
theorem card_transPairs_ge {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (β : ℝ)
    (p : Space)
    (hcone : ∀ i ∈ through Y p, (((through Y p).filter fun l =>
      min ‖v l - v i‖ ‖v l + v i‖ ≤ β).card : ℝ) ≤ (through Y p).card / 2) :
    ((through Y p).card : ℝ) ^ 2 / 2 ≤ (transPairs Y v β p).card := by
  classical
  set s := through Y p with hs
  have hrow : ∀ i ∈ s, (s.card : ℝ) / 2 ≤ ((s.filter fun l => β < min ‖v i - v l‖ ‖v i + v l‖).card : ℝ) := by
    intro i hi
    have hsplit := s.card_filter_add_card_filter_not (fun l => β < min ‖v i - v l‖ ‖v i + v l‖)
    have hc := hcone i hi
    have heq : (s.filter fun l => ¬β < min ‖v i - v l‖ ‖v i + v l‖) =
        s.filter fun l => min ‖v l - v i‖ ‖v l + v i‖ ≤ β := by
      ext l
      simp only [Finset.mem_filter, not_lt]
      rw [norm_sub_rev (v i) (v l), add_comm (v i) (v l)]
    rw [heq] at hsplit
    have : ((s.filter fun l => β < min ‖v i - v l‖ ‖v i + v l‖).card : ℝ) +
        ((s.filter fun l => min ‖v l - v i‖ ‖v l + v i‖ ≤ β).card : ℝ) = s.card := by
      exact_mod_cast hsplit
    linarith
  have hcount : ((transPairs Y v β p).card : ℝ) =
      ∑ i ∈ s, ((s.filter fun l => β < min ‖v i - v l‖ ‖v i + v l‖).card : ℝ) := by
    unfold transPairs
    rw [← hs, Finset.card_filter, Finset.sum_product, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.card_filter]
  rw [hcount]
  calc ((s.card : ℝ)) ^ 2 / 2 = ∑ _i ∈ s, (s.card : ℝ) / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum hrow


/-- Coarse labels of the transverse pairs at a point. -/
noncomputable def coarsePairs {n k : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (β : ℝ)
    (a : Fin n → Fin k) (p : Space) : Finset (Fin k × Fin k) := by
  classical exact (transPairs Y v β p).image fun ii => (a ii.1, a ii.2)

/-- If each fibre has at most `B` tubes through `p`, the transverse pairs give at least
`#pairs / B²` coarse label pairs. -/
theorem card_transPairs_le {n k : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space) (β : ℝ)
    (a : Fin n → Fin k) (p : Space) (B : ℕ)
    (hB : ∀ j, ((through Y p).filter fun i => a i = j).card ≤ B) :
    (transPairs Y v β p).card ≤ B * B * (coarsePairs Y v β a p).card := by
  classical
  unfold coarsePairs
  apply Finset.card_le_mul_card_image
  rintro ⟨j, j'⟩ _
  calc ((transPairs Y v β p).filter fun ii => (a ii.1, a ii.2) = (j, j')).card
      ≤ (((through Y p).filter fun i => a i = j) ×ˢ ((through Y p).filter fun i => a i = j')).card := by
        apply Finset.card_le_card
        intro ii hii
        simp only [transPairs, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq] at hii ⊢
        exact ⟨⟨hii.1.1.1, hii.2.1⟩, hii.1.1.2, hii.2.2⟩
    _ = ((through Y p).filter fun i => a i = j).card *
          ((through Y p).filter fun i => a i = j').card := Finset.card_product _ _
    _ ≤ B * B := Nat.mul_le_mul (hB j) (hB j')


/-- Pigeonhole for covering multiplicity: if every point of `Q` lies in at least `L` of the
measurable sets `S π` (`π ∈ P`), one of them carries `L / #P` of the mass of `Q`. -/
theorem exists_heavy_member {ι : Type*} (ν : Measure Space) (Q : Set Space) (P : Finset ι)
    (hP : P.Nonempty) (S : ι → Set Space) (hS : ∀ π, MeasurableSet (S π)) (L : ℝ≥0∞)
    (hL : ∀ p ∈ Q, L ≤ ∑ π ∈ P, (S π).indicator 1 p) (hQ : MeasurableSet Q) :
    ∃ π ∈ P, L * ν Q ≤ P.card * ν (Q ∩ S π) := by
  classical
  have h1 : L * ν Q ≤ ∑ π ∈ P, ν (Q ∩ S π) := by
    calc L * ν Q = ∫⁻ p in Q, L ∂ν := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ p in Q, ∑ π ∈ P, (S π).indicator 1 p ∂ν := setLIntegral_mono'
          hQ fun p hp => hL p hp
      _ = ∑ π ∈ P, ∫⁻ p in Q, (S π).indicator 1 p ∂ν := by
          rw [lintegral_finsetSum _ fun π _ => measurable_one.indicator (hS π)]
      _ = ∑ π ∈ P, ν (Q ∩ S π) := by
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [lintegral_indicator_one (hS π), Measure.restrict_apply (hS π), inter_comm]
  obtain ⟨π, hπ, hmax⟩ := Finset.exists_max_image P (fun π => ν (Q ∩ S π)) hP
  refine ⟨π, hπ, h1.trans ?_⟩
  calc ∑ π ∈ P, ν (Q ∩ S π) ≤ ∑ _σ ∈ P, ν (Q ∩ S π) := Finset.sum_le_sum fun σ hσ => hmax σ hσ
    _ = P.card * ν (Q ∩ S π) := by rw [Finset.sum_const, nsmul_eq_mul]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
