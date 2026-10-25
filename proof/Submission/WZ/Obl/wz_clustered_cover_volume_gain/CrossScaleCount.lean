-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.CrossScaleCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenRefinement
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.GroupedMultiplicity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseCore

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal

lemma supported_fine_count {n N : ℕ} {S : Finset (Fin n)} {Z : Fin n → Set V}
    (f : Fin n → Fin N) (hZ : ∀ i, i ∉ S → Z i = ∅) (k : Fin N) (p : V) :
    q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} = fiberBodyCount f Z k p := by
  rw [fiberBodyCount_eq_ncard]
  congr 1
  ext i
  constructor
  · exact fun hi => hi.2
  · intro hi
    refine ⟨?_, hi⟩
    by_contra hh
    have hp := hi.2
    simpa only [hZ i hh, mem_empty_iff_false] using hp

/-- The number of active parents in a coarse box multiplies the common
fine upper level to bound its fine incidence count. -/
theorem packet_count_of_medium {σ ω δ loss ρ b Cm M : ℝ} {n N J : ℕ}
    {Y Z W : Fin n → Set V} {S : Finset (Fin n)} {U : Finset (Fin N)}
    {f : Fin n → Fin N} {g : Fin N → Fin J}
    (hM : 0 ≤ M) (hMR : MR σ ω δ loss ρ b Cm n N J Y Z W S U f g)
    (hlevel : ∀ k p, p ∈ assignedFiber f Z k → fiberBodyCount f Z k p ≤ M) :
    ∀ p j, Parent.fiberMultiplicity (g ∘ f) W j p ≤
      O (M * (Cm * δ ^ (-loss) * (ρ / b) ^ (-ω - σ))) := by
  classical
  intro p j
  let Q := {k : Fin N | k ∈ U ∧ g k = j ∧ ∃ i ∈ S, f i = k ∧ p ∈ W i}
  have hsupport (i) (hi : p ∈ W i) : i ∈ S ∧ f i ∈ U := by
    constructor
    · by_contra hh
      simpa only [(hMR.1 i).2.2 (Or.inl hh), mem_empty_iff_false] using hi
    · by_contra hh
      simpa only [(hMR.1 i).2.2 (Or.inr hh), mem_empty_iff_false] using hi
  have hcount := Parent.Interfaces.assigned_count_le
    {i : Fin n | (g ∘ f) i = j ∧ p ∈ W i} Q f (M := M)
    (by intro i hi; exact ⟨(hsupport i hi.2).2, hi.1, i, (hsupport i hi.2).1, rfl, hi.2⟩)
    (by
      intro k hk
      obtain ⟨i, hiS, hik, hip⟩ := hk.2.2
      have hupper := hlevel k p ⟨i, hik, (hMR.1 i).2.1 hip⟩
      apply le_trans _ hupper
      rw [fiberBodyCount_eq_ncard]
      apply Nat.cast_le.mpr
      exact Set.ncard_le_ncard (fun i hi => ⟨hi.2, (hMR.1 i).2.1 hi.1.2⟩) (Set.toFinite _))
  have hreal : fiberBodyCount (g ∘ f) W j p ≤ M * (Cm * δ ^ (-loss) * (ρ / b) ^ (-ω - σ)) := by
    rw [fiberBodyCount_eq_ncard]
    exact hcount.trans (mul_le_mul_of_nonneg_left (hMR.2.2 p j) hM)
  have hform : Parent.fiberMultiplicity (g ∘ f) W j p =
      ∑ i, if (g ∘ f) i = j ∧ p ∈ W i then (1 : ℝ≥0∞) else 0 := by
    rw [Parent.fiberMultiplicity, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (g ∘ f) i = j <;> by_cases hp : p ∈ W i <;> simp [hi, hp]
  rw [hform]
  have he : (∑ i, if (g ∘ f) i = j ∧ p ∈ W i then (1 : ℝ≥0∞) else 0) =
      O (fiberBodyCount (g ∘ f) W j p) := by
    rw [fiberBodyCount_eq_ncard]
    simp only [O, ENNReal.ofReal_natCast, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
    congr 1
    simp only [Set.ncard_eq_toFinset_card']
    congr 1
    ext i
    simp
  rw [he]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The exact cancellation in the product of the fine packet, medium, and
coarse estimates, leaving only their errors and the richness gain. -/
lemma coarse_packet_product {δ ρ b n J σ ω Cf Cm Cc gain ef em ec : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hb : 0 < b) (hn : 0 < n) (hJ : 0 < J) :
    Cc * ((Cf * δ ^ (gain - ef) * (δ / ρ) ^ (-ω) * (n / J * δ * ρ / b ^ 2) ^ σ) *
      (Cm * δ ^ (-em) * (ρ / b) ^ (-ω - σ))) * δ ^ (-ec) * (b ^ (-ω) * (J * b) ^ σ) =
      Cf * Cm * Cc * δ ^ (-ω + (gain - ef - em - ec)) * (n * δ) ^ σ := by
  calc
    _ = (Cf * Cm * Cc) * (δ ^ (gain - ef) * δ ^ (-em) * δ ^ (-ec)) *
        (((δ / ρ) ^ (-ω) * (n / J * δ * ρ / b ^ 2) ^ σ) *
          (ρ / b) ^ (-ω - σ) * (b ^ (-ω) * (J * b) ^ σ)) := by ring
    _ = _ := by
      rw [Parent.three_scale_product hδ hρ hb hn hJ σ ω,
        ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      calc
        _ = (Cf * Cm * Cc) * (δ ^ (gain - ef + -em + -ec) * δ ^ (-ω)) * (n * δ) ^ σ := by ring
        _ = _ := by rw [← Real.rpow_add hδ]; congr 2; ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
