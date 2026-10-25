import Submission.Obl.k4_native_calibrated_homogeneous_remainder.Models
import Submission.Obl.k4_dyadic_crop_worlds.Assembly
import Submission.Obl.k4_finite_width_output_exclusion.Subsequence

/-! Restrict the full list of worlds and normalize its weights, keeping the full
conditioned prior and the same incidence set in every retained world. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_dyadic_crop_worlds (sum_equivFin)

noncomputable def keptWeightSum (p : Data) (S : (k : ℕ) → Finset (Fin (p.W k))) (k : ℕ) : ℝ :=
  ∑ b ∈ S k, p.ω k b

noncomputable def keptWorldIndex {W : ℕ} (S : Finset (Fin W)) (b : Fin S.card) : Fin W :=
  (S.equivFin.symm b).1

noncomputable def keepWorlds (p : Data) (S : (k : ℕ) → Finset (Fin (p.W k)))
    (K' : ℕ → ℝ) : Data :=
  { p with
    K := K'
    W := fun k => (S k).card
    ω := fun k b => p.ω k (keptWorldIndex (S k) b) / keptWeightSum p S k
    ν := fun k b => p.ν k (keptWorldIndex (S k) b)
    E := fun k b => p.E k (keptWorldIndex (S k) b)
    P := fun k b => p.P k (keptWorldIndex (S k) b)
    B := fun k b => p.B k (keptWorldIndex (S k) b)
    g := fun k b => p.g k (keptWorldIndex (S k) b)
    G := fun k b => p.G k (keptWorldIndex (S k) b) }

/-- Full-world restriction preserves the raw native predicate. Its selected
mass lower bound may use any enlarged subpower slack. -/
theorem RawValid.keep_worlds {p : Data} (hp : RawValid p)
    (S : (k : ℕ) → Finset (Fin (p.W k))) (K' : ℕ → ℝ)
    (hK' : (∀ k, 1 ≤ K' k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K' k ≤ p.N k ^ ε)
    (hKK' : ∀ k, p.K k ≤ K' k)
    (hretain : ∀ k, ENNReal.ofReal ((K' k)⁻¹) ≤
      ∑ b ∈ S k, ENNReal.ofReal (p.ω k b) * selected p k b univ) :
    RawValid (keepWorlds p S K') ∧
      ∀ k, 0 < keptWeightSum p S k ∧ keptWeightSum p S k ≤ 1 := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, M, D, hfmt⟩
  have hnorm : ∀ k, 0 < keptWeightSum p S k ∧ keptWeightSum p S k ≤ 1 := by
    intro k
    have hω : ∀ b, 0 ≤ p.ω k b := (hfmt k).2.1
    have hsum : ∑ b, p.ω k b = 1 := (hfmt k).2.2.1
    have ht0 : 0 ≤ keptWeightSum p S k := Finset.sum_nonneg (fun b _ => hω b)
    have ht1 : keptWeightSum p S k ≤ 1 := by
      calc
        _ ≤ ∑ b, p.ω k b := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ (S k)) (fun b _ _ => hω b)
        _ = 1 := hsum
    have hm : ∀ b, selected p k b univ ≤ 1 := by
      intro b
      have hw := (hfmt k).2.2.2.1 b
      have : IsProbabilityMeasure (p.ν k b) := hw.1
      change ((p.ν k b).prod volume).restrict (p.E k b) univ ≤ 1
      rw [Measure.restrict_apply_univ]
      exact Submission.Obl.k4_dyadic_crop_worlds.selected_le_one hw.2.2.2.2.2.2.2.2.1
    have hwgt : (∑ b ∈ S k, ENNReal.ofReal (p.ω k b) * selected p k b univ) ≤
        ENNReal.ofReal (keptWeightSum p S k) := by
      calc
        _ ≤ ∑ b ∈ S k, ENNReal.ofReal (p.ω k b) := by
          exact Finset.sum_le_sum fun b _ => by simpa using mul_le_mul' le_rfl (hm b)
        _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun b _ => hω b)).symm
    have ht : 0 < keptWeightSum p S k := by
      by_contra hn
      have hz : keptWeightSum p S k = 0 := le_antisymm (le_of_not_gt hn) ht0
      have hpos : 0 < ENNReal.ofReal ((K' k)⁻¹) := by
        apply ENNReal.ofReal_pos.mpr
        exact inv_pos.mpr (by linarith [hK'.1 k])
      have hh := (hretain k).trans hwgt
      rw [hz, ENNReal.ofReal_zero] at hh
      exact (not_le_of_gt hpos) hh
    exact ⟨ht, ht1⟩
  refine ⟨?_, hnorm⟩
  refine ⟨hN, hNt, hK', hL, hd, hd1, hS, hη, M, D, fun k => ?_⟩
  have ht : 0 < keptWeightSum p S k := (hnorm k).1
  have hω : ∀ b, 0 ≤ p.ω k b := (hfmt k).2.1
  have hK0 : 0 < p.K k := by linarith [hK.1 k]
  have hK'0 : 0 < K' k := by linarith [hK'.1 k]
  refine ⟨?_, (fun b => div_nonneg (hω _) ht.le), ?_, ?_, ?_⟩
  · have hc : ((S k).card : ℝ) ≤ (p.W k : ℝ) := by
      exact_mod_cast (show (S k).card ≤ p.W k by
        simpa using Finset.card_le_card (Finset.subset_univ (S k)))
    exact hc.trans (hfmt k).1
  · change (∑ b : Fin (S k).card,
      p.ω k (keptWorldIndex (S k) b) / keptWeightSum p S k) = 1
    rw [← Finset.sum_div]
    change (∑ b : Fin (S k).card,
      p.ω k ((S k).equivFin.symm b).1) / keptWeightSum p S k = 1
    rw [sum_equivFin]
    exact div_self ht.ne'
  · intro b
    let b₀ := keptWorldIndex (S k) b
    rcases (hfmt k).2.2.2.1 b₀ with
      ⟨hν, hB, hBle, hBi, hP, hc, hprior, hEm, hEt, hEb, hEf, hnat, hlow⟩
    refine ⟨hν, hB, hBle, hBi, hP, hc, hprior, hEm, hEt, hEb, hEf, ?_, ?_⟩
    · filter_upwards [hnat] with l hl t ht
      obtain ⟨hy, hpv, hpd, hpdd⟩ := hl t ht
      exact ⟨hy.trans (hKK' k), hpv.trans (hKK' k),
        hpd.trans (mul_le_mul_of_nonneg_right (hKK' k) hB.le),
        hpdd.trans (mul_le_mul_of_nonneg_right (hKK' k) (sq_nonneg _))⟩
    · filter_upwards [hlow] with z hz
      exact (div_le_div_of_nonneg_left hB.le hK0 (hKK' k)).trans hz
  · change ENNReal.ofReal ((K' k)⁻¹) ≤
      ∑ b : Fin (S k).card,
        ENNReal.ofReal (p.ω k ((S k).equivFin.symm b).1 / keptWeightSum p S k) *
          selected p k ((S k).equivFin.symm b).1 univ
    rw [sum_equivFin (S k) (fun b =>
      ENNReal.ofReal (p.ω k b / keptWeightSum p S k) * selected p k b univ)]
    have heq : ∀ b, ENNReal.ofReal (p.ω k b / keptWeightSum p S k) =
        ENNReal.ofReal ((keptWeightSum p S k)⁻¹) * ENNReal.ofReal (p.ω k b) := by
      intro b
      rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
    simp_rw [heq, mul_assoc]
    rw [← Finset.mul_sum]
    refine (hretain k).trans ?_
    have hti : 1 ≤ (keptWeightSum p S k)⁻¹ := by
      rw [← one_div, le_div_iff₀ ht]
      simpa using (hnorm k).2
    have hti' : (1 : ENNReal) ≤ ENNReal.ofReal ((keptWeightSum p S k)⁻¹) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hti
    simpa only [one_mul] using mul_le_mul' hti' (le_refl
      (∑ b ∈ S k, ENNReal.ofReal (p.ω k b) * selected p k b univ))


/-- The raw predicate is stable under a cofinal subsequence. -/
theorem RawValid.reindex {p : Data} (hp : RawValid p) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) : RawValid (p.reindex ψ) := by
  rcases hp with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, M, D, hfmt⟩
  refine ⟨(fun k => hN (ψ k)), hNt.comp hψ,
    ⟨(fun k => hK.1 (ψ k)), ?_⟩, hL, hd, hd1, hS, hη, M, D, fun k => hfmt (ψ k)⟩
  intro ε hε
  exact hψ.eventually (hK.2 ε hε)

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
