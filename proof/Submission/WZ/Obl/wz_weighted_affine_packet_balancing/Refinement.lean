-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_weighted_affine_packet_balancing.Refinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Basic
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Finite
import Submission.WZ.Obl.wz_affine_packet_counting_transfer.Basic

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_weighted_affine_packet_balancing

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Restrict and truncate disjoint nonempty fibers to a common cardinality. -/
theorem balanced_fibers {n M b : ℕ} (hM : 0 < M) (hb : 0 < b)
    (F : Fin M → Finset (Fin n)) (hF : ∀ a, (F a).Nonempty)
    (hdisj : ∀ a a', a ≠ a' → Disjoint (F a) (F a'))
    {R : ℝ} (hR : 1 < R) (hn : (n : ℝ) < R ^ b) :
    ∃ (N q : ℕ) (u : Fin N → Fin M) (G : Fin N → Finset (Fin n)),
      0 < N ∧ 0 < q ∧ Function.Injective u ∧ (∀ a, G a ⊆ F (u a)) ∧
      (∀ a, (G a).card = q) ∧ (∀ a a', a ≠ a' → Disjoint (G a) (G a')) ∧
      (∑ a, ((F a).card : ℝ)) ≤ (b : ℝ) * R * N * q := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨N, q, u, hN, hq, hu, hqu, hmass⟩ := uniform_selection
    (fun a => (F a).card) (fun a => Finset.card_pos.mpr (hF a)) hb
    (fun a => by simpa using (F a).card_le_univ) hR hn
  choose G hGF hGcard using fun a => Finset.exists_subset_card_eq (hqu a)
  refine ⟨N, q, u, G, hN, hq, hu, hGF, hGcard, ?_, hmass⟩
  intro a a' haa'
  exact (hdisj _ _ (fun h => haa' (hu h))).mono (hGF a) (hGF a')

/-- Weighted slab counts pass to the truncated family. -/
theorem slab_restrict {n M N q : ℕ} {ρ h h₀ mass : ℝ}
    (hh : 0 < h) (hh₀ : 0 < h₀) (hq : 0 < q)
    (z w : Fin M → Space) (F : Fin M → Finset (Fin n))
    (u : Fin N → Fin M) (G : Fin N → Finset (Fin n))
    (hGF : ∀ a, G a ⊆ F (u a)) (hcard : ∀ a, (G a).card = q)
    (hdisj : ∀ a a', a ≠ a' → Disjoint (G a) (G a'))
    (hlocal : h * mass ≤ h₀ * (N : ℝ) * q)
    (hslab : ∀ (ν : Space) (s r : ℝ), ‖ν‖ = 1 → 0 < r →
      ENNReal.ofReal (Set.ncard {i : Fin n | ∃ a : Fin M, i ∈ F a ∧
        Tube ρ (z a) (w a) ⊆ (Ball ∩ {p | |inner ℝ ν p - s| ≤ r})} : ℝ) ≤
      ENNReal.ofReal (h₀⁻¹ * mass) * volume (Ball ∩ {p | |inner ℝ ν p - s| ≤ r})) :
    SlabCount ρ h⁻¹ N (z ∘ u) (w ∘ u) := by
  intro ν s r hν hr
  let Q : Set Space := Ball ∩ {p | |inner ℝ ν p - s| ≤ r}
  let S : Set (Fin N) := {a | Tube ρ (z (u a)) (w (u a)) ⊆ Q}
  let A : Set (Fin n) := {i | ∃ a, i ∈ F a ∧ Tube ρ (z a) (w a) ⊆ Q}
  have hc : S.ncard * q ≤ A.ncard :=
    WangZahlLot.Obl.wz_affine_packet_counting_transfer.fiber_count G hcard hdisj S A
      (fun a ha i hi => ⟨u a, hGF a hi, ha⟩)
  have hc' : (S.ncard : ℝ) * (q : ℝ) ≤ (A.ncard : ℝ) := by exact_mod_cast hc
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hcount : ENNReal.ofReal ((S.ncard : ℝ) * (q : ℝ)) ≤
      ENNReal.ofReal (h₀⁻¹ * mass) * volume Q :=
    (ENNReal.ofReal_le_ofReal hc').trans (hslab ν s r hν hr)
  have hcoeff : (q : ℝ)⁻¹ * (h₀⁻¹ * mass) ≤ h⁻¹ * (N : ℝ) := by
    have he : (q : ℝ)⁻¹ * (h₀⁻¹ * mass) = mass / ((q : ℝ) * h₀) := by ring
    rw [he, inv_mul_eq_div]
    apply (div_le_div_iff₀ (mul_pos hq' hh₀) hh).mpr
    nlinarith [hlocal]
  change ENNReal.ofReal (S.ncard : ℝ) ≤ ENNReal.ofReal (h⁻¹ * (N : ℝ)) * volume Q
  calc
    _ = ENNReal.ofReal ((q : ℝ)⁻¹) * ENNReal.ofReal ((S.ncard : ℝ) * q) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal ((q : ℝ)⁻¹) * (ENNReal.ofReal (h₀⁻¹ * mass) * volume Q) :=
      mul_le_mul' le_rfl hcount
    _ = ENNReal.ofReal ((q : ℝ)⁻¹ * (h₀⁻¹ * mass)) * volume Q := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl

/-- Pointwise shading density yields the required summed density after restriction. -/
theorem density_sum {N : ℕ} {h h₀ ρ : ℝ} (_hh : 0 ≤ h) (hle : h ≤ h₀)
    (Z : Fin N → Set Space) (hZ : ∀ a, ENNReal.ofReal (h₀ * ρ ^ 2) ≤ volume (Z a)) :
    ENNReal.ofReal (h * (N : ℝ) * ρ ^ 2) ≤ ∑ a, volume (Z a) := by
  calc
    _ = ∑ _a : Fin N, ENNReal.ofReal (h * ρ ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      congr 1
      ring
    _ ≤ ∑ a, volume (Z a) := Finset.sum_le_sum fun a _ =>
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (sq_nonneg ρ))).trans (hZ a)

end WangZahlLot.Obl.wz_weighted_affine_packet_balancing
