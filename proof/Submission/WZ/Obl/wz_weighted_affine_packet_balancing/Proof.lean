-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_weighted_affine_packet_balancing.Proof.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Parameters
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Refinement
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Transport

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_weighted_affine_packet_balancing

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

theorem main : ∀ e : ℝ, 0 < e → ∃ s : ℝ, 0 < s ∧ ∃ δ₀ : ℝ,
    0 < δ₀ ∧ δ₀ ≤ (1 / 100 : ℝ) ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Weighted δ (δ ^ s) n x v Y → Output e δ n x v Y := by
  classical
  intro e he
  obtain ⟨s, b, δ₀, hs, hb, hδ₀, hδ₀max, hparam⟩ := parameters e he
  refine ⟨s, hs, δ₀, hδ₀, hδ₀max, ?_⟩
  intro δ hδ hδsmall n x v Y hW
  obtain ⟨hhe, hR, hbins, hscale, hsmall⟩ := hparam δ hδ hδsmall
  let h : ℝ := δ ^ e
  let h₀ : ℝ := δ ^ s
  have hh : 0 < h := Real.rpow_pos_of_pos hδ _
  have hh₀ : 0 < h₀ := Real.rpow_pos_of_pos hδ _
  rcases hW with ⟨hn, hnpol, m, hm, ρ, hρ, hδρ, hρmax, M, f, D, z, w, Z, F,
    hM, hD, hJac, hw, hB, hsep, hZm, hZT, hZd, hF, hdisj, hinc, hmass, hslab, hvolume⟩
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hDpos (j : Fin m) : 0 < D j := (pow_pos hδ 100).trans_le (hD j).1
  have hfinite (j : Fin m) : volume (⋃ a, Z j a) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : Space)) (r := 1)).ne
      (measure_mono (Set.iUnion_subset fun a => (hZT j a).trans (hB j a)))
  let cost : Fin m → ℝ := fun j => (ENNReal.ofReal (D j) * volume (⋃ a, Z j a)).toReal
  let C : ℝ := ∑ j, cost j
  have hcost (j : Fin m) : 0 ≤ cost j := ENNReal.toReal_nonneg
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => hcost j
  have hcost_eq (j : Fin m) : ENNReal.ofReal (cost j) =
      ENNReal.ofReal (D j) * volume (⋃ a, Z j a) :=
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite j))
  have hCeq : ENNReal.ofReal C = ∑ j, ENNReal.ofReal (D j) * volume (⋃ a, Z j a) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hcost j)]
    exact Finset.sum_congr rfl (fun j _ => hcost_eq j)
  obtain ⟨j, hgood, hjC⟩ := good_cell hm
    (fun j => ∑ a, ((F j a).card : ℝ)) cost hcost (mul_pos hh₀ hn').le hmass
  obtain ⟨N, q, u, G, hN, hq, hu, hGF, hGcard, hGdisj, hbalance⟩ :=
    balanced_fibers (hM j) hb (F j) (hF j) (hdisj j) hR (hnpol.trans_lt hbins)
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hlocal : h * (∑ a, ((F j a).card : ℝ)) ≤ h₀ * (N : ℝ) * q := by
    calc
      _ ≤ h * ((b : ℝ) * δ ^ (-s) * N * q) := mul_le_mul_of_nonneg_left hbalance hh.le
      _ = (h * ((b : ℝ) * δ ^ (-s))) * (N : ℝ) * q := by ring
      _ ≤ h₀ * (N : ℝ) * q := by gcongr
  have hbudget : h * (n : ℝ) * cost j ≤ C * ((N : ℝ) * q) :=
    selected_budget hh.le hh₀ hC hgood (by simpa only [mul_assoc] using hlocal)
  obtain ⟨k, hk, hretained, hround⟩ := repetitions (mul_pos hh hn') (mul_pos hN' hq')
  have hcostbudget : h * h * (k : ℝ) * cost j ≤ C :=
    repeated_cost (mul_pos hN' hq') (hcost j) hC hjC hbudget hround hsmall
  have hradius : δ ^ (1 + e) ≤ ρ := by
    rw [Real.rpow_add hδ, Real.rpow_one]
    exact (mul_le_mul_of_nonneg_left hhe hδ.le).trans hδρ
  refine ⟨k, N, q, hk, hN, hq, ρ, h * D j, hradius, hρmax, mul_pos hh (hDpos j),
    (fun _ a => z j (u a)), (fun _ a => w j (u a)), (fun _ a => Z j (u a)), ?_, ?_, ?_⟩
  · refine ⟨(fun _ => G), (fun _ => f j), (fun _ => hGcard), (fun _ => hGdisj),
      ?_, ?_, ?_⟩
    · simpa only [mul_assoc] using hretained
    · intro _ a i hi
      exact hinc j (u a) i (hGF a hi)
    · intro _ Q _
      calc
        volume (f j '' Q ∩ Ball) ≤ volume (f j '' Q) := measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal (D j) * volume Q := hJac j Q
        _ = ENNReal.ofReal ((h * D j) / h) * volume Q := by
          congr 2
          field_simp
  · intro _
    constructor
    · refine ⟨hN, (fun a => hw j (u a)), (fun a => hB j (u a)),
        (fun a a' haa' => hsep j (u a) (u a') (fun heq => haa' (hu heq))),
        (fun a => hZm j (u a)), (fun a => hZT j (u a)), ?_⟩
      exact density_sum hh.le hhe _ (fun a => hZd j (u a))
    · exact slab_restrict hh hh₀ hq (z j) (w j) (F j) u G hGF hGcard hGdisj hlocal (hslab j)
  · have hsub : (⋃ a : Fin N, Z j (u a)) ⊆ ⋃ a, Z j a := by
      exact Set.iUnion_subset fun a => Set.subset_iUnion_of_subset (u a) Subset.rfl
    calc
      _ ≤ ENNReal.ofReal C := transport_repetitions hh.le hsub (hcost_eq j) hcostbudget
      _ ≤ volume (⋃ i, Y i) := by rw [hCeq]; exact hvolume

end WangZahlLot.Obl.wz_weighted_affine_packet_balancing
