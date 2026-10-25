-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SecondFilling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SecondFilling.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 commit be976b9, SecondFilling.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CutDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- Simultaneous second filling for a finite family of angular pieces.
The packet angle may vary with the label. One aggregate row budget gives
half-mass retention, relative incidence counts, and density in every
occupied enclosing set. -/
theorem cordoba_family_filling {κ : Type*} [Fintype κ] {n : ℕ}
    {d L β : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 100) (hL : 2 * d ≤ L)
    (θ r mass lam vol : κ → ℝ) (hθ : ∀ k, 0 < θ k)
    (hr : ∀ k, d ≤ r k ∧ r k ≤ 1) (hmass : ∀ k, 0 ≤ mass k)
    (hlam : ∀ k, 0 ≤ lam k)
    (x v : κ → Fin n → V) (hv : ∀ k i, ‖v k i‖ = 1)
    (Y : κ → Fin n → Set V) (hYm : ∀ k i, MeasurableSet (Y k i))
    (hYT : ∀ k i, Y k i ⊆ T d (x k i) (v k i))
    (z : κ → V) (hball : ∀ k i, Y k i ⊆ ball (z k) (L / 2))
    (U : κ → Set V) (hYU : ∀ k i, Y k i ⊆ U k)
    (hUvol : ∀ k, μ (U k) ≤ O (vol k))
    (hBr : ∀ k p u s, d ≤ s →
      q n {i | p ∈ Y k i ∧ pd (v k i) u ≤ s} ≤
        2 * (s / θ k) ^ β * q n {i | p ∈ Y k i})
    (cost : κ → Fin n → ENNReal)
    (hcost : ∀ k i, (Y k i).Nonempty → O (mass k) ≤ cost k i)
    (hbudget : (∑ k, ∑ i, cost k i) ≤ (1 / 4 : ENNReal) * ∑ k, ∑ i, μ (Y k i))
    (hangle : ∀ k, 8 * (r k / θ k) ^ β < 1)
    (hnum : ∀ k, (1000000000 * L * d ^ 5 * (1 + Real.log (1 / d))) *
      (lam k * vol k) ≤ (mass k) ^ 3 * r k) :
    ∃ Z : κ → Fin n → Set V,
      (∀ k i, MeasurableSet (Z k i) ∧ Z k i ⊆ Y k i) ∧
      (∀ k i, Z k i ⊆ U k) ∧
      (1 / 2 : ENNReal) * (∑ k, ∑ i, μ (Y k i)) ≤ ∑ k, ∑ i, μ (Z k i) ∧
      (∀ k i, (Z k i).Nonempty → O (mass k) ≤ μ (Z k i)) ∧
      (∀ k p, p ∈ ⋃ i, Z k i → q n {i | p ∈ Y k i} ≤ 4 * q n {i | p ∈ Z k i}) ∧
      (∀ k p u s, d ≤ s →
        q n {i | p ∈ Z k i ∧ pd (v k i) u ≤ s} ≤
          8 * (s / θ k) ^ β * q n {i | p ∈ Z k i}) ∧
      ∀ k, (⋃ i, Z k i).Nonempty → O (lam k) * μ (U k) ≤ μ (⋃ i, Z k i) := by
  classical
  have hYfin (k : κ) (i : Fin n) : μ (Y k i) ≠ ⊤ :=
    measure_ne_top_of_subset (hball k i) (measure_ball_lt_top (μ := volume)).ne
  obtain ⟨Z, hZ, hsum, hrows, hcounts⟩ :=
    WangZahlLot.Obl.wz_move_two_dense_broad_prisms.relative_shading_core_family
      volume Y hYm hYfin cost (1 / 4)
  have hhalf : (1 / 4 : ENNReal) + 1 / 4 = 1 / 2 := by
    have hq : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [← hq, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    rw [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num,
      ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hkeep : (1 / 2 : ENNReal) * (∑ k, ∑ i, μ (Y k i)) ≤
      ∑ k, ∑ i, μ (Z k i) := by
    apply WangZahlLot.Obl.wz_clustered_cover_volume_gain.half_mass_after_loss
      (ENNReal.sum_ne_top.mpr (fun k _ => ENNReal.sum_ne_top.mpr (fun i _ => hYfin k i)))
      (by simpa only [add_assoc] using hsum)
    calc
      _ ≤ (1 / 4 : ENNReal) * (∑ k, ∑ i, μ (Y k i)) +
          (1 / 4 : ENNReal) * (∑ k, ∑ i, μ (Y k i)) := add_le_add hbudget le_rfl
      _ = _ := by rw [← add_mul, hhalf]
  have hmassZ (k : κ) (i : Fin n) (hi : (Z k i).Nonempty) :
      O (mass k) ≤ μ (Z k i) := (hcost k i (hi.mono (hZ k i).2)).trans (hrows k i hi)
  have hcount (k : κ) (p : V) (hp : p ∈ ⋃ i, Z k i) :
      q n {i | p ∈ Y k i} ≤ 4 * q n {i | p ∈ Z k i} := by
    have hh := ENNReal.toReal_mono (by simp) (hcounts k p hp)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at hh
    change ({i | p ∈ Y k i}.ncard : ℝ) ≤ 4 * ({i | p ∈ Z k i}.ncard : ℝ)
    linarith
  have hBrZ (k : κ) (p u : V) (s : ℝ) (hs : d ≤ s) :
      q n {i | p ∈ Z k i ∧ pd (v k i) u ≤ s} ≤
        8 * (s / θ k) ^ β * q n {i | p ∈ Z k i} := by
    by_cases hp : p ∈ ⋃ i, Z k i
    · have hcap : q n {i | p ∈ Z k i ∧ pd (v k i) u ≤ s} ≤
          q n {i | p ∈ Y k i ∧ pd (v k i) u ≤ s} :=
        Nat.cast_le.mpr (Set.ncard_le_ncard
          (fun i hi => ⟨(hZ k i).2 hi.1, hi.2⟩) (Set.toFinite _))
      calc
        _ ≤ 2 * (s / θ k) ^ β * q n {i | p ∈ Y k i} := hcap.trans (hBr k p u s hs)
        _ ≤ 2 * (s / θ k) ^ β * (4 * q n {i | p ∈ Z k i}) :=
          mul_le_mul_of_nonneg_left (hcount k p hp)
            (by have hs0 := hd.trans_le hs; have hk := hθ k; positivity)
        _ = _ := by ring
    · have he : {i | p ∈ Z k i ∧ pd (v k i) u ≤ s} = ∅ := by
        ext i
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hi => (hp (mem_iUnion.mpr ⟨i, hi⟩)).elim
      rw [show q n {i | p ∈ Z k i ∧ pd (v k i) u ≤ s} = 0 by simp only [q, he, ncard_empty, Nat.cast_zero]]
      have hs0 := hd.trans_le hs
      have hk := hθ k
      positivity
  refine ⟨Z, hZ, fun k i => (hZ k i).2.trans (hYU k i), hkeep,
    hmassZ, hcount, hBrZ, ?_⟩
  intro k hne
  obtain ⟨i₀, hi₀⟩ := nonempty_iUnion.mp hne
  have hn : 0 < n := i₀.pos
  have hcor := WangZahlLot.Obl.wz_move_two_dense_broad_prisms.broad_packet_cut_mass
    hn hd hd1 (hd.trans_le (hr k).1) (hr k).2 hL (hmass k)
    (x k) (v k) (hv k) (Z k) (fun i => (hZ k i).1)
    (fun i => (hZ k i).2.trans (hYT k i)) (z k)
    (fun i => (hZ k i).2.trans (hball k i)) (hmassZ k) i₀ hi₀ (hangle k)
    (fun p _ => hBrZ k p (v k i₀) (r k) (hr k).1)
    Set.univ MeasurableSet.univ (fun _ _ => subset_univ _)
  simp only [inter_univ] at hcor
  have hlog : 0 < 1 + Real.log (1 / d) := by
    have hh : 1 ≤ 1 / d := (le_div_iff₀ hd).mpr (by linarith)
    linarith [Real.log_nonneg hh]
  have hcoef : 0 < 1000000000 * L * d ^ 5 * (1 + Real.log (1 / d)) := by
    have hL0 : 0 < L := by linarith
    positivity
  have hreal : lam k * vol k ≤ volume.real (⋃ i, Z k i) :=
    (mul_le_mul_iff_right₀ hcoef).mp ((hnum k).trans hcor)
  have hZfin : μ (⋃ i, Z k i) ≠ ⊤ :=
    measure_ne_top_of_subset (iUnion_subset fun i => (hZ k i).2.trans (hball k i))
      (measure_ball_lt_top (μ := volume)).ne
  calc
    _ ≤ O (lam k) * O (vol k) := mul_le_mul' le_rfl (hUvol k)
    _ = O (lam k * vol k) := by
      dsimp only [O]
      rw [ENNReal.ofReal_mul (hlam k)]
    _ ≤ _ := (ENNReal.ofReal_le_iff_le_toReal hZfin).mpr hreal

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
