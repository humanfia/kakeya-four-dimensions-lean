-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedProperties.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConcentratedProperties.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedState
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalNormalization
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.LocalizedFactorization

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

noncomputable section

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

theorem dimensions (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y) (hδ : 0 < δ) :
    0 < D.a ∧ 0 < ρ ∧ ρ ≤ 1 ∧ 0 < c ∧ c ≤ 1 := by
  have ha : 0 < D.a := hδ.trans_le D.grains.1
  have hrc : 0 < ρ * c := ha.trans_le D.grains.2.1
  have hc : 0 < c := hrc.trans_le D.grains.2.2.1
  refine ⟨ha, (mul_pos_iff_of_pos_right hc).mp hrc, ?_, hc, D.grains.2.2.2.1⟩
  nlinarith [D.grains.2.2.1]

/-- The balanced selection has strictly positive mass in each selected
grain, so all selected indices satisfy the natural-neighborhood condition. -/
theorem selected_mass_pos (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) : ∀ j ∈ D.Q, 0 < (μ (D.Hg j)).toReal := by
  obtain ⟨ha, hρ, -, hc, -⟩ := D.dimensions hδ
  obtain ⟨i₀, hi₀⟩ := D.selected_nonempty
  have hL : (0 : ℝ) < D.L := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i₀.isLt)
  obtain ⟨hfin, hweight, hmass⟩ := grain_real_weights hδ D.grains
  have hfull : 0 < ∑ j, (μ (D.Hg j)).toReal :=
    (by positivity : 0 < δ ^ (ε / 4) * D.L * (D.a * (ρ * c) * c)).trans_le hmass
  have hQfin : (∑ j ∈ D.Q, μ (D.Hg j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hfin j)
  have hkeep := ENNReal.toReal_mono hQfin D.retained
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
    ENNReal.toReal_sum (fun j _ => hfin j), ENNReal.toReal_sum (fun j _ => hfin j)] at hkeep
  have hsel : 0 < ∑ j ∈ D.Q, (μ (D.Hg j)).toReal :=
    (mul_pos (Real.rpow_pos_of_pos hδ _) hfull).trans_le hkeep
  obtain ⟨i, hi, hmi⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j (_ : j ∈ D.Q) => ENNReal.toReal_nonneg)).mp hsel
  intro j hj
  exact (mul_pos_iff_of_pos_left (Real.rpow_pos_of_pos hδ _)).mp
    (hmi.trans_le (D.balanced i hi j hj))

theorem selected_natural (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) :
    ∀ j ∈ D.Q, grainNear D.a ρ c D.z D.e (D.anchor (D.packet j)) j := by
  intro j hj
  apply D.natural j
  intro he
  have hm := D.selected_mass_pos hδ j hj
  simpa only [he, measure_empty, ENNReal.toReal_zero, lt_self_iff_false] using hm

/-- The half-cardinality guarantee for dense blocks retains grain mass
with only the previously quantified balance loss. -/
theorem retained_block_mass (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) (F : Finset (Finset (Fin D.L)))
    (hsub : ∀ R ∈ F, R ⊆ D.Q)
    (hcard : (D.Q.card : ℝ) ≤ 2 * (F.biUnion id).card) :
    O (δ ^ (ε / 80) / 2) * ∑ j ∈ D.Q, μ (D.Hg j) ≤
      ∑ j ∈ F.biUnion id, μ (D.Hg j) := by
  classical
  let R := F.biUnion id
  have hRQ : R ⊆ D.Q := by
    intro j hj
    obtain ⟨P, hP, hjP⟩ := Finset.mem_biUnion.mp hj
    exact hsub P hP hjP
  have hR : R.Nonempty := by
    have hQpos : (0 : ℝ) < D.Q.card := Nat.cast_pos.mpr (Finset.card_pos.mpr D.selected_nonempty)
    have hRpos : (0 : ℝ) < R.card := by
      change (D.Q.card : ℝ) ≤ 2 * R.card at hcard
      linarith
    exact Finset.card_pos.mp (Nat.cast_pos.mp hRpos)
  obtain ⟨hfin, -, -⟩ := grain_real_weights hδ D.grains
  have hs := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.comparable_mass_of_card_retention
    D.Q R (fun j => (μ (D.Hg j)).toReal) hR hRQ
    (Real.rpow_nonneg hδ.le (-(ε / 80))) (by norm_num : (0 : ℝ) ≤ 2)
    (fun _ _ => ENNReal.toReal_nonneg) D.balanced hcard
  have hQfin : (∑ j ∈ D.Q, μ (D.Hg j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hfin j)
  have hRfin : (∑ j ∈ R, μ (D.Hg j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hfin j)
  have hmass : (∑ j ∈ D.Q, μ (D.Hg j)) ≤
      O (δ ^ (-(ε / 80)) * 2) * ∑ j ∈ R, μ (D.Hg j) := by
    rw [← ENNReal.ofReal_toReal hQfin, ← ENNReal.ofReal_toReal hRfin,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [ENNReal.toReal_sum (fun j _ => hfin j)] using hs
  have hfactor : O (δ ^ (ε / 80) / 2) * O (δ ^ (-(ε / 80)) * 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have he : δ ^ (ε / 80) / 2 * (δ ^ (-(ε / 80)) * 2) = 1 := by
      calc
        _ = δ ^ (ε / 80) * δ ^ (-(ε / 80)) := by ring
        _ = 1 := by rw [← Real.rpow_add hδ]; simp
    rw [he, ENNReal.ofReal_one]
  calc
    _ ≤ O (δ ^ (ε / 80) / 2) *
        (O (δ ^ (-(ε / 80)) * 2) * ∑ j ∈ R, μ (D.Hg j)) :=
      mul_le_mul' le_rfl hmass
    _ = _ := by rw [← mul_assoc, hfactor, one_mul]

/-- The normalization can be applied to any injective subfamily of one
selected packet; its Jacobian does not depend on the packet. -/
theorem normalize_packet (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {k : ℕ} (ι : Fin k → Fin D.L) (t : Fin D.K)
    (hι : ∀ j, ι j ∈ D.Q) (ht : ∀ j, D.packet (ι j) = t) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (ρ / (64 * D.a * c ^ 2)) * μ W) ∧
      (∀ j, f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)) ⊆ Metric.ball (0 : V) 1) ∧
      (∀ j, Metric.ball (f (D.z (ι j))) (D.a / (8 * c)) ⊆
        f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j))) ∧
      (∀ j, ∃ u ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)),
        ∃ v ∈ f '' P D.a (ρ * c) c (D.z (ι j)) (D.e (ι j)), (1 / 4 : ℝ) ≤ dist u v) ∧
      (∀ u v, dist u v / (4 * c) ≤ dist (f u) (f v)) := by
  obtain ⟨ha, hρ, hρ1, hc, -⟩ := D.dimensions hδ
  apply natural_grain_normalization ha hρ hρ1 hc D.grains.2.1
    (D.z ∘ ι) (D.e ∘ ι) (D.z (D.anchor t)) (D.e (D.anchor t))
  intro j
  have hh := D.selected_natural hδ (ι j) (hι j)
  simpa only [grainNear, ht j, Function.comp_apply] using hh

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
