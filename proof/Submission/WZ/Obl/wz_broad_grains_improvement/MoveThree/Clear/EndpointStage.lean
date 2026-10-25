-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.EndpointStage.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/EndpointStage.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.FibreEnds
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.TwoLevel
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.RefinementStage

/-!
Ported (namespace and imports adjusted) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/EndpointStage.lean`, branch x0641 of the o169
repository (sessions x0551/x0556/x0587/x0641/x0661/x0670; workspace code, not accepted).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber fiberBodyCount fiberBodyCount_eq_ncard supported_fine_count
    assignedFiber_eq_supported assignedFiber_mono assignedFiber_common_cut fiberBodyCount_restrict)
open WangZahlLot.Obl.wz_coarse_tube_grains.RIS (tubeEnds)

/-- The full stage can be trimmed away from all fine tube ends, retaining a
quarter of the fine mass and preserving the given grain boxes. -/
theorem endpoint_clear_stage_data {ω ζ δ h ε ρ a c b g : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hhε : h ≤ ε)
    (hA : A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y)
    (hC : C δ h n x v Y S Z ρ N y w f True)
    (hbr : Broad ω ζ δ h ρ n N v S Z f)
    (hH : H δ h n x v S Z ρ N y w f a c b g)
    (hc : c ≤ 1 / 2) (hendbudget : 5120 * c ≤ δ ^ (2 * h))
    (hmassbudget : δ ^ ε ≤ (1 / 8) * δ ^ h)
    (hbrbudget : 2 * δ ^ (-h) ≤ δ ^ (-ε)) :
    ∃ W : Fin n → Set V,
      (∀ i, W i ⊆ Z i ∧ Disjoint (W i) (tubeEnds δ c (x i) (v i))) ∧
      O (1 / 4) * ∑ i, μ (Z i) ≤ ∑ i, μ (W i) ∧
      C δ ε n x v Y S W ρ N y w f True ∧
      Broad ω ζ δ ε ρ n N v S W f ∧
      H δ ε n x v S W ρ N y w f a c b g := by
  obtain ⟨L, z, e, Hs, γ, m, hHB⟩ := H_iff.mp hH
  have hsupport : ∀ i, i ∉ S → Z i = ∅ := fun i => (hC.1 i).2.2
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hC.1 i).1
  have hδc : δ ≤ c := hHB.1.trans (hHB.2.1.trans hHB.2.2.1)
  have hdense : O (δ ^ (2 * h) * n * δ ^ 2) ≤ ∑ i, μ (Z i) := by
    calc
      O (δ ^ (2 * h) * n * δ ^ 2) = O (δ ^ h) * O (δ ^ h * n * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show 2 * h = h + h by ring, Real.rpow_add hδ]
        ring
      _ ≤ O (δ ^ h) * ∑ i, μ (Y i) := mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := hC.2.1.trans_eq (sum_supported hsupport)
  have hfin : (∑ i, μ (Z i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ =>
    ne_top_of_le_ne_top (measure_ball_lt_top (μ := volume) (x := (0 : V)) (r := 1)).ne
      (measure_mono ((hC.1 i).2.1.trans ((hA.2.1 i).2.2.2.trans (hA.2.1 i).2.1)))
  have hlevelZ : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
    intro k p hp
    rw [assignedFiber_eq_supported f hsupport] at hp
    rw [← supported_fine_count f hsupport]
    exact hHB.2.2.2.2.2.2.2.2.1 k p hp
  have hm : 0 < m := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
    have hZpos : 0 < ∑ i, μ (Z i) := (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hdense
    obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
      (f := fun _ => (0 : ENNReal)) (g := fun i => μ (Z i)) (by simpa using hZpos)
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hi.ne'
    have hh := (hlevelZ (f i) p ⟨i, rfl, hp⟩).2
    have hpos : 0 < fiberBodyCount f Z (f i) p := by
      rw [fiberBodyCount_eq_ncard]
      exact Nat.cast_pos.mpr ((Set.ncard_pos (Set.toFinite _)).mpr ⟨i, rfl, hp⟩)
    linarith
  obtain ⟨U, hU, hmassU, hfracU⟩ := trim_fibre_endpoints x v Z f hδ hδc hc
    (fun i => (hA.2.1 i).1) hZm hfin hdense hendbudget
  have hUoff : ∀ i, i ∉ S → U i = ∅ := fun i hi =>
    subset_empty_iff.mp ((hU i).2.1.trans (by rw [hsupport i hi]))
  have hlevelU : ∀ k p, p ∈ assignedFiber f U k →
      m / 2 ≤ fiberBodyCount f U k p ∧ fiberBodyCount f U k p ≤ 2 * m := by
    intro k p hp
    have hz := hlevelZ k p (assignedFiber_mono f (fun i => (hU i).2.1) k hp)
    have hfrac : fiberBodyCount f Z k p ≤ 2 * fiberBodyCount f U k p := by
      simpa only [fiberBodyCount_eq_ncard, q] using hfracU k p hp
    have hle : fiberBodyCount f U k p ≤ fiberBodyCount f Z k p := by
      rw [fiberBodyCount_eq_ncard, fiberBodyCount_eq_ncard]
      exact Nat.cast_le.mpr (Set.ncard_mono fun i hi => ⟨hi.1, (hU i).2.1 hi.2⟩)
    constructor <;> linarith
  obtain ⟨m', D, hm', hm'm, hD, hmassD, hlevelD⟩ :=
    two_level_fibre_cut f U hm (fun i => (hU i).1) hlevelU
  let W i := U i ∩ D (f i)
  have hWm i : MeasurableSet (W i) := (hU i).1.inter (hD (f i))
  have hWZ i : W i ⊆ Z i := inter_subset_left.trans (hU i).2.1
  have hWoff : ∀ i, i ∉ S → W i = ∅ := fun i hi =>
    subset_empty_iff.mp ((hWZ i).trans (by rw [hsupport i hi]))
  have hmassW : O (1 / 4) * ∑ i, μ (Z i) ≤ ∑ i, μ (W i) := by
    calc
      O (1 / 4) * ∑ i, μ (Z i) = O (1 / 2) * (O (1 / 2) * ∑ i, μ (Z i)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ O (1 / 2) * ∑ i, μ (U i) := mul_le_mul' le_rfl hmassU
      _ ≤ _ := hmassD
  have hfracW : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} ≤
        2 * q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} := by
    intro k p hp
    have hpW : p ∈ assignedFiber f W k := (assignedFiber_eq_supported f hWoff k).symm ▸ hp
    have hp' : p ∈ assignedFiber f U k ∩ D k := by
      change p ∈ assignedFiber f (fun i => U i ∩ D (f i)) k at hpW
      rwa [assignedFiber_common_cut] at hpW
    rw [show q n {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} = fiberBodyCount f Z k p from
      supported_fine_count f hsupport k p,
      show q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} = fiberBodyCount f W k p from
      supported_fine_count f hWoff k p]
    change fiberBodyCount f Z k p ≤ 2 * fiberBodyCount f (fun i => U i ∩ D (f i)) k p
    rw [fiberBodyCount_restrict, indicator_of_mem hp'.2]
    simpa only [fiberBodyCount_eq_ncard, q] using hfracU k p hp'.1
  have hlevelW : ∀ k p, (∃ i ∈ S, f i = k ∧ p ∈ W i) →
      q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} ∈ Icc m' (2 * m') := by
    intro k p hp
    rw [show q n {i | i ∈ S ∧ f i = k ∧ p ∈ W i} = fiberBodyCount f W k p from
      supported_fine_count f hWoff k p]
    exact hlevelD k p ((assignedFiber_eq_supported f hWoff k).symm ▸ hp)
  refine ⟨W, fun i => ⟨hWZ i, (hU i).2.2.mono_left inter_subset_left⟩, hmassW, ?_⟩
  exact shading_refine_stage_data hδ hδ1 hρ hhε hm (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hC hbr hHB hWm hWZ hmassW (by convert hmassbudget using 1 <;> norm_num)
    hfracW hbrbudget hlevelW

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
