-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.FamilyGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.FiberCover
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.WeightedSelection
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.IndexedMoment

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric
open scoped BigOperators

theorem fiber_gain_of_moment {I : Type*} [Fintype I] (F : Finset Plane)
    (T : I → Finset Plane) (f : I → Plane) {δ d K : ℝ} (hd : 0 < d)
    (hT : ∀ i, T i ⊆ F) (hne : ∃ i, (T i).Nonempty)
    (hdensity : d * (Fintype.card I : ℝ) * (F.card : ℝ) ≤ ∑ i, ((T i).card : ℝ))
    (hmoment : ∑ i, projectionEnergy F (f i) δ ≤
      K * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2) :
    ∃ i, ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun x => inner ℝ (f i) x) '' (↑(T i) : Set Plane)) cc →
      d ^ 2 ≤ K * (m : ℝ) := by
  classical
  obtain ⟨i₀, x, hx⟩ := hne
  have hIpos : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty I from ⟨i₀⟩)
  have hFpos : (0 : ℝ) < F.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, hT i₀ hx⟩
  let n (i : I) : ℝ := (T i).card
  let W : ℝ := ∑ i, (n i) ^ 2
  have hcauchy : (∑ i, n i) ^ 2 ≤ (Fintype.card I : ℝ) * W := by
    simpa only [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := n)
  have hsquare : (d * (Fintype.card I : ℝ) * (F.card : ℝ)) ^ 2 ≤ (∑ i, n i) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hdensity 2
  have hWlower : d ^ 2 * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2 ≤ W := by
    apply (mul_le_mul_iff_right₀ hIpos).mp
    calc (Fintype.card I : ℝ) * (d ^ 2 * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2) =
          (d * (Fintype.card I : ℝ) * (F.card : ℝ)) ^ 2 := by ring
      _ ≤ (∑ i, n i) ^ 2 := hsquare
      _ ≤ (Fintype.card I : ℝ) * W := hcauchy
  have hWpos : 0 < W := (by positivity : 0 < d ^ 2 * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2).trans_le hWlower
  obtain ⟨i, hi, hn, hselect⟩ := exists_weighted_ratio Finset.univ
    (fun i => projectionEnergy F (f i) δ) (fun i => (n i) ^ 2)
    (fun i _ => projectionEnergy_nonneg F (f i) δ) (fun i _ => sq_nonneg _) hWpos
  have hscale : 0 < (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2 := by positivity
  have hrow : projectionEnergy F (f i) δ * d ^ 2 ≤ K * (n i) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hscale).mp
    calc (projectionEnergy F (f i) δ * d ^ 2) * ((Fintype.card I : ℝ) * (F.card : ℝ) ^ 2) =
          projectionEnergy F (f i) δ * (d ^ 2 * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2) := by ring
      _ ≤ projectionEnergy F (f i) δ * W :=
        mul_le_mul_of_nonneg_left hWlower (projectionEnergy_nonneg F (f i) δ)
      _ ≤ (∑ j, projectionEnergy F (f j) δ) * (n i) ^ 2 := hselect
      _ ≤ (K * (Fintype.card I : ℝ) * (F.card : ℝ) ^ 2) * (n i) ^ 2 :=
        mul_le_mul_of_nonneg_right hmoment (sq_nonneg _)
      _ = (K * (n i) ^ 2) * ((Fintype.card I : ℝ) * (F.card : ℝ) ^ 2) := by ring
  refine ⟨i, ?_⟩
  intro m cc hc
  have hcover : (n i) ^ 2 ≤ (m : ℝ) * projectionEnergy F (f i) δ :=
    card_sq_le_cover_mul_projectionEnergy (hT i) (f i) δ hc
  apply (mul_le_mul_iff_left₀ hn).mp
  calc d ^ 2 * (n i) ^ 2 ≤ d ^ 2 * ((m : ℝ) * projectionEnergy F (f i) δ) :=
        mul_le_mul_of_nonneg_left hcover (sq_nonneg d)
    _ = (m : ℝ) * (projectionEnergy F (f i) δ * d ^ 2) := by ring
    _ ≤ (m : ℝ) * (K * (n i) ^ 2) := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg m)
    _ = (K * (m : ℝ)) * (n i) ^ 2 := by ring

theorem indexed_kaufman_energy_gain {I : Type*} [Fintype I] {f : I → Plane}
    {δ C d γ : ℝ} {F : Finset Plane} (T : I → Finset Plane)
    (hF : ClosedFiniteFrostman δ C F) (hf : IndexedFrostman δ C f)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hd : 0 < d)
    (hunit : ∀ i, ‖f i‖ = 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hT : ∀ i, T i ⊆ F) (hne : ∃ i, (T i).Nonempty)
    (hdensity : d * (Fintype.card I : ℝ) * (F.card : ℝ) ≤ ∑ i, ((T i).card : ℝ)) :
    ∃ i, ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers δ ((fun x => inner ℝ (f i) x) '' (↑(T i) : Set Plane)) cc →
      d ^ 2 ≤ (8 * C ^ 2 * energyConstant γ * δ ^ γ) * (m : ℝ) :=
  fiber_gain_of_moment F T f hd hT hne hdensity
    (sum_indexed_projectionEnergy_le hF hf hδ hδ1 hC hunit hγ hγ1)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
