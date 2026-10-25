-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseEstimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseNormalize
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.PointwiseEstimate

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces

open MeasureTheory Set

noncomputable section

/-- E applies to the actual coarse shadings once their uniform density reaches its
threshold. All normalization and separation losses are included explicitly. -/
theorem factored_coarse_estimate {σ ω : ℝ} (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ κ ηE : ℝ, 0 < κ ∧ 0 < ηE ∧
    ∀ {δ η h ρ K m a b D H : ℝ} {n N L : ℕ}
      {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
      {y w : Fin N → V} {f : Fin n → Fin N} {U : Finset (Fin N)}
      {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {g : Fin N → Fin L},
      0 < δ → δ ≤ 1 → δ ≤ ρ → 0 ≤ h → 0 ≤ η → 1 ≤ K → 1 ≤ D → b ≤ 1 / 3 →
      U.Nonempty → A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y → C δ h n x v Y S Z ρ N y w f →
      Factor.AssignedCover 4 ρ K y w U m a b L z e g →
      (n : ℝ) ≤ D * (S.filter fun i => f i ∈ U).card →
      (∀ k ∈ U, o (δ ^ H * q {i | i ∈ S ∧ f i = k} * δ ^ 2) ≤
        ∑ i ∈ S with f i = k, μ (Z i)) →
      900 * ((3 / 100 : ℝ) * b) ^ ηE ≤ δ ^ H →
      let r := (3 / 100 : ℝ) * b
      let M := ((9 * b / (8 * a)) * K) / (1 / 100 : ℝ)
      let l := (δ ^ (-h) * K * D * δ ^ (-η)) / (1 / 100 : ℝ) ^ 3
      o (κ * r ^ (ω + ε) * (M⁻¹) ^ 2 * (L * r ^ 2) *
        (M ^ (-(3 / 2 : ℝ)) * l * (L * r)) ^ (-σ)) ≤ μ (⋃ j, packetShading b S Z f U g j) := by
  classical
  intro ε hε
  obtain ⟨κ, hκ, ηE, hηE, hbound⟩ := pointwise_dense_estimate hE ε hε
  refine ⟨1000000 * κ, ηE, by positivity, hηE, ?_⟩
  intro δ η h ρ K m a b D H n N L x v Y Z S y w f U z e g
    hδ hδ1 hδρ hh hη hK hD hb3 hU hA hC hcover hcard hdense hdensity
  let r := (3 / 100 : ℝ) * b
  let M := ((9 * b / (8 * a)) * K) / (1 / 100 : ℝ)
  let l := (δ ^ (-h) * K * D * δ ^ (-η)) / (1 / 100 : ℝ) ^ 3
  let c : ℝ := 1 / 100
  have hc : 0 < c := by norm_num [c]
  have ha : 0 < a := hδ.trans_le (hδρ.trans hcover.width)
  have hb : 0 < b := ha.trans_le hcover.ordered
  have hr : 0 < r := by dsimp [r]; positivity
  have hr100 : r ≤ 1 / 100 := by dsimp [r]; linarith
  have hM : 1 ≤ M := by
    have hratio : 1 ≤ 9 * b / (8 * a) := (one_le_div (by positivity)).mpr (by linarith [hcover.ordered])
    have hmul := one_le_mul_of_one_le_of_one_le hratio hK
    dsimp [M]
    apply (one_le_div (by norm_num : (0 : ℝ) < 1 / 100)).mpr
    linarith
  have hl : 1 ≤ l := by
    have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hh)
    have hq := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hη)
    have hmul := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hp hK) hD) hq
    dsimp [l]
    apply (one_le_div (by norm_num : (0 : ℝ) < (1 / 100 : ℝ) ^ 3)).mpr
    linarith
  let w' : Fin L → V := fun j => (e j).symm (EuclideanSpace.single 2 1)
  let x' : Fin L → V := fun j => c • z j - (1 / 2 : ℝ) • w' j
  let Q : Fin L → Set V := fun j => factoringCarrier b (z j) (e j)
  let Y' : Fin L → Set V := fun j => uniformMap hc '' packetShading b S Z f U g j
  have hnorm (j : Fin L) := normalized_factoring_carrier hb3
    (factored_center_norm_lt hδ hδρ hA hC hcover j) (e j)
  have hcover' (j : Fin L) : uniformMap hc '' Q j ⊆ T r (x' j) (w' j) := (hnorm j).2.1
  have hshape (j : Fin L) := factored_coarse_shading hδ hδρ hA hC hcover hdense j
  have hfib : ∀ j, ‖w' j‖ = 1 ∧ T r (x' j) (w' j) ⊆ I ∧ MeasurableSet (Y' j) ∧
      Y' j ⊆ T r (x' j) (w' j) := by
    intro j
    exact ⟨(hnorm j).1, (hnorm j).2.2,
      (uniformMap hc).toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hshape j).1,
      (Set.image_mono (hshape j).2.1).trans (hcover' j)⟩
  have hden : ∀ j, o (r ^ ηE * r ^ 2) ≤ μ (Y' j) := by
    intro j
    have hnum : r ^ ηE * r ^ 2 ≤ c ^ 3 * (δ ^ H * b ^ 2) := by
      calc
        _ = c ^ 3 * (900 * r ^ ηE * b ^ 2) := by dsimp [c, r]; ring
        _ ≤ _ := by gcongr
    change ENNReal.ofReal _ ≤ volume (uniformMap hc '' packetShading b S Z f U g j)
    rw [uniformMap_volume hc]
    refine (ENNReal.ofReal_le_ofReal hnum).trans ?_
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ c ^ 3)]
    exact mul_le_mul_right (hshape j).2.2 _
  have hK' : Interfaces.K r M L x' w' := by
    have hh := normalized_carrier_katz hc Q x' w'
      (ρ := 3 * b) (by simpa only [show c * (3 * b) = r by dsimp [c, r]; ring] using hcover')
      (factored_carrier_katz_count (hδ.trans_le hδρ) (by linarith) hcover)
    simpa only [show c * (3 * b) = r by dsimp [c, r]; ring] using hh
  have hF' : F r l L x' w' := normalized_carrier_frostman hc (by norm_num [c]) Q x' w' hcover'
    (factored_carrier_slab_count hδ hδρ (by linarith) (by linarith) hU hA hC hcover hcard)
  have hL : 0 < L := by
    obtain ⟨k, hk⟩ := hU
    exact Nat.zero_lt_of_lt (g k).isLt
  have hv := hbound r hr hr100 M l hM hl L x' w' Y' hL hfib hden hK' hF'
  have hvol : μ (⋃ j, Y' j) = o (c ^ 3) * μ (⋃ j, packetShading b S Z f U g j) := by
    rw [← Set.image_iUnion]
    exact uniformMap_volume hc _
  rw [hvol] at hv
  have hv' := mul_le_mul_right hv (o 1000000)
  change o ((1000000 * κ) * r ^ (ω + ε) * (M⁻¹) ^ 2 * (L * r ^ 2) *
    (M ^ (-(3 / 2 : ℝ)) * l * (L * r)) ^ (-σ)) ≤ _
  convert hv' using 1
  · rw [o, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1000000)]
    congr 1
    ring
  · rw [← mul_assoc, o, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1000000)]
    norm_num [c]

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Interfaces
