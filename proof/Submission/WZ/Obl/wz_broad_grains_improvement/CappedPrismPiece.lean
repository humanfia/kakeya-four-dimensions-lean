-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedPrismPiece.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.NarrowBundle

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms
  (PrismPiece Crosses high_count_common_cut broad_of_fixed_packet)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (bodyCount)
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)

/-- An effective incidence cap for one piece, including its normalized mass.
This is the one-column version of the accepted `PrismData.HasCaps`. -/
def PrismPieceCap {n N J : ℕ} (d h a c : ℝ) (ρ : Fin J → ℝ)
    (Q : PrismPiece n N J) : Prop :=
  ∃ m : ℝ, 0 < m ∧ (∀ p, bodyCount Q.piece p ≤ m) ∧
    O (d ^ h * m) * μ (P a (ρ Q.scale * c) c Q.center Q.frame) ≤
      ∑ i, μ (Q.piece i)

/-- A spatial cut keeps all the geometric metadata of one prism. -/
def cutPrismPiece {n N J : ℕ} (Q : PrismPiece n N J) (E : Set V) : PrismPiece n N J :=
  { Q with piece := fun i => Q.piece i ∩ E }

/-- High-count selection supplies both ordinary density and normalized caps.
The static packet is used only to transfer broadness after the common cut. -/
theorem high_count_capped_piece {n N J : ℕ} {ω ζ d h a c s θ D : ℝ}
    {ρ : Fin J → ℝ} {x v : Fin n → V} {y w : Fin N → V}
    (Q : PrismPiece n N J) (S : Finset (Fin n))
    (hd : 0 < d) (hθ : 0 < θ) (hD : 0 < D) (hS : S.Nonempty)
    (hshape : d ≤ a ∧ a ≤ ρ Q.scale * c ∧ ρ Q.scale * c ≤ c ∧ c ≤ 1)
    (hpieces : ∀ i, MeasurableSet (Q.piece i) ∧
      Q.piece i ⊆ P a (ρ Q.scale * c) c Q.center Q.frame)
    (hzero : ∀ i, i ∉ S → Q.piece i = ∅)
    (hcross : ∀ i, (Q.piece i).Nonempty →
      T d (x i) (v i) ⊆ T s (y Q.coarse) (w Q.coarse) ∧
        Crosses d a (ρ Q.scale * c) c (x i) (v i) Q.center Q.frame)
    (hcap : ∀ u r, d ≤ r → ((S.filter (fun i => pd (v i) u ≤ r)).card : ℝ) ≤
      2 * (r / θ) ^ (ω * ζ / 100) * (S.card : ℝ))
    (hmass : O (D * (S.card : ℝ)) * μ (P a (ρ Q.scale * c) c Q.center Q.frame) ≤
      ∑ i, μ (Q.piece i))
    (hdensity : d ^ h ≤ D / 2)
    (hbroad : (4 / D) * (ρ Q.scale / θ) ^ (ω * ζ / 100) ≤ d ^ (-h)) :
    ∃ E : Set V, MeasurableSet E ∧
      (cutPrismPiece Q E).Good ω ζ d h a c s ρ x v y w ∧
      PrismPieceCap d h a c ρ (cutPrismPiece Q E) ∧
      (1 / 2 : ENNReal) * (∑ i, μ (Q.piece i)) ≤
        ∑ i, μ ((cutPrismPiece Q E).piece i) := by
  classical
  have ha := hd.trans_le hshape.1
  have hb := ha.trans_le hshape.2.1
  have hc := hb.trans_le hshape.2.2.1
  have hρ : 0 < ρ Q.scale := (mul_pos_iff_of_pos_right hc).mp hb
  have hSm : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hcount (p : V) : bodyCount Q.piece p ≤ (S.card : ℝ) := by
    have hsub : {i | p ∈ Q.piece i} ⊆ (S : Set (Fin n)) := by
      intro i hi
      change p ∈ Q.piece i at hi
      by_contra hn
      simpa only [hzero i hn, mem_empty_iff_false] using hi
    have hh := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hh
    change ({i | p ∈ Q.piece i}.ncard : ℝ) ≤ (S.card : ℝ)
    exact_mod_cast hh
  have hEfin : μ (P a (ρ Q.scale * c) c Q.center Q.frame) ≠ ∞ := by
    have hv : μ (P a (ρ Q.scale * c) c Q.center Q.frame) = O (a * (ρ Q.scale * c) * c) :=
      WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha.le hb.le hc.le _ _
    rw [hv]
    exact ENNReal.ofReal_ne_top
  obtain ⟨E, hEm, hretain, hdense, hmany⟩ := high_count_common_cut hD hSm
    (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_isClosed _ _ _ _ _).measurableSet
    hEfin Q.piece (fun i => (hpieces i).1) (fun i => (hpieces i).2) hcount hmass
  have hcutzero (i) (hi : i ∉ S) : (cutPrismPiece Q E).piece i = ∅ := by
    simp only [cutPrismPiece, hzero i hi, empty_inter]
  have hbrbudget : (2 / (D / 2)) * (ρ Q.scale / θ) ^ (ω * ζ / 100) ≤ d ^ (-h) := by
    have he : (2 / (D / 2) : ℝ) = 4 / D := by field_simp; norm_num
    rw [he]
    exact hbroad
  have hbr := broad_of_fixed_packet S hd hθ hρ (show 0 < D / 2 by positivity)
    (show (0 : ℝ) ≤ 2 by norm_num) hcutzero
    (fun p hp => by
      have hh := hmany p hp
      change (D / 2) * (S.card : ℝ) ≤ bodyCount (fun i => Q.piece i ∩ E) p
      nlinarith) hcap hbrbudget
  refine ⟨E, hEm, ?_, ?_, hretain⟩
  · refine ⟨hshape.1, hshape.2.1, hshape.2.2.1, hshape.2.2.2, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(hpieces i).1.inter hEm, inter_subset_left.trans (hpieces i).2⟩
    · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hdensity) le_rfl).trans hdense
    · intro i hi
      exact hcross i (hi.mono inter_subset_left)
    · intro p u r _ hdr _
      exact hbr p u r hdr
  · refine ⟨S.card, hSm, ?_, ?_⟩
    · intro p
      apply le_trans _ (hcount p)
      change ({i | p ∈ (cutPrismPiece Q E).piece i}.ncard : ℝ) ≤
        ({i | p ∈ Q.piece i}.ncard : ℝ)
      exact_mod_cast Set.ncard_le_ncard
        (show {i | p ∈ (cutPrismPiece Q E).piece i} ⊆ {i | p ∈ Q.piece i}
          from fun _ hi => hi.1)
    · calc
        _ ≤ O ((D / 2) * (S.card : ℝ)) * μ (P a (ρ Q.scale * c) c Q.center Q.frame) := by
          apply mul_le_mul' _ le_rfl
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hdensity hSm.le)
        _ = (1 / 2 : ENNReal) *
            (O (D * (S.card : ℝ)) * μ (P a (ρ Q.scale * c) c Q.center Q.frame)) := by
          rw [show D / 2 * (S.card : ℝ) = (1 / 2) * (D * (S.card : ℝ)) by ring,
            O, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          norm_num [ENNReal.ofReal_div_of_pos, mul_assoc]
        _ ≤ (1 / 2 : ENNReal) * ∑ i, μ (Q.piece i) := mul_le_mul' le_rfl hmass
        _ ≤ _ := hretain

end WangZahlLot.Obl.wz_broad_grains_improvement
