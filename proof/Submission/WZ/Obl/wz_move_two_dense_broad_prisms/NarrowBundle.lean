-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.NarrowBundle.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.FixedPacket
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.HighCountCut
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.NarrowGeometry

/-! Dense broad prisms obtained by extending one fixed narrow packet. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric MeasureTheory
open scoped ENNReal
open wz_measurable_angular_selection (pd)
open wz_clustered_cover_volume_gain (bodyCount)

/-- Extend one static packet to its natural length, then retain a common
high-multiplicity cut. Directional broadness survives because the tube set is fixed. -/
theorem narrow_fixed_packet_good {n N J : ℕ} {ω ζ d h θ s mass D : ℝ}
    (hd : 0 < d) (hθ : 0 < θ) (hθsmall : θ ≤ 1/10000)
    (hlength : 10*(d/θ) ≤ 1) (hD : 0 < D)
    (hmass : D*((10000*d)*(10000*d)*(10*(d/θ))) ≤ mass)
    (hdense : d^h ≤ D/2) (hbudget : (4/D)*1000^(ω*ζ/100) ≤ d^(-h))
    (x v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (y w : Fin N → V) (k₀ : Fin N) (ρ : Fin J → ℝ) (k : Fin J)
    (hρ : ρ k = 1000*θ)
    (U : Fin n → Set V) (hUm : ∀ i, MeasurableSet (U i))
    (hUT : ∀ i, U i ⊆ T d (x i) (v i))
    (S : Finset (Fin n)) (hS : S.Nonempty) (p u : V) (hu : ‖u‖ = 1)
    (hp : ∀ i ∈ S, p ∈ U i)
    (hang : ∀ i ∈ S, pd (v i) u ≤ 2*θ)
    (hends : ∀ i ∈ S, 40*(d/θ) ≤ dist p (x i) ∧ 40*(d/θ) ≤ dist p (x i+v i))
    (hcover : ∀ i ∈ S, T d (x i) (v i) ⊆ T s (y k₀) (w k₀))
    (hrow : ∀ i ∈ S, O mass ≤ volume (U i ∩ ball p ((d/θ)/2)))
    (hcap : ∀ u' r, d ≤ r → ((S.filter (fun i => pd (v i) u' ≤ r)).card : ℝ) ≤
      2*(r/θ)^(ω*ζ/100)*(S.card : ℝ)) :
    ∃ Q : PrismPiece n N J, Q.scale = k ∧ Q.coarse = k₀ ∧
      Q.Good ω ζ d h (10000*d) (10*(d/θ)) s ρ x v y w ∧
      ∀ i, Q.piece i ⊆ U i := by
  classical
  have hell : 0 < d/θ := div_pos hd hθ
  have hside : 10000*d ≤ 10*(d/θ) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hθ).mpr
    nlinarith
  have hwidth : ρ k*(10*(d/θ)) = 10000*d := by
    rw [hρ]
    field_simp
    <;> ring
  obtain ⟨e, he⟩ := narrow_cap_prism hd hθ hθsmall p u hu
  let E := P (10000*d) (10000*d) (10*(d/θ)) p e
  let Y := fun i => if i ∈ S then U i ∩ ball p ((d/θ)/2) else ∅
  have hYm (i) : MeasurableSet (Y i) := by
    dsimp [Y]
    split_ifs
    · exact (hUm i).inter measurableSet_ball
    · exact MeasurableSet.empty
  have hYU (i) : Y i ⊆ U i := by
    dsimp [Y]
    split_ifs
    · exact inter_subset_left
    · exact empty_subset _
  have hmem {i : Fin n} {z : V} (hz : z ∈ Y i) : i ∈ S := by
    by_contra hi
    simpa only [Y, if_neg hi, mem_empty_iff_false] using hz
  have hgeom (i) (hi : i ∈ S) := he (x i) (v i) (hv i) (hUT i (hp i hi))
    (hang i hi) (hends i hi).1 (hends i hi).2
  have hYE (i) : Y i ⊆ E := by
    intro z hz
    have hi := hmem hz
    have hz' : z ∈ U i ∩ ball p ((d/θ)/2) := by simpa only [Y, if_pos hi] using hz
    have hcore := (hgeom i hi).2 ⟨hUT i hz'.1, hz'.2⟩
    change |e (z-p) 0| ≤ (10000*d)/2 ∧
      |e (z-p) 1| ≤ (10000*d)/2 ∧ |e (z-p) 2| ≤ (10*(d/θ))/2
    exact ⟨by linarith [hcore.1], by linarith [hcore.2.1], by linarith [hcore.2.2]⟩
  have hEm : MeasurableSet E :=
    (wz_two_scale_flat_box_estimate.box_isClosed _ _ _ _ _).measurableSet
  have hvol : volume E = O ((10000*d)*(10000*d)*(10*(d/θ))) :=
    wz_two_scale_flat_box_estimate.box_volume (by positivity) (by positivity) (by positivity) p e
  have hEfin : volume E ≠ ∞ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  have hN : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hcount (z : V) : bodyCount Y z ≤ (S.card : ℝ) := by
    have hsub : {i | z ∈ Y i} ⊆ (S : Set (Fin n)) := fun i hi => hmem hi
    have hh := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hh
    change (Set.ncard {i | z ∈ Y i} : ℝ) ≤ (S.card : ℝ)
    exact_mod_cast hh
  have hsum : O ((S.card : ℝ)*mass) ≤ ∑ i, volume (Y i) := by
    change ENNReal.ofReal ((S.card : ℝ)*mass) ≤ _
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    calc
      (S.card : ENNReal)*O mass = ∑ i ∈ S, O mass := by simp
      _ ≤ ∑ i ∈ S, volume (Y i) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Y, if_pos hi] using hrow i hi
      _ ≤ ∑ i, volume (Y i) := Finset.sum_le_univ_sum_of_nonneg (fun _ => bot_le)
  have htotal : O (D*(S.card : ℝ))*volume E ≤ ∑ i, volume (Y i) := by
    rw [hvol]
    change ENNReal.ofReal (D*(S.card : ℝ))*ENNReal.ofReal _ ≤ _
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ D*(S.card : ℝ))]
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hsum
    nlinarith
  obtain ⟨C, hCm, _, hdensity, hmany⟩ := high_count_common_cut hD hN hEm hEfin
    Y hYm hYE hcount htotal
  let W := fun i => Y i ∩ C
  have hzero (i) (hi : i ∉ S) : W i = ∅ := by simp only [W, Y, if_neg hi, empty_inter]
  have hmany' (z) (hz : z ∈ ⋃ i, W i) : (D/2)*(S.card : ℝ) ≤ q n {i | z ∈ W i} := by
    have hh := hmany z hz
    change D*(S.card : ℝ)/2 ≤ q n {i | z ∈ W i} at hh
    nlinarith
  have hBr := broad_of_fixed_packet S hd hθ (show 0 < ρ k by rw [hρ]; positivity)
    (show 0 < D/2 by positivity) (show (0 : ℝ) ≤ 2 by norm_num) hzero hmany' hcap
    (show (2/(D/2))*(ρ k/θ)^(ω*ζ/100) ≤ d^(-h) by
      have heq : ρ k/θ = 1000 := by rw [hρ]; field_simp
      rw [heq]
      convert hbudget using 1 <;> congr 1 <;> field_simp <;> ring)
  let Q : PrismPiece n N J := ⟨k, k₀, p, e, W⟩
  refine ⟨Q, rfl, rfl, ?_, fun i z hz => hYU i hz.1⟩
  change d ≤ 10000*d ∧ 10000*d ≤ ρ k*(10*(d/θ)) ∧
    ρ k*(10*(d/θ)) ≤ 10*(d/θ) ∧ 10*(d/θ) ≤ 1 ∧ _
  rw [hwidth]
  refine ⟨by linarith, le_rfl, hside, hlength, ?_, ?_, ?_, ?_⟩
  · exact fun i => ⟨(hYm i).inter hCm, inter_subset_left.trans (hYE i)⟩
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hdense) (le_refl (volume E))).trans hdensity
  · intro i hi
    obtain ⟨z, hz⟩ := hi
    have hiS := hmem hz.1
    exact ⟨hcover i hiS, (hgeom i hiS).1⟩
  · intro z u' r _ hdr _
    exact hBr z u' r hdr

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
