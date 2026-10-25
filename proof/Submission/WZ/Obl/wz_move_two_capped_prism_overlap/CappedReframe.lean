-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CappedReframe.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.AxialReframe
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CappedParameterCell
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.AngularScale

/- Adapted from this workspace: o197/x0567, 422e78fd8000, CappedReframe.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P T I A bodyCount)

/-- Reorient a capped parameter class into a single fixed-radius carrier.
The enlargement costs only a constant divided by the original coarse radius. -/
theorem capped_axial_reframe {ω ζ δ h h' ρ c θ K : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V} {y u : V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh : 0 ≤ h) (hhh : h ≤ h')
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 16 ≤ θ * K)
    (hδc : 4 * δ ≤ c) (hthin : D.a ≤ θ * c / 128) (hsmall : K * c ≤ θ / 8)
    (hβ : 0 ≤ ω * ζ / 100)
    (hdensity : O (δ ^ h') * O (128 * K ^ 3 * θ / ρ) ≤ O (δ ^ h))
    (hangular : δ ^ (-h) * (1 / ρ) ^ (ω * ζ / 100) ≤ δ ^ (-h'))
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i)) (hu : ‖u‖ = 1)
    (H : D.Valid ω ζ δ h ρ c x v Y 1) (Hcap : D.HasCaps δ h ρ c)
    (hclass : ∀ i j, (D.W i j).Nonempty → ‖v i - u‖ ≤ θ / 100 ∧
      T δ (x i) (v i) ⊆ T (θ / 4) y u ∧ D.PairAway ρ c (100 * (K * c)) x v i j) :
    ∃ D' : PrismData n, D'.a = 128 * K * D.a ∧ D'.N = 1 ∧
      D'.Valid ω ζ δ h' θ (K * c) x v Y 1 ∧ D'.HasCaps δ h' θ (K * c) ∧
      ∀ i j, (D'.W i j).Nonempty →
        ∀ p ∈ P D'.a (θ * (K * c)) (K * c) (D'.z j) (D'.e j),
          96 * (K * c) < dist p (x i) ∧ 96 * (K * c) < dist p (x i + v i) := by
  have Hcopy := H
  rcases Hcopy with ⟨hδa, hab, hbc, hc1, hW, hmass, hdense, hcross, hbroad, hX, hw, hcover, hdisj⟩
  have ha : 0 < D.a := hδ.trans_le hδa
  have hc : 0 < c := ha.trans_le (hab.trans hbc)
  have hρ : 0 < ρ := (mul_pos_iff.mp (ha.trans_le hab)).resolve_right
    (by intro hh; linarith [hh.2]) |>.1
  have hρ1 : ρ ≤ 1 := (mul_le_mul_iff_left₀ hc).mp (by simpa using hbc)
  have hK0 : 0 < K := by nlinarith
  have hK16 : 16 ≤ K := by nlinarith
  have hnewa : 0 < 128 * K * D.a := by positivity
  have hnewab : 128 * K * D.a ≤ θ * (K * c) := by nlinarith
  have hnewbc : θ * (K * c) ≤ K * c := by nlinarith
  have hshort (i : Fin n) (j : Fin D.L) (hi : (D.W i j).Nonempty) :
      |D.e j (v i) 0| ≤ 6 * D.a / c :=
    (WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_direction
      (D.e j) hδ hδa hab hδc (hv i) (hcross i j hi).2.2).1
  have he (j : Fin D.L) : ∃ e' : V ≃ₗᵢ[ℝ] V,
      (∀ p, e' p 0 = D.e j p 0) ∧ e' u 1 = 0 := by
    obtain ⟨i, hi⟩ := valid_prism_nonempty D hδ H j
    apply exists_axial_frame (D.e j) hu
    have hvu := (hclass i j hi).1
    have hdiff : |D.e j u 0 - D.e j (v i) 0| ≤ θ / 100 := by
      have hd := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.abs_rotated_coord_le (D.e j) (u - v i) 0
      rw [norm_sub_rev] at hd
      simpa only [map_sub, PiLp.sub_apply] using hd.trans hvu
    have hsum := (abs_sub_le (D.e j u 0) (D.e j (v i) 0) 0)
    simp only [sub_zero] at hsum
    have hs := hshort i j hi
    have ht : 6 * D.a / c ≤ 6 * θ / 128 := by
      apply (div_le_iff₀ hc).mpr
      nlinarith
    linarith
  choose e' hcoord hu1 using he
  have hgeom (i : Fin n) (j : Fin D.L) (hi : (D.W i j).Nonempty) :
      P D.a (ρ * c) c (D.z j) (D.e j) ⊆ P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j) ∧
      (∀ p ∈ T δ (x i) (v i) ∩ frontier (P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j)),
        |e' j (p - D.z j) 2| = (K * c) / 2) ∧
      (∀ t ∈ ({-(K * c) / 2, (K * c) / 2} : Set ℝ), ∃ p ∈ T δ (x i) (v i) ∩
        P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j), e' j (p - D.z j) 2 = t) ∧
      P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j) ⊆ T θ y u ∧
      (e' j u 0) ^ 2 + (e' j u 1) ^ 2 ≤ (10 * θ) ^ 2 ∧
      ∀ p ∈ P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j),
        96 * (K * c) < dist p (x i) ∧ 96 * (K * c) < dist p (x i + v i) := by
    obtain ⟨p, hp⟩ := hi
    have hpP := ((hW i j).2.1 hp).2
    have hpT := hYT i ((hW i j).2.1 hp).1
    exact axial_reframe_geometry (D.e j) (e' j) hδ hθ hθ1 hK hδa hab hbc hthin hsmall
      (hv i) (hclass i j ⟨p, hp⟩).1 (hshort i j ⟨p, hp⟩) (hcoord j) (hu1 j)
      ⟨hpT, hpP⟩ ((hclass i j ⟨p, hp⟩).2.2 p hpP).1
      ((hclass i j ⟨p, hp⟩).2.2 p hpP).2 (hclass i j ⟨p, hp⟩).2.1
  have hall (j : Fin D.L) :
      P D.a (ρ * c) c (D.z j) (D.e j) ⊆ P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j) ∧
      P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j) ⊆ T θ y u ∧
      (e' j u 0) ^ 2 + (e' j u 1) ^ 2 ≤ (10 * θ) ^ 2 := by
    obtain ⟨i, hi⟩ := valid_prism_nonempty D hδ H j
    have hg := hgeom i j hi
    exact ⟨hg.1, hg.2.2.2.1, hg.2.2.2.2.1⟩
  have hvol (j : Fin D.L) :
      volume (P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j)) =
      O (128 * K ^ 3 * θ / ρ) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume hnewa.le (by positivity) (by positivity),
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha.le (by positivity) hc.le]
    change ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 128 * K ^ 3 * θ / ρ)]
    congr 1
    field_simp
    <;> ring
  let D' : PrismData n := {
    a := 128 * K * D.a, s := θ, L := D.L, N := 1, z := D.z, e := e', W := D.W,
    y := fun _ => y, w := fun _ => u, γ := fun _ => 0 }
  refine ⟨D', rfl, rfl, ?_, ?_, ?_⟩
  · change δ ≤ 128 * K * D.a ∧ _
    refine ⟨by nlinarith, hnewab, hnewbc, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
    · intro i j
      exact ⟨(hW i j).1, fun p hp => ⟨((hW i j).2.1 hp).1, (hall j).1 ((hW i j).2.1 hp).2⟩,
        (hW i j).2.2⟩
    · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hhh)) le_rfl).trans hmass
    · intro j
      change O (δ ^ h') * volume (P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j)) ≤ _
      rw [hvol, ← mul_assoc]
      exact (mul_le_mul' hdensity le_rfl).trans (hdense j)
    · intro i j hi
      have hg := hgeom i j hi
      exact ⟨((hclass i j hi).2.1).trans (thickening_mono (by linarith : θ / 4 ≤ θ) _),
        hg.2.1, hg.2.2.1⟩
    · intro j p w r hw hdr hrθ
      have hb := angular_bound_enlarge v {i | p ∈ D.W i j} hδ hρ hρ1 hβ
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith : -h ≤ 0))
        hangular (hbroad j p) w r hw hdr (hrθ.trans hθ1)
      simp only [div_one] at hb
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
      apply Real.rpow_le_rpow (hδ.le.trans hdr) _ hβ
      exact (le_div_iff₀ hθ).mpr (by nlinarith)
    · intro i j hne
      exact (hne (Subsingleton.elim i j)).elim
    · intro _
      exact hu
    · intro _
      exact ⟨rfl, fun j => (hall j).2⟩
  · obtain ⟨m, hm, hcount, havg⟩ := Hcap
    refine ⟨m, hm, hcount, ?_⟩
    intro j
    change O (δ ^ h' * m j) * volume (P (128 * K * D.a) (θ * (K * c)) (K * c) (D.z j) (e' j)) ≤ _
    rw [hvol]
    have hh : O (δ ^ h' * m j) * (O (128 * K ^ 3 * θ / ρ) *
        volume (P D.a (ρ * c) c (D.z j) (D.e j))) =
      (O (δ ^ h') * O (128 * K ^ 3 * θ / ρ)) * O (m j) *
        volume (P D.a (ρ * c) c (D.z j) (D.e j)) := by
      change ENNReal.ofReal _ * _ = _
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
      ring
    rw [hh]
    apply (mul_le_mul' (mul_le_mul' hdensity le_rfl) le_rfl).trans
    simpa only [O, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h)] using havg j
  · intro i j hi
    exact (hgeom i j hi).2.2.2.2.2

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
