-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.WeightedTransverse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedRegular
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedCut
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TransverseDichotomy

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, WeightedTransverse.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V O μ transverseDensity transverseDensity_pos)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

/-- The geometric part of the transverse argument only needs a dense anchor
set. The measure used to select that anchor does not enter this implication. -/
theorem transverse_anchor_forces_density {n : ℕ} {a b D h s r L J q : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hD : 0 < D) (hh : 0 < h) (hs : 0 < s) (hs1 : s ≤ 1)
    (has : a ≤ s * b) (hr : 0 < r) (hL : 0 ≤ L)
    (hLr : L * r ≤ (s / 2) * b) (hJ : 0 < J) (hq : 0 ≤ q)
    (f : V ≃ᵃ[ℝ] V) (c : Fin n → V)
    (u : Fin n → OrthonormalBasis (Fin 3) ℝ V) (H : Fin n → Set V) (Z U : Set V)
    (hvol : ∀ Q, volume (f '' Q) = O J * volume Q)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q)
    (hHm : ∀ i, MeasurableSet (H i)) (hHP : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hHZ : ∀ i, f '' H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p r) ≤ O (q * r ^ 3))
    (i : Fin n) (A : Set V) (hAm : MeasurableSet A) (hAP : A ⊆ prism a b (c i) (u i))
    (hA : O (D / 2) * volume (prism a b (c i) (u i)) ≤ volume A)
    (htrans : ∀ p ∈ A, ∃ j, s < pd (u j 0) (u i 0) ∧ p ∈ H j) :
    transverseDensity a b D h s ≤ 46080 * q := by
  have hb0 : 0 < b := ha.trans_le hab
  obtain ⟨t, hst, ht1, hfill⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.transverse_global_filling
      ha hab hb hh (half_pos hD) hs hs1 c (fun j => u j) H (c i) (u i) A
      (fun j => (u j).orthonormal) hHm hHP hregular (u i).orthonormal hAm hAP hA
      (fun p hp => by
        obtain ⟨j, hj, hpj⟩ := htrans p hp
        exact ⟨j, hpj, hj.le⟩)
  let F : Set V := {p | |inner ℝ (u i 0) (p - c i)| ≤ 3 * a + 2 * t * b} ∩
    (cTube b (c i) (u i) ∩ ⋃ j, H j)
  have hFZ : f '' F ⊆ Z := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp.2.2
    exact hHZ j ⟨p, hj, rfl⟩
  have hcoords : F ⊆ orthogonalBox ![3 * a + 2 * t * b, 4 * b, 1] (c i) (u i) := by
    intro p hp j
    have hbnd := WangZahlLot.Obl.wz_clustered_cover_volume_gain.cTube_coordinate_bounds
      (u i).orthonormal hp.2.1
    fin_cases j
    · exact hp.1
    · exact hbnd.1 1 (by decide)
    · change |inner ℝ (u i 2) (p - c i)| ≤ 1
      calc
        _ ≤ ‖u i 2‖ * ‖p - c i‖ := abs_real_inner_le_norm _ _
        _ = ‖p - c i‖ := by rw [(u i).orthonormal.1 2, one_mul]
        _ ≤ 4 * b + 1 / 2 := hbnd.2
        _ ≤ 1 := by linarith
  apply WangZahlLot.Obl.wz_clustered_cover_volume_gain.affine_filling_forces_ball_density
    ha.le hb0 (hb.trans (by norm_num)) ((half_pos hs).trans_le hst) ht1
    (by nlinarith [mul_le_mul_of_nonneg_right hst hb0.le])
    (transverseDensity_pos ha hab hD hh).le hq hr hL
    (hLr.trans (mul_le_mul_of_nonneg_right hst hb0.le)) hJ f (c i) (u i) F U
    hvol hLip hcoords (hFZ.trans hZU) hUball ?_ (fun p hp => hupper p (hFZ hp))
  convert hfill using 1
  congr 1
  dsimp [transverseDensity]
  ring

/-- A transverse cut can preserve the incidence measure of each individual
prism. It suffices to know its average weighted density and an upper density
bound for that measure; pointwise lower multiplicity is unnecessary. -/
theorem weighted_regular_prism_transverse_or_narrow {n : ℕ} {a b D h s r L J q : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hD : 0 < D) (hh : 0 < h) (hs : 0 < s) (hs1 : s ≤ 1)
    (has : a ≤ s * b) (hr : 0 < r) (hL : 0 ≤ L)
    (hLr : L * r ≤ (s / 2) * b) (hJ : 0 < J) (hq : 0 ≤ q)
    (f : V ≃ᵃ[ℝ] V) (c : Fin n → V)
    (u : Fin n → OrthonormalBasis (Fin 3) ℝ V) (H : Fin n → Set V) (Z U : Set V)
    (ν : Fin n → Measure V) (m : Fin n → ℝ) (hm : ∀ i, 0 < m i)
    (hvol : ∀ Q, volume (f '' Q) = O J * volume Q)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q)
    (hHm : ∀ i, MeasurableSet (H i)) (hHP : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hHZ : ∀ i, f '' H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hfin : ∀ i, ν i (H i) ≠ ⊤)
    (hdom : ∀ i A, MeasurableSet A → ν i A ≤ O (m i) * volume A)
    (hdense : ∀ i, O (D * m i) * volume (prism a b (c i) (u i)) ≤ ν i (H i))
    (hregular : ∀ i p, p ∈ H i →
      O h * μ (prism a b (c i) (u i) ∩ ball p b) ≤ μ (H i ∩ ball p b))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p r) ≤ O (q * r ^ 3)) :
    transverseDensity a b D h s ≤ 46080 * q ∨
    ∃ G : Fin n → Set V,
      (∀ i, MeasurableSet (G i) ∧ G i ⊆ H i ∧
        (1 / 2 : ENNReal) * ν i (H i) ≤ ν i (G i)) ∧
      ∀ i j p, p ∈ G i → p ∈ G j → pd (u i 0) (u j 0) ≤ s := by
  rcases dominated_remove_bad_incidences volume ν H (fun i => prism a b (c i) (u i))
      (fun i j => s < pd (u j 0) (u i 0)) m hD.le hm hHm hfin hdom hdense with hbad | hgood
  · obtain ⟨i, A, hAm, hAH, hA, htrans⟩ := hbad
    exact Or.inl (transverse_anchor_forces_density ha hab hb hD hh hs hs1 has
      hr hL hLr hJ hq f c u H Z U hvol hLip hHm hHP hHZ hZU hUball hregular hupper
      i A hAm (hAH.trans (hHP i)) hA htrans)
  · obtain ⟨G, hG, hrel⟩ := hgood
    exact Or.inr ⟨G, hG, fun i j p hi hj => le_of_not_gt (hrel j i p hj hi)⟩

/-- Weighted regularization followed by a weighted transverse cut retains a
quarter of every incidence measure and a quarter of its effective density. -/
theorem weighted_prism_transverse_or_narrow {n : ℕ} {a b D s r L J q : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 1000000)
    (hD : 0 < D) (hs : 0 < s) (hs1 : s ≤ 1)
    (has : a ≤ s * b) (hr : 0 < r) (hL : 0 ≤ L)
    (hLr : L * r ≤ (s / 2) * b) (hJ : 0 < J) (hq : 0 ≤ q)
    (f : V ≃ᵃ[ℝ] V) (c : Fin n → V)
    (u : Fin n → OrthonormalBasis (Fin 3) ℝ V) (H : Fin n → Set V) (Z U : Set V)
    (ν : Fin n → Measure V) (m : Fin n → ℝ) (hm : ∀ i, 0 < m i)
    (hvol : ∀ Q, volume (f '' Q) = O J * volume Q)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q)
    (hHm : ∀ i, MeasurableSet (H i)) (hHP : ∀ i, H i ⊆ prism a b (c i) (u i))
    (hHZ : ∀ i, f '' H i ⊆ Z) (hZU : Z ⊆ U) (hUball : U ⊆ ball 0 1)
    (hfin : ∀ i, ν i (H i) ≠ ⊤)
    (hdom : ∀ i A, MeasurableSet A → ν i A ≤ O (m i) * volume A)
    (hdense : ∀ i, O (D * m i) * volume (prism a b (c i) (u i)) ≤ ν i (H i))
    (hupper : ∀ p ∈ Z, volume (U ∩ ball p r) ≤ O (q * r ^ 3)) :
    transverseDensity a b (D / 2) (D / 16000) s ≤ 46080 * q ∨
    ∃ G : Fin n → Set V,
      (∀ i, MeasurableSet (G i) ∧ G i ⊆ H i ∧
        (1 / 4 : ENNReal) * ν i (H i) ≤ ν i (G i) ∧
        O (D / 4) * volume (prism a b (c i) (u i)) ≤ volume (G i)) ∧
      ∀ i j p, p ∈ G i → p ∈ G j → pd (u i 0) (u j 0) ≤ s := by
  choose C hCm hCH hkeep hreg using fun i => convex_weighted_regular_at_radius (ν i)
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.prism_convex a b (c i) (u i))
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.prism_measurable a b (c i) (u i))
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.prism_totallyBounded
      a b (c i) (u i).orthonormal) (hHm i) (hHP i) (hfin i)
    (mul_nonneg hD.le (hm i).le) (ha.trans_le hab) (hdense i)
  have hregvol (i : Fin n) (p : V) (hp : p ∈ C i) :
      O (D / 16000) * volume (prism a b (c i) (u i) ∩ ball p b) ≤
        volume (C i ∩ ball p b) := by
    have hh := (hreg i p hp).trans (hdom i _ ((hCm i).inter measurableSet_ball))
    have he : O (D * m i / 16000) = O (m i) * O (D / 16000) := by
      rw [← ENNReal.ofReal_mul (hm i).le]
      congr 1
      ring
    rw [he, mul_assoc] at hh
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (hm i)).ne'
      ENNReal.ofReal_ne_top).mp hh
  have hdenC (i : Fin n) : O ((D / 2) * m i) * volume (prism a b (c i) (u i)) ≤
      ν i (C i) := by
    calc
      _ = (1 / 2 : ENNReal) * (O (D * m i) * volume (prism a b (c i) (u i))) := by
        rw [← mul_assoc]
        congr 1
        rw [show (D / 2) * m i = D * m i / 2 by ring]
        change ENNReal.ofReal (D * m i / 2) = _
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num [O, div_eq_mul_inv, mul_comm]
      _ ≤ (1 / 2 : ENNReal) * ν i (H i) := mul_le_mul' le_rfl (hdense i)
      _ ≤ _ := hkeep i
  rcases weighted_regular_prism_transverse_or_narrow ha hab hb (half_pos hD)
      (by positivity : 0 < D / 16000) hs hs1 has hr hL hLr hJ hq f c u C Z U ν m hm
      hvol hLip hCm (fun i => (hCH i).trans (hHP i))
      (fun i => (image_mono (hCH i)).trans (hHZ i)) hZU hUball
      (fun i => ne_top_of_le_ne_top (hfin i) (measure_mono (hCH i)))
      hdom hdenC hregvol hupper with hden | hcut
  · exact Or.inl hden
  · obtain ⟨G, hG, hnarrow⟩ := hcut
    have hret (i : Fin n) : (1 / 4 : ENNReal) * ν i (H i) ≤ ν i (G i) := by
      calc
        _ = (1 / 2 : ENNReal) * ((1 / 2 : ENNReal) * ν i (H i)) := by
          rw [← mul_assoc]
          congr 1
          norm_num [one_div, ← ENNReal.mul_inv]
        _ ≤ (1 / 2 : ENNReal) * ν i (C i) := mul_le_mul' le_rfl (hkeep i)
        _ ≤ _ := (hG i).2.2
    refine Or.inr ⟨G, ?_, hnarrow⟩
    intro i
    refine ⟨(hG i).1, (hG i).2.1.trans (hCH i), hret i, ?_⟩
    have hlow : O (m i) * (O (D / 4) * volume (prism a b (c i) (u i))) ≤
        O (m i) * volume (G i) := by
      calc
        _ = (1 / 4 : ENNReal) * (O (D * m i) * volume (prism a b (c i) (u i))) := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (hm i).le]
          congr 1
          rw [show m i * (D / 4) = D * m i / 4 by ring]
          change ENNReal.ofReal (D * m i / 4) = _
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
          norm_num [O, div_eq_mul_inv, mul_comm]
        _ ≤ (1 / 4 : ENNReal) * ν i (H i) := mul_le_mul' le_rfl (hdense i)
        _ ≤ ν i (G i) := hret i
        _ ≤ _ := hdom i _ (hG i).1
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (hm i)).ne'
      ENNReal.ofReal_ne_top).mp hlow

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
