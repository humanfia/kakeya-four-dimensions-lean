-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_long_grains_gain.LevelBound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_long_grains_gain.CrossBox
import Submission.WZ.Obl.wz_move_two_long_grains_gain.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyRefinement
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_normalized_projection_iteration.Expansion

/-!
# Long grains force a small fibre multiplicity (WZ Move 2, the long-grain case)

Every fine tube of a fibre that meets a grain crosses the grain's box between its
long faces, so it lies in the enlarged box `P (18 a/c) (18 ρ) 4` of volume
`1296 a ρ / c` (`tube_subset_enlarged_box`).  The Katz–Tao condition bounds their
number by `m_KT · 1296 a ρ / (c δ²)`, each meets the grain in volume at most
`1152 c δ²`, and a grain of average mass `δ^h a ρ c²` needs at least `m` of them at
each of its points.  Hence the multiplicity level of frozen grains satisfies

  `m δ^h c² ≤ 1492992 m_KT`.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_long_grains_gain

open MeasureTheory Set Metric
open scoped ENNReal

set_option maxHeartbeats 800000 in
/-- **The multiplicity level of frozen grains is at most `1492992 m_KT δ^(-h) / c²`.** -/
theorem level_le_of_katz_tao {δ η mK l h ρ a c b g m : ℝ} {n N L : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : Fin N → V}
    {f : Fin n → Fin N} {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {G : Fin L → Set V}
    {γ : Fin L → Fin N} {β : Prop}
    (hδ : 0 < δ) (hA : A δ η mK l n x v Y) (hmK : 0 ≤ mK)
    (hC : C δ h n x v Y S Z ρ N y w f β)
    (hH : HB δ h n x v S Z ρ N y w f a c b g L z e G γ m) (h4 : 4 * δ ≤ c) (hL : 0 < L) :
    m * δ ^ h * c ^ 2 ≤ 1492992 * mK := by
  classical
  by_cases hm : m ≤ 0
  · have : m * δ ^ h * c ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hm (by positivity))
        (by positivity)
    linarith
  rw [not_le] at hm
  obtain ⟨hda, hab, hbc, hc1, hgeom, hdisj, hunion, hmassG, hmult, hcross, -, -⟩ := hH
  have ha : 0 < a := hδ.trans_le hda
  have hρc : 0 < ρ * c := ha.trans_le hab
  have hcpos : 0 < c := hρc.trans_le hbc
  have hρ : 0 < ρ := pos_of_mul_pos_left hρc hcpos.le
  have hδc : δ ≤ c := hda.trans (hab.trans hbc)
  have hth : 0 < δ ^ h := Real.rpow_pos_of_pos hδ h
  -- a grain of at least average mass
  have hLne : (Finset.univ : Finset (Fin L)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hL⟩⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, O (δ ^ h * (a * (ρ * c) * c)) ≤ μ (G j₀) := by
    by_contra hcon
    push_neg at hcon
    have hlt := ENNReal.sum_lt_sum_of_nonempty hLne (fun j _ => hcon j)
    have heq : ∑ _j : Fin L, O (δ ^ h * (a * (ρ * c) * c)) =
        O (δ ^ h * L * a * (ρ * c) * c) := by
      rw [sum_const_ofReal]
      congr 1
      ring
    rw [heq] at hlt
    exact absurd hmassG (not_le.mpr hlt)
  -- the enlarged box
  let W := P (18 * a / c) (18 * (ρ * c) / c) 4 (z j₀) (e j₀)
  have hWconv : Convex ℝ W := WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_convex _ _ _ _ _
  have hWvol : μ W = O (18 * a / c * (18 * (ρ * c) / c) * 4) :=
    WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume (by positivity) (by positivity)
      (by norm_num) _ _
  -- the tubes meeting the grain
  let I : Finset (Fin n) :=
    S.filter (fun i => f i = γ j₀ ∧ (Z i ∩ G j₀).Nonempty)
  have hIW : ∀ i ∈ I, T δ (x i) (v i) ⊆ W := by
    intro i hi
    obtain ⟨hiS, hfi, hne⟩ := Finset.mem_filter.mp hi
    obtain ⟨-, -, htwo⟩ := hcross i hiS j₀ hfi hne
    exact tube_subset_enlarged_box (hA.2.1 i).1 hδ hda hab hbc hc1 h4
      (htwo (-c / 2) (by simp)) (htwo (c / 2) (by simp))
  -- Katz-Tao in the enlarged box
  have hKT := hA.2.2.2.2.1 W hWconv
  have hIcard : (I.card : ℝ) ≤ q n {i | T δ (x i) (v i) ⊆ W} := by
    have h0 : (↑I : Set (Fin n)).ncard ≤ ({i | T δ (x i) (v i) ⊆ W} : Set (Fin n)).ncard :=
      Set.ncard_le_ncard (fun i hi => hIW i hi) (Set.toFinite _)
    rw [Set.ncard_coe_finset] at h0
    simp only [q]
    exact_mod_cast h0
  have hKTI : (I.card : ℝ) * δ ^ 2 ≤ mK * (18 * a / c * (18 * (ρ * c) / c) * 4) := by
    have h1 : O ((I.card : ℝ) * δ ^ 2) ≤ O (mK * (18 * a / c * (18 * (ρ * c) / c) * 4)) := by
      calc O ((I.card : ℝ) * δ ^ 2) ≤ O (q n {i | T δ (x i) (v i) ⊆ W} * δ ^ 2) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hIcard (by positivity))
        _ ≤ O mK * μ W := hKT
        _ = O (mK * (18 * a / c * (18 * (ρ * c) / c) * 4)) := by
            rw [hWvol, ← ENNReal.ofReal_mul hmK]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  -- the grain mass is carried by at least `m` tubes of `I` at each point
  let Y₁ : Fin 1 → Set V := fun _ => G j₀
  let Z₁ : Fin n → Set V := fun i => if i ∈ I then Z i ∩ G j₀ else ∅
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hC.1 i).1
  have hZ₁m : ∀ i, MeasurableSet (Z₁ i) := by
    intro i
    by_cases hi : i ∈ I
    · simp only [Z₁, if_pos hi]
      exact (hZm i).inter (hgeom j₀).1
    · simp only [Z₁, if_neg hi]
      exact MeasurableSet.empty
  have hcountp : ∀ p, m * WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount Y₁ p ≤
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount Z₁ p := by
    intro p
    by_cases hp : p ∈ G j₀
    · have hY₁ : WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount Y₁ p = 1 := by
        simp [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount, Y₁, hp]
      have hset : {i : Fin n | p ∈ Z₁ i} = {i | i ∈ S ∧ f i = γ j₀ ∧ p ∈ Z i} := by
        ext i
        simp only [mem_setOf_eq, Z₁]
        constructor
        · intro h
          by_cases hi : i ∈ I
          · rw [if_pos hi] at h
            obtain ⟨hiS, hfi, -⟩ := Finset.mem_filter.mp hi
            exact ⟨hiS, hfi, h.1⟩
          · rw [if_neg hi] at h
            exact h.elim
        · rintro ⟨hiS, hfi, hpZ⟩
          have hi : i ∈ I := Finset.mem_filter.mpr ⟨hiS, hfi, ⟨p, hpZ, hp⟩⟩
          rw [if_pos hi]
          exact ⟨hpZ, hp⟩
      have hfib : p ∈ {p | ∃ i ∈ S, f i = γ j₀ ∧ p ∈ Z i} := by
        rw [← hunion (γ j₀)]
        exact ⟨j₀, rfl, hp⟩
      have hlev := hmult (γ j₀) p hfib
      rw [hY₁, mul_one]
      simp only [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount, hset]
      exact hlev.1
    · have hY₁ : WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount Y₁ p = 0 := by
        simp [WangZahlLot.Obl.wz_clustered_cover_volume_gain.bodyCount, Y₁, hp]
      rw [hY₁, mul_zero]
      exact Nat.cast_nonneg _
  have hmass₁ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.body_mass_le_of_count
    (Y := Y₁) (Z := Z₁) (fun _ => (hgeom j₀).1) hZ₁m hm.le hcountp
  simp only [Y₁, Finset.univ_unique, Finset.sum_singleton] at hmass₁
  -- each tube of `I` meets the grain in volume at most `1152 c δ²`
  have hball : G j₀ ⊆ closedBall (z j₀) c :=
    (hgeom j₀).2.1.trans
      (WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_subset_closedBall hab hbc hcpos.le _ _)
  have hZ₁le : ∀ i, μ (Z₁ i) ≤ if i ∈ I then O (1152 * c * δ ^ 2) else 0 := by
    intro i
    by_cases hi : i ∈ I
    · simp only [Z₁, if_pos hi]
      have hsub : Z i ∩ G j₀ ⊆ T δ (x i) (v i) ∩ closedBall (z j₀) c :=
        fun p hp => ⟨(hA.2.1 i).2.2.2 ((hC.1 i).2.1 hp.1), hball hp.2⟩
      exact (measure_mono hsub).trans
        (WangZahlLot.Obl.wz_normalized_projection_iteration.tube_inter_ball_volume_le hδ hδc
          (x i) (v i) (z j₀) (hA.2.1 i).1)
    · simp only [Z₁, if_neg hi]
      exact le_of_eq measure_empty
  have hsum₁ : ∑ i, μ (Z₁ i) ≤ O (I.card * (1152 * c * δ ^ 2)) := by
    calc ∑ i, μ (Z₁ i) ≤ ∑ i, (if i ∈ I then O (1152 * c * δ ^ 2) else 0) :=
          Finset.sum_le_sum fun i _ => hZ₁le i
      _ = ∑ i ∈ I, O (1152 * c * δ ^ 2) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = O (I.card * (1152 * c * δ ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp only [O]
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  -- combine
  have hchain : O (m * (δ ^ h * (a * (ρ * c) * c))) ≤ O (I.card * (1152 * c * δ ^ 2)) := by
    calc O (m * (δ ^ h * (a * (ρ * c) * c))) = O m * O (δ ^ h * (a * (ρ * c) * c)) :=
          ENNReal.ofReal_mul hm.le
      _ ≤ O m * μ (G j₀) := mul_le_mul' le_rfl hj₀
      _ ≤ ∑ i, μ (Z₁ i) := hmass₁
      _ ≤ _ := hsum₁
  have hreal : m * (δ ^ h * (a * (ρ * c) * c)) ≤ I.card * (1152 * c * δ ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  -- `I.card δ² ≤ 1296 m_KT a ρ / c`
  have hvolW : 18 * a / c * (18 * (ρ * c) / c) * 4 = 1296 * a * ρ / c := by
    field_simp
    ring
  rw [hvolW] at hKTI
  have hfinal : m * δ ^ h * c ^ 2 * (a * ρ) ≤ 1492992 * mK * (a * ρ) := by
    have e1 : m * δ ^ h * c ^ 2 * (a * ρ) = m * (δ ^ h * (a * (ρ * c) * c)) := by ring
    have e2 : (I.card : ℝ) * (1152 * c * δ ^ 2) = 1152 * c * ((I.card : ℝ) * δ ^ 2) := by ring
    have e3 : 1152 * c * (mK * (1296 * a * ρ / c)) = 1492992 * mK * (a * ρ) := by
      field_simp
      ring
    calc m * δ ^ h * c ^ 2 * (a * ρ) = m * (δ ^ h * (a * (ρ * c) * c)) := e1
      _ ≤ (I.card : ℝ) * (1152 * c * δ ^ 2) := hreal
      _ = 1152 * c * ((I.card : ℝ) * δ ^ 2) := e2
      _ ≤ 1152 * c * (mK * (1296 * a * ρ / c)) :=
          mul_le_mul_of_nonneg_left hKTI (by positivity)
      _ = 1492992 * mK * (a * ρ) := e3
  exact le_of_mul_le_mul_right hfinal (by positivity)

end WangZahlLot.Obl.wz_move_two_long_grains_gain
