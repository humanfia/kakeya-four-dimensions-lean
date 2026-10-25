-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Slabs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Strong

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- An invertible affine preimage of a slab is again a slab with a unit normal. -/
theorem affine_slab_preimage (F : AffineEquiv ℝ Space Space) (u : Space) (t s : ℝ)
    (hu : ‖u‖ = 1) (hs : 0 < s) :
    ∃ (u' : Space) (t' s' : ℝ), ‖u'‖ = 1 ∧ 0 < s' ∧
      F ⁻¹' {p | |inner ℝ u p - t| ≤ s} = {p | |inner ℝ u' p - t'| ≤ s'} := by
  let a : Space := LinearMap.adjoint F.linear.toLinearMap u
  have ha : ∀ p, inner ℝ a p = inner ℝ u (F.linear p) :=
    fun p => LinearMap.adjoint_inner_left F.linear.toLinearMap p u
  have ha0 : a ≠ 0 := by
    intro hz
    have h := ha (F.linear.symm u)
    rw [hz, inner_zero_left, F.linear.apply_symm_apply, real_inner_self_eq_norm_sq, hu] at h
    norm_num at h
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let u' : Space := ‖a‖⁻¹ • a
  let t' : ℝ := (t - inner ℝ u (F 0)) / ‖a‖
  have hunit : ‖u'‖ = 1 := by
    dsimp [u']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  refine ⟨u', t', s / ‖a‖, hunit, div_pos hs hnorm, ?_⟩
  have hFp (p : Space) : F p = F.linear p + F 0 := by
    simpa only [vadd_eq_add, add_zero] using F.map_vadd (0 : Space) p
  have he (p : Space) : inner ℝ u' p - t' = (inner ℝ u (F p) - t) / ‖a‖ := by
    dsimp [u', t']
    rw [real_inner_smul_left, ha, hFp p, inner_add_right]
    field_simp
    ring
  ext p
  change |inner ℝ u (F p) - t| ≤ s ↔ |inner ℝ u' p - t'| ≤ s / ‖a‖
  rw [he, abs_div, abs_of_pos hnorm]
  exact (div_le_div_iff_of_pos_right hnorm).symm

/-- Relative slab counts survive affine normalization and enlargement to exact round tubes.
The normalization cost is the reciprocal volume of the transformed parent container. -/
theorem relative_slab_affine_transport {d d' L J c : ℝ} {n : ℕ}
    (F : AffineEquiv ℝ Space Space) (x v x' v' : Fin n → Space) (U : Set Space)
    (hc : 0 < c)
    (hvol : ∀ W : Set Space, volume (F '' W) = ENNReal.ofReal J * volume W)
    (hU : ∀ i, Tube d (x i) (v i) ⊆ U)
    (hFU : F '' U ⊆ Metric.ball 0 1)
    (hcv : ENNReal.ofReal c ≤ volume (F '' U))
    (hcontain : ∀ i, F '' Tube d (x i) (v i) ⊆ Tube d' (x' i) (v' i))
    (hR : RelativeSlab d L x v (fun _ => True) U) : Frostman d' (L / c) n x' v' := by
  intro u t s hu hs
  obtain ⟨u0, t0, s0, hu0, hs0, hpre⟩ := affine_slab_preimage F u t s hu hs
  let S : Set Space := {p | |inner ℝ u p - t| ≤ s}
  let S0 : Set Space := {p | |inner ℝ u0 p - t0| ≤ s0}
  change F ⁻¹' S = S0 at hpre
  have hcount : Set.ncard {i | Tube d' (x' i) (v' i) ⊆ Metric.ball 0 1 ∩ S} ≤
      Set.ncard {i | Tube d (x i) (v i) ⊆ U ∩ S0} := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro i hi p hp
    refine ⟨hU i hp, ?_⟩
    have hh : F p ∈ S := (hi (hcontain i ⟨p, hp, rfl⟩)).2
    exact hpre ▸ (show p ∈ F ⁻¹' S from hh)
  have hr := hR u0 t0 s0 hu0 hs0
  simp only [true_and, Set.ofPred_true, Set.ncard_univ, Nat.card_fin] at hr
  have himage : F '' (U ∩ S0) ⊆ Metric.ball 0 1 ∩ S := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨hFU ⟨p, hp.1, rfl⟩, ?_⟩
    have : p ∈ F ⁻¹' S := hpre.symm ▸ hp.2
    exact this
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal c * ENNReal.ofReal
        (Set.ncard {i | Tube d' (x' i) (v' i) ⊆ Metric.ball 0 1 ∩ S} : ℝ) ≤
        volume (F '' U) * ENNReal.ofReal
        (Set.ncard {i | Tube d (x i) (v i) ⊆ U ∩ S0} : ℝ) := by gcongr
    _ = ENNReal.ofReal J * (ENNReal.ofReal
        (Set.ncard {i | Tube d (x i) (v i) ⊆ U ∩ S0} : ℝ) * volume U) := by
      rw [hvol]
      ac_rfl
    _ ≤ ENNReal.ofReal J * (ENNReal.ofReal (L * n) * volume (U ∩ S0)) := mul_le_mul' le_rfl hr
    _ = ENNReal.ofReal (L * n) * volume (F '' (U ∩ S0)) := by rw [hvol]; ac_rfl
    _ ≤ ENNReal.ofReal (L * n) * volume (Metric.ball 0 1 ∩ S) := by gcongr
    _ = ENNReal.ofReal c * (ENNReal.ofReal (L / c * n) * volume (Metric.ball 0 1 ∩ S)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le]
      congr 2
      field_simp

end WangZahlLot.Obl.wz_multiscale_finite_tower
