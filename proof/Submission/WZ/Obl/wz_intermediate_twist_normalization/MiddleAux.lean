-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.MiddleAux.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Truncation
import Submission.WZ.Obl.wz_intermediate_twist_normalization.NoBad

/-!
# Removed mass of the truncation

* `removed_mass`: the mass removed by the truncation is at most the sum over the classes `k`
  of the masses `R_k` of the shadings of the enlarged class `k` over `clG k`.
* `markov_clG`: `λ |clG k| ≤ R_k`.
* `volume_tube_le`, `volume_tube_diff_nwin_le`: volumes of a tube and of its part outside the
  height window of its normalized tube.
* `class_mass_le`: with the threshold `λ = 288 C Kt Z δ² ρ^(-ε)`, the black box forbids dense
  classes, so `R_k ≤ |J| δ² (200 ρ^η' + 288 (e + δ))`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj CountF fib
  measurable_fib volume_eq_lintegral_fib)
open WangZahlLot.Obl.wz_compact_offset_normalization (mem_tube_iff abs_coord_le_norm)

section

variable {n : ℕ} {f : ℝ → ℝ} {x v : Fin n → Space} {Y : Fin n → Set Space}

/-- The mass of a class over its high-multiplicity set. -/
noncomputable def clR (f : ℝ → ℝ) (lam : ℝ) (x v : Fin n → Space) (Y : Fin n → Set Space)
    (k : ℤ × ℤ) : ℝ≥0∞ :=
  ∑ j ∈ clSet (f 0) x v k, volume (Y j ∩ pmap f ⁻¹' clG f lam x v Y k)

/-- The set of class indices. -/
noncomputable def clIdxSet (f : ℝ → ℝ) (x v : Fin n → Space) : Finset (ℤ × ℤ) :=
  Finset.univ.image (fun i => clIdx (f 0) (x i) (v i))

/-- **The removed mass.** -/
theorem removed_mass (hf : Continuous f) (hYm : ∀ i, MeasurableSet (Y i)) (lam : ℝ) :
    ∑ i, volume (Y i) ≤ ∑ i, volume (trY f lam x v Y i) +
      ∑ k ∈ clIdxSet f x v, clR f lam x v Y k := by
  classical
  have hsplit : ∀ i, volume (Y i) = volume (trY f lam x v Y i) +
      volume (Y i ∩ pmap f ⁻¹' clG f lam x v Y (clIdx (f 0) (x i) (v i))) := by
    intro i
    have hm : MeasurableSet (pmap f ⁻¹' lowSet f lam x v Y (clIdx (f 0) (x i) (v i))) :=
      (measurableSet_lowSet hf hYm lam _).preimage (continuous_pmap hf).measurable
    rw [← measure_inter_add_diff (Y i) hm, trY]
    congr 2
    rw [diff_eq, ← preimage_compl, compl_lowSet]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib]
  gcongr
  rw [clIdxSet, ← Finset.sum_fiberwise_of_maps_to
    (g := fun i => clIdx (f 0) (x i) (v i)) (t := Finset.univ.image _)
    (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [clR]
  calc ∑ i ∈ Finset.univ.filter (fun i => clIdx (f 0) (x i) (v i) = k),
        volume (Y i ∩ pmap f ⁻¹' clG f lam x v Y (clIdx (f 0) (x i) (v i)))
      = ∑ i ∈ Finset.univ.filter (fun i => clIdx (f 0) (x i) (v i) = k),
          volume (Y i ∩ pmap f ⁻¹' clG f lam x v Y k) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ clSet (f 0) x v k, volume (Y j ∩ pmap f ⁻¹' clG f lam x v Y k) := by
        apply Finset.sum_le_sum_of_subset
        intro i hi
        have := mem_clSet_self (f 0) x v i
        rwa [(Finset.mem_filter.mp hi).2] at this

/-- **Markov's inequality for the near multiplicity.** -/
theorem markov_clG (hf : Continuous f) (hYm : ∀ i, MeasurableSet (Y i)) (lam : ℝ)
    (k : ℤ × ℤ) :
    ENNReal.ofReal lam * volume (clG f lam x v Y k) ≤ clR f lam x v Y k := by
  classical
  have hG := measurableSet_clG (x := x) (v := v) hf hYm lam k
  rw [clR]
  have h1 : ∀ j, volume (Y j ∩ pmap f ⁻¹' clG f lam x v Y k) =
      ∫⁻ q, (clG f lam x v Y k).indicator (fib f (Y j)) q := fun j =>
    volume_inter_pmap_preimage hf (hYm j) hG
  simp_rw [h1]
  rw [← lintegral_finsetSum _ (fun j _ => (measurable_fib hf (hYm j)).indicator hG),
    ← lintegral_indicator_const hG]
  refine lintegral_mono fun q => ?_
  by_cases hq : q ∈ clG f lam x v Y k
  · rw [indicator_of_mem hq]
    simp_rw [indicator_of_mem hq]
    exact hq.le
  · rw [indicator_of_notMem hq]
    exact zero_le

/-- Version of the band estimate without an order hypothesis. -/
theorem volume_tube_band_le' {δ : ℝ} (hδ : 0 < δ) {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (a b : ℝ) :
    volume (tube δ x v ∩ hband a b) ≤ ENNReal.ofReal (72 * δ ^ 2 * (b - a)) := by
  rcases le_total a b with hab | hab
  · exact volume_tube_band_le hδ hv hv2 hab
  · rcases eq_or_lt_of_le hab with h | h
    · subst h; exact volume_tube_band_le hδ hv hv2 le_rfl
    · have : tube δ x v ∩ hband a b = ∅ := by
        ext p
        simp only [hband, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
        intro ⟨_, h1, h2⟩
        linarith
      rw [this, measure_empty]
      exact zero_le

/-- The volume of a transverse tube in the unit ball. -/
theorem volume_tube_le {δ : ℝ} (hδ : 0 < δ) {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hT : tube δ x v ⊆ ball 0 1) :
    volume (tube δ x v) ≤ ENNReal.ofReal (144 * δ ^ 2) := by
  have hsub : tube δ x v ⊆ tube δ x v ∩ hband (-1) 1 := by
    intro p hp
    refine ⟨hp, ?_⟩
    have h1 := mem_ball_zero_iff.mp (hT hp)
    have h2 := (abs_coord_le_norm p 2).trans_lt h1
    exact ⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩
  calc volume (tube δ x v) ≤ volume (tube δ x v ∩ hband (-1) 1) := measure_mono hsub
    _ ≤ ENNReal.ofReal (72 * δ ^ 2 * (1 - -1)) := volume_tube_band_le' hδ hv hv2 _ _
    _ = ENNReal.ofReal (144 * δ ^ 2) := by congr 1; ring

/-- The part of a tube outside the window of its normalized tube is small. -/
theorem CG.volume_tube_diff_nwin_le {c δ Z ρ e r0 α β : ℝ} {x v : Space}
    (h : CG c δ Z ρ e r0 α β x v) :
    volume (tube δ x v \ nwin Z c β ρ e δ x v) ≤ ENNReal.ofReal (288 * δ ^ 2 * (e + δ)) := by
  obtain ⟨hA, hB, hC, hD⟩ := h.nhb_bounds
  obtain ⟨hu1, hu2⟩ := h.nuz_bounds
  have hδ := h.hδ
  have he0 : 0 ≤ e := by have := h.he16; have := h.hr0; nlinarith
  have heu : 2 * e * nuz Z c β v ≤ 2 * e := by nlinarith
  have hsub : tube δ x v \ nwin Z c β ρ e δ x v ⊆
      (tube δ x v ∩ hband (nzlo x v - δ) (nhb Z c β ρ e x v + δ)) ∪
        (tube δ x v ∩ hband (nhb Z c β ρ e x v + nuz Z c β v - δ) (nzlo x v + |v 2| + δ)) := by
    intro p ⟨hp, hpw⟩
    obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
    obtain ⟨-, -, hq1, hq2⟩ := h.height_bounds ht
    have hpq : |p 2 - (x + t • v) 2| < δ := by
      have := abs_coord_le_norm (p - (x + t • v)) 2
      rw [PiLp.sub_apply] at this
      rw [dist_eq_norm] at hpt
      linarith
    obtain ⟨hl, hu⟩ := abs_lt.mp hpq
    simp only [nwin, mem_setOf_eq, not_and_or, not_le] at hpw
    rcases hpw with hw | hw
    · left
      exact ⟨hp, by linarith, hw.le⟩
    · right
      exact ⟨hp, hw.le, by linarith⟩
  have hb1 : 72 * δ ^ 2 * (nhb Z c β ρ e x v + δ - (nzlo x v - δ)) ≤ 144 * δ ^ 2 * (e + δ) := by
    have h1 : nhb Z c β ρ e x v + δ - (nzlo x v - δ) ≤ 2 * (e + δ) := by linarith
    have h2 : 0 ≤ 72 * δ ^ 2 := by positivity
    nlinarith
  have hb2 : 72 * δ ^ 2 * (nzlo x v + |v 2| + δ - (nhb Z c β ρ e x v + nuz Z c β v - δ)) ≤
      144 * δ ^ 2 * (e + δ) := by
    have h1 : nzlo x v + |v 2| + δ - (nhb Z c β ρ e x v + nuz Z c β v - δ) ≤ 2 * (e + δ) := by
      linarith
    have h2 : 0 ≤ 72 * δ ^ 2 := by positivity
    nlinarith
  calc volume (tube δ x v \ nwin Z c β ρ e δ x v)
      ≤ volume (tube δ x v ∩ hband (nzlo x v - δ) (nhb Z c β ρ e x v + δ)) +
          volume (tube δ x v ∩
            hband (nhb Z c β ρ e x v + nuz Z c β v - δ) (nzlo x v + |v 2| + δ)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (144 * δ ^ 2 * (e + δ)) + ENNReal.ofReal (144 * δ ^ 2 * (e + δ)) :=
        add_le_add ((volume_tube_band_le' hδ h.hv h.hv2 _ _).trans (ENNReal.ofReal_le_ofReal hb1))
          ((volume_tube_band_le' hδ h.hv h.hv2 _ _).trans (ENNReal.ofReal_le_ofReal hb2))
    _ = ENNReal.ofReal (288 * δ ^ 2 * (e + δ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **No dense class.** -/
theorem class_mass_le {εG ηG dG CG' : ℝ} (hGB : GBeAt εG ηG dG CG') (hCG' : 0 < CG')
    {η δ : ℝ} (hYm : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ tube δ (x i) (v i))
    (hF : CountF η δ n x v) (hf : SlopeN f)
    {Z ρ e r0 : ℝ} (k : ℤ × ℤ) (hJ : (clSet (f 0) x v k).Nonempty)
    (hCG : ∀ j ∈ clSet (f 0) x v k,
      CG (f 0) δ Z ρ e r0 (clα (f 0) k) (clβ (f 0) k) (x j) (v j))
    (hρd : ρ ≤ dG) (hρr : ρ ^ ηG ≤ r0) (hn : 0 < n) :
    clR f (288 * CG' * (δ ^ (-η) * n / Z ^ 2) * Z * δ ^ 2 * ρ ^ (-εG)) x v Y k ≤
      ENNReal.ofReal ((clSet (f 0) x v k).card * (δ ^ 2 * (200 * ρ ^ ηG + 288 * (e + δ)))) := by
  classical
  set J := clSet (f 0) x v k with hJdef
  set Kt := δ ^ (-η) * n / Z ^ 2 with hKt
  set lam := 288 * CG' * Kt * Z * δ ^ 2 * ρ ^ (-εG) with hlam
  set G := clG f lam x v Y k with hGdef
  have hfc : Continuous f := hf.continuous
  have hGm : MeasurableSet G := measurableSet_clG hfc hYm lam k
  obtain ⟨j0, hj0⟩ := hJ
  have h0 := hCG j0 hj0
  have hZ := h0.hZ
  have hδ := h0.hδ
  have hρ0 : 0 < ρ := by rw [h0.hρ]; have := h0.hc; positivity
  have hm : (0 : ℝ) < J.card := by exact_mod_cast Finset.card_pos.mpr ⟨j0, hj0⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hKt0 : 0 < Kt := div_pos (mul_pos (Real.rpow_pos_of_pos hδ _) hn0) (by positivity)
  have hlam0 : 0 < lam := by rw [hlam]; have := Real.rpow_pos_of_pos hρ0 (-εG); positivity
  -- the parts of the shadings inside the windows are not dense
  have hsparse : ∑ j ∈ J, volume (clPart f Z (clβ (f 0) k) ρ e δ G (x j) (v j) (Y j)) <
      ENNReal.ofReal (200 * ρ ^ ηG * (J.card : ℝ) * δ ^ 2) := by
    by_contra hdense
    push Not at hdense
    have hcb := class_bound hGB hYm hYT hF hf J ⟨j0, hj0⟩ hCG hρd hρr hGm hdense
    -- the high-multiplicity set is small
    have hR : clR f lam x v Y k ≤ ENNReal.ofReal (J.card * (144 * δ ^ 2)) := by
      rw [clR]
      calc ∑ j ∈ J, volume (Y j ∩ pmap f ⁻¹' G)
          ≤ ∑ j ∈ J, ENNReal.ofReal (144 * δ ^ 2) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hh := hCG j hj
            exact (measure_mono (inter_subset_left.trans (hYT j))).trans
              (volume_tube_le hδ hh.hv hh.hv2 hh.hT)
        _ = ENNReal.ofReal (J.card * (144 * δ ^ 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
    have hmk := markov_clG hfc hYm lam k (x := x) (v := v)
    have hGle : volume G ≤ ENNReal.ofReal (J.card * (144 * δ ^ 2) / lam) := by
      rw [ENNReal.ofReal_div_of_pos hlam0, ENNReal.le_div_iff_mul_le
        (Or.inl (by simpa using hlam0)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact hmk.trans hR
    have hchain : ENNReal.ofReal (ρ ^ εG * (J.card : ℝ)) ≤
        ENNReal.ofReal (CG' * Kt * Z * (J.card * (144 * δ ^ 2) / lam)) := by
      calc ENNReal.ofReal (ρ ^ εG * (J.card : ℝ))
          ≤ ENNReal.ofReal (CG' * Kt) * (ENNReal.ofReal Z * volume G) := hcb
        _ ≤ ENNReal.ofReal (CG' * Kt) * (ENNReal.ofReal Z *
              ENNReal.ofReal (J.card * (144 * δ ^ 2) / lam)) := by gcongr
        _ = ENNReal.ofReal (CG' * Kt * Z * (J.card * (144 * δ ^ 2) / lam)) := by
            rw [← ENNReal.ofReal_mul hZ.le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
    have hρε : ρ ^ (-εG) * ρ ^ εG = 1 := by
      rw [← Real.rpow_add hρ0]; simp
    have : CG' * Kt * Z * (J.card * (144 * δ ^ 2) / lam) = ρ ^ εG * J.card / 2 := by
      rw [hlam]
      have hρpos : 0 < ρ ^ εG := Real.rpow_pos_of_pos hρ0 _
      have hρn : ρ ^ (-εG) = (ρ ^ εG)⁻¹ := Real.rpow_neg hρ0.le _
      rw [hρn]
      field_simp
      ring
    rw [this] at hchain
    have hpos : 0 < ρ ^ εG * J.card := mul_pos (Real.rpow_pos_of_pos hρ0 _) hm
    linarith
  -- the mass over the high-multiplicity set
  rw [clR]
  calc ∑ j ∈ J, volume (Y j ∩ pmap f ⁻¹' G)
      ≤ ∑ j ∈ J, (volume (clPart f Z (clβ (f 0) k) ρ e δ G (x j) (v j) (Y j)) +
          ENNReal.ofReal (288 * δ ^ 2 * (e + δ))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hh := hCG j hj
        have hsub : Y j ∩ pmap f ⁻¹' G ⊆ clPart f Z (clβ (f 0) k) ρ e δ G (x j) (v j) (Y j) ∪
            (tube δ (x j) (v j) \ nwin Z (f 0) (clβ (f 0) k) ρ e δ (x j) (v j)) := by
          intro p hp
          by_cases hw : p ∈ nwin Z (f 0) (clβ (f 0) k) ρ e δ (x j) (v j)
          · exact Or.inl ⟨hp, hw⟩
          · exact Or.inr ⟨hYT j hp.1, hw⟩
        exact (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl hh.volume_tube_diff_nwin_le))
    _ = ∑ j ∈ J, volume (clPart f Z (clβ (f 0) k) ρ e δ G (x j) (v j) (Y j)) +
          J.card * ENNReal.ofReal (288 * δ ^ 2 * (e + δ)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (200 * ρ ^ ηG * (J.card : ℝ) * δ ^ 2) +
          J.card * ENNReal.ofReal (288 * δ ^ 2 * (e + δ)) :=
        add_le_add hsparse.le le_rfl
    _ = ENNReal.ofReal ((J.card : ℝ) * (δ ^ 2 * (200 * ρ ^ ηG + 288 * (e + δ)))) := by
        have he0 : 0 ≤ e := by have := h0.he16; have := h0.hr0; nlinarith
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end

end WangZahlLot.Obl.wz_intermediate_twist_normalization
