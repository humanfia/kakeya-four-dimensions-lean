-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CoverScaleSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.SplitScales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

theorem IndexedCovers.select_scales {J k q : ℕ} {d θ ζ C ω H B g gap g' gap' : ℝ}
    {T : TubeHierarchy J} {Y : Fin (T.layer (k + 1)).card → Set Space}
    (D : IndexedCovers T k d θ ζ C ω H B Y) (HC : HierarchyControl d θ g gap T)
    (hk : k < J) (hd : 0 < d) (hd1 : d < 1) (hζ : 0 < ζ)
    (hω : 0 ≤ ω / 100) (hω1 : ω / 100 ≤ 1) (hC : 1 ≤ C) (hgap' : 0 ≤ gap')
    (hlarge : (T.layer (k + 1)).radius / (T.layer k).radius ≤ d ^ g')
    (hq : 0 < q) (hspan : d ^ (-2 : ℝ) < (d ^ (-ζ)) ^ q) (hqsmall : (q : ℝ) * d ^ ζ ≤ 1)
    (hCsmall : C ^ 2 * d ≤ 1)
    (hmesh : 1024 * C * d ^ g' ≤ d ^ ((1 - ω / 100) * g))
    (htop : 65536 * C * d ^ (ω / 100 * g') ≤ d ^ gap') :
    ∃ P : Finset (Fin (T.layer k).card), P.Nonempty ∧ ∃ r : ℝ, 0 < r ∧
      d ^ ζ * (T.layer J).card ≤ (Finset.univ.filter (fun i => T.ancestor k i ∈ P)).card ∧
      r ≤ (T.layer k).radius / 64 ∧ (T.layer (k + 1)).radius < r ∧
      d ^ g' * (T.layer k).radius ≤ r ∧ d ^ g' * r ≤ (T.layer (k + 1)).radius ∧
      r ≤ d ^ gap' * (T.layer k).radius ∧ (T.layer (k + 1)).radius ≤ d ^ gap' * r ∧
      ∀ t ∈ P, (T.layer (k + 1)).radius ≤ (D.cover t).radius ∧ (D.cover t).radius ≤ 1 / 160 ∧
        1024 * (D.cover t).radius ≤ r ∧ r ≤ 1024 * d ^ (-ζ) * (D.cover t).radius := by
  classical
  let r₀ := (T.layer k).radius
  let s := (T.layer (k + 1)).radius
  let t := s / r₀
  let c := ω / 100
  let a := r₀ * (t ^ (1 - c) / C)
  let b := r₀ * (C * t ^ c)
  have hr : 0 < r₀ := HC.positive k hk.le
  have hs : 0 < s := HC.positive (k + 1) (by omega)
  have ht : 0 < t := div_pos hs hr
  have ht1 : t < 1 := (div_lt_one hr).mpr (HC.decreasing k hk)
  have hdt : d ≤ t := (HC.ratio_bounds hd.le hk).1
  have hr1 : r₀ ≤ 1 := (HC.radius_bounds hk.le).2
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have ha : 0 < a := mul_pos hr (div_pos (Real.rpow_pos_of_pos ht _) hC0)
  have hρlo (i) : a ≤ (D.cover i).radius := by
    have hh := (D.cover i).scale_lower
    change r₀ * (t ^ (1 - c) / C) ≤ _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hC0).mpr
    simpa only [mul_comm C] using hh
  have hρhi (i) : (D.cover i).radius ≤ b := by
    have hh := (D.cover i).scale_upper
    dsimp only [b]
    nlinarith only [hh]
  have hab : b / a < (d ^ (-ζ)) ^ q := by
    have he : b / a = (C * t ^ c) / (t ^ (1 - c) / C) := by
      dsimp [a, b]
      exact mul_div_mul_left _ _ hr.ne'
    rw [he]
    exact (normalized_scale_span hd ht hdt ht1.le hω hC0 hCsmall).trans_lt hspan
  have hB' : 1 < d ^ (-ζ) := by
    rw [Real.rpow_neg hd.le]
    exact (one_lt_inv₀ (Real.rpow_pos_of_pos hd ζ)).mpr (Real.rpow_lt_one hd.le hd1 hζ)
  obtain ⟨P, hP, r, hrpos, hPcard, hrlo, hrhi, hPr⟩ :=
    synchronize_scales (T.layer J).card_pos (T.ancestor k) (fun t => (D.cover t).radius)
      ha hq hB' hρlo hρhi hab
  have hunlo : 1024 * (t ^ (1 - c) / C) ≤ r / r₀ := (le_div_iff₀ hr).mpr (by
    dsimp only [a] at hrlo
    nlinarith only [hrlo])
  have hunhi : r / r₀ ≤ 1024 * (C * t ^ c) := (div_le_iff₀ hr).mpr (by
    dsimp only [b] at hrhi
    nlinarith only [hrhi])
  have htlo : d ^ g ≤ t := (le_div_iff₀ hr).mpr (HC.lower_gap k hk)
  obtain ⟨hA, hB, hu, hu64, hul, hlu, huh, hhu⟩ := normalized_split_scales
    hd hd1.le ht hω hω1 hC hgap' htlo hlarge hmesh htop hunlo hunhi
  have hst : t * r₀ = s := div_mul_cancel₀ s hr.ne'
  have hru : r / r₀ * r₀ = r := div_mul_cancel₀ r hr.ne'
  have hret : d ^ ζ * (T.layer J).card ≤
      (Finset.univ.filter (fun i => T.ancestor k i ∈ P)).card := by
    calc
      _ ≤ d ^ ζ * ((q : ℝ) * (Finset.univ.filter (fun i => T.ancestor k i ∈ P)).card) :=
        mul_le_mul_of_nonneg_left hPcard (Real.rpow_nonneg hd.le _)
      _ ≤ _ := by
        rw [← mul_assoc]
        have hh := mul_le_mul_of_nonneg_right hqsmall
          (Nat.cast_nonneg (Finset.univ.filter (fun i => T.ancestor k i ∈ P)).card)
        simpa only [one_mul, mul_comm (d ^ ζ) (q : ℝ)] using hh
  refine ⟨P, hP, r, hrpos, hret, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := (div_le_iff₀ hr).mp hu64
    change r ≤ r₀ / 64
    nlinarith only [hh]
  · have htu : t < r / r₀ := by nlinarith only [hA, hunlo, ht]
    have hh := mul_lt_mul_of_pos_right htu hr
    simpa only [hst, hru] using hh
  · exact (le_div_iff₀ hr).mp hul
  · have hh := mul_le_mul_of_nonneg_right hlu hr.le
    simpa only [mul_assoc, hru, hst] using hh
  · exact (div_le_iff₀ hr).mp huh
  · have hh := mul_le_mul_of_nonneg_right hhu hr.le
    simpa only [mul_assoc, hru, hst] using hh
  · intro i hi
    refine ⟨?_, ?_, (hPr i hi).1, (hPr i hi).2⟩
    · have hh : s ≤ a := by
        have hh := mul_le_mul_of_nonneg_right hA hr.le
        dsimp only [a]
        nlinarith only [hh, hst]
      exact hh.trans (hρlo i)
    · have hh : b ≤ 1 / 65536 := by
        have hb0 : 0 ≤ C * t ^ c := by positivity
        calc
          b = r₀ * (C * t ^ c) := rfl
          _ ≤ 1 * (C * t ^ c) := mul_le_mul_of_nonneg_right hr1 hb0
          _ ≤ 1 / 65536 := by simpa only [one_mul] using hB
      have hh' := (hρhi i).trans hh
      linarith

end WangZahlLot.Obl.wz_multiscale_finite_tower
