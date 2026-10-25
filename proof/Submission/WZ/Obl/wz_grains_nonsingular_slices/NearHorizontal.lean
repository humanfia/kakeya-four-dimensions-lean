-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.NearHorizontal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.ShearFubini

/-!
# Nearly horizontal tubes carry little mass

A nearly horizontal tube either crosses the global grains, and then its shading is sparse by
the AD estimate on twisted slices, or it runs along the grains, and then the AD estimate at a
fixed height packs too many such tubes into a thin convex box.

Write `γ = √θ`, `E = ⋃ i, Y i`, and for a tube `i` let `φᵢ = |v i 0 + f (x i 2) * v i 1|` be
its transversality to the grain direction `(-f z, 1, 0)` at its base height.
All estimates are made on horizontal slices through the shear Fubini formula
`volume A = ∫⁻ z, ∫⁻ u, volume (grainFib f A u z)`.

* For a tube with `|v i 2| < θ` and `φᵢ ≥ γ`, at every height of the tube the grain fibres are
  `≲ δ / γ` long, the twisted positions lie in an interval of length `≲ φ δ / max |v i 2| δ`,
  and only those in `PS f E z` contribute; the AD estimate at scale `δ` gives
  `volume (Y i) ≲ δ ^ (-η) δ ² (θ / γ) ^ σ` (`nh_trans_tube`).
* For the tubes with `φᵢ < γ`, at a fixed height `z` the AD estimate at scale `γ` covers the
  twisted positions by `≲ δ ^ (-η) γ ^ (σ - 1)` intervals, and each tube through height `z`
  with `|v i 2| ≤ t` lies in a convex box of volume `≲ t γ` around one of them, so there are
  `≲ δ ^ (-2η) n γ ^ σ t` of them (`nh_count`).  The slice areas are `≲ δ² / max |v i 2| δ`,
  and a dyadic summation over `|v i 2|` (`nh_dyadic`) costs the logarithmic factor.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-! ### Elementary geometry of a tube in twisted coordinates -/

/-- A set of reals of small diameter has small measure. -/
lemma nh_volume_le_of_abs {S : Set ℝ} {D : ℝ} (h : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ D) :
    volume S ≤ ENNReal.ofReal D :=
  (Real.volume_le_diam S).trans (ediam_le_of_forall_dist_le fun x hx y hy => by
    rw [Real.dist_eq]; exact h x hx y hy)

lemma nh_abs_coord_le (p : Space) (k : Fin 3) : |p k| ≤ ‖p‖ := PiLp.norm_apply_le p k

lemma nh_abs_coord_v {v : Space} (hv : ‖v‖ = 1) (k : Fin 3) : |v k| ≤ 1 :=
  (nh_abs_coord_le v k).trans hv.le

lemma nh_abs_coord_ball {p : Space} (hp : p ∈ ball (0:Space) 1) (k : Fin 3) : |p k| < 1 :=
  (nh_abs_coord_le p k).trans_lt (by simpa using hp)

lemma nh_mem_tube_self {δ : ℝ} (hδ : 0 < δ) (x v : Space) : x ∈ Tube δ x v :=
  self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))

/-- Coordinates of a point of a tube. -/
lemma nh_coords {δ : ℝ} {x v p : Space} (hp : p ∈ Tube δ x v) :
    ∃ τ ∈ Icc (0:ℝ) 1, ∀ k : Fin 3, |p k - (x k + τ * v k)| < δ := by
  obtain ⟨τ, hτ, hpt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  refine ⟨τ, hτ, fun k => ?_⟩
  have h := nh_abs_coord_le (p - (x + τ • v)) k
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
  exact h.trans_lt hpt

lemma nh_abs_lin {X c d E : ℝ} (h : X = c + d) (hd : |d| ≤ E) :
    |X| ≤ |c| + E ∧ |c| ≤ |X| + E := by
  constructor
  · rw [h]; exact (abs_add_le c d).trans (by linarith)
  · have : c = X + (-d) := by rw [h]; ring
    rw [this]; exact (abs_add_le X (-d)).trans (by rw [abs_neg]; linarith)

/-- Two points of a tube: their parameters differ by `Δ ≤ 1`, and linear coordinates
differ by `Δ` times the corresponding coordinate of the direction, up to `O(δ)`. -/
lemma nh_pair {δ F : ℝ} {x v p p' : Space} (hv : ‖v‖ = 1) (hF : |F| ≤ 1)
    (hp : p ∈ Tube δ x v) (hp' : p' ∈ Tube δ x v) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ Δ ≤ 1 ∧
      |p 2 - p' 2| ≤ Δ * |v 2| + 2 * δ ∧ Δ * |v 2| ≤ |p 2 - p' 2| + 2 * δ ∧
      |(p 0 + F * p 1) - (p' 0 + F * p' 1)| ≤ Δ * |v 0 + F * v 1| + 4 * δ ∧
      Δ * |v 0 + F * v 1| ≤ |(p 0 + F * p 1) - (p' 0 + F * p' 1)| + 4 * δ ∧
      |p 1 - p' 1| ≤ Δ + 2 * δ := by
  obtain ⟨τ, hτ, hp⟩ := nh_coords hp
  obtain ⟨τ', hτ', hp'⟩ := nh_coords hp'
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2
  have h0' := hp' 0; have h1' := hp' 1; have h2' := hp' 2
  set A0 := p 0 - (x 0 + τ * v 0)
  set A1 := p 1 - (x 1 + τ * v 1)
  set A2 := p 2 - (x 2 + τ * v 2)
  set B0 := p' 0 - (x 0 + τ' * v 0)
  set B1 := p' 1 - (x 1 + τ' * v 1)
  set B2 := p' 2 - (x 2 + τ' * v 2)
  have hΔ : |τ - τ'| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2],
    by linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]⟩
  refine ⟨|τ - τ'|, abs_nonneg _, hΔ, ?_⟩
  have hd2 : |A2 - B2| ≤ 2 * δ := (abs_sub _ _).trans (by linarith)
  have hd1 : |A1 - B1| ≤ 2 * δ := (abs_sub _ _).trans (by linarith)
  have hd0 : |(A0 - B0) + F * (A1 - B1)| ≤ 4 * δ := by
    calc |(A0 - B0) + F * (A1 - B1)| ≤ |A0 - B0| + |F| * |A1 - B1| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 * δ + 1 * (2 * δ) := by
          gcongr
          · exact (abs_sub _ _).trans (by linarith)
      _ = 4 * δ := by ring
  have e2 : p 2 - p' 2 = (τ - τ') * v 2 + (A2 - B2) := by simp only [A2, B2]; ring
  have e1 : p 1 - p' 1 = (τ - τ') * v 1 + (A1 - B1) := by simp only [A1, B1]; ring
  have e0 : (p 0 + F * p 1) - (p' 0 + F * p' 1) =
      (τ - τ') * (v 0 + F * v 1) + ((A0 - B0) + F * (A1 - B1)) := by
    simp only [A0, A1, B0, B1]; ring
  have k2 := nh_abs_lin e2 hd2
  have k1 := nh_abs_lin e1 hd1
  have k0 := nh_abs_lin e0 hd0
  rw [abs_mul] at k2 k1 k0
  have hv1 : |τ - τ'| * |v 1| ≤ |τ - τ'| :=
    mul_le_of_le_one_right (abs_nonneg _) (nh_abs_coord_v hv 1)
  exact ⟨k2.1, k2.2, k0.1, k0.2, by linarith [k1.1]⟩

/-- The grain fibres of a tube at a fixed height are short. -/
lemma nh_fibre_le {δ D z u : ℝ} {f : ℝ → ℝ} {x v : Space} (hv : ‖v‖ = 1) (hF : |f z| ≤ 1)
    (hD : ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ 1 → Δ * |v 2| ≤ 2 * δ → Δ * |v 0 + f z * v 1| ≤ 4 * δ →
      Δ + 2 * δ ≤ D) :
    volume (grainFib f (Tube δ x v) u z) ≤ ENNReal.ofReal D := by
  apply nh_volume_le_of_abs
  intro y hy y' hy'
  rw [mem_grainFib] at hy hy'
  obtain ⟨Δ, h0, h1, -, h2b, -, h0b, h1a⟩ := nh_pair (F := f z) hv hF hy hy'
  simp only [ofTwist_zero, ofTwist_one, ofTwist_two, sub_self, abs_zero, zero_add] at h2b h0b h1a
  have e : u - f z * y + f z * y - (u - f z * y' + f z * y') = 0 := by ring
  rw [e, abs_zero, zero_add] at h0b
  exact h1a.trans (hD Δ h0 h1 h2b h0b)

/-- The twisted positions of a tube at a fixed height form a short interval. -/
lemma nh_PS_diam {δ R z : ℝ} {f : ℝ → ℝ} {x v : Space} (hv : ‖v‖ = 1) (hF : |f z| ≤ 1)
    (hR : ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ 1 → Δ * |v 2| ≤ 2 * δ →
      Δ * |v 0 + f z * v 1| + 4 * δ ≤ R) :
    ∀ u ∈ PS f (Tube δ x v) z, ∀ u' ∈ PS f (Tube δ x v) z, |u - u'| ≤ R := by
  intro u hu u' hu'
  obtain ⟨y, hy⟩ := mem_PS_iff.mp hu
  obtain ⟨y', hy'⟩ := mem_PS_iff.mp hu'
  rw [mem_grainFib] at hy hy'
  obtain ⟨Δ, h0, h1, -, h2b, h0a, -, -⟩ := nh_pair (F := f z) hv hF hy hy'
  simp only [ofTwist_zero, ofTwist_one, ofTwist_two, sub_self, abs_zero, zero_add] at h2b h0a
  have e : u - f z * y + f z * y - (u' - f z * y' + f z * y') = u - u' := by ring
  rw [e] at h0a
  exact h0a.trans (hR Δ h0 h1 h2b)

/-- The twisted slice area of a shading is controlled by the fibre length of the tube times
the measure of the relevant twisted positions. -/
lemma nh_slice_le {f : ℝ → ℝ} {S E T : Set Space} {D z : ℝ} (hST : S ⊆ T) (hSE : S ⊆ E)
    (hD : ∀ u, volume (grainFib f T u z) ≤ ENNReal.ofReal D) :
    ∫⁻ u, volume (grainFib f S u z) ≤ ENNReal.ofReal D * volume (PS f E z ∩ PS f T z) := by
  refine le_trans (lintegral_mono fun u => ?_) (lintegral_indicator_const_le _ _)
  by_cases hu : u ∈ PS f E z ∩ PS f T z
  · rw [indicator_of_mem hu]
    exact (measure_mono (grainFib_mono hST u z)).trans (hD u)
  · rw [indicator_of_notMem hu]
    have he : grainFib f S u z = ∅ := by
      by_contra hne
      obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr hne
      exact hu ⟨mem_PS_iff.mpr ⟨y, hSE hy⟩, mem_PS_iff.mpr ⟨y, hST hy⟩⟩
    rw [he, measure_empty]

/-- A slice of `S` vanishes at heights not attained by `S`. -/
lemma nh_slice_eq_zero {f : ℝ → ℝ} {S : Set Space} {z : ℝ} (h : ¬ ∃ p ∈ S, p 2 = z) :
    ∫⁻ u, volume (grainFib f S u z) = 0 := by
  have he : ∀ u, grainFib f S u z = ∅ := by
    intro u
    by_contra hne
    obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr hne
    exact h ⟨_, hy, by simp⟩
  simp [he]

/-- Integrating slice bounds over the height range of a tube. -/
lemma nh_lintegral_height_le {f : ℝ → ℝ} {S T : Set Space} (hST : S ⊆ T) {A H : ℝ}
    (hH : ∀ p ∈ T, ∀ p' ∈ T, |p 2 - p' 2| ≤ H)
    (hA : ∀ z, (∃ p ∈ T, p 2 = z) → ∫⁻ u, volume (grainFib f S u z) ≤ ENNReal.ofReal A) :
    ∫⁻ z, ∫⁻ u, volume (grainFib f S u z) ≤ ENNReal.ofReal A * ENNReal.ofReal H := by
  set Hs : Set ℝ := (fun p : Space => p 2) '' T
  have hHs : volume Hs ≤ ENNReal.ofReal H := by
    apply nh_volume_le_of_abs
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩
    exact hH p hp p' hp'
  refine le_trans (lintegral_mono fun z => ?_)
    ((lintegral_indicator_const_le Hs _).trans (mul_le_mul_right hHs _))
  by_cases hz : z ∈ Hs
  · rw [indicator_of_mem hz]
    obtain ⟨p, hp, rfl⟩ := hz
    exact hA _ ⟨p, hp, rfl⟩
  · rw [indicator_of_notMem hz, nh_slice_eq_zero]
    rintro ⟨p, hp, rfl⟩
    exact hz ⟨p, hST hp, rfl⟩

/-! ### Tubes crossing the grains -/

/-- The arithmetic of the transversal slice bound. -/
lemma nh_trans_arith {σ η θ δ γ φ s : ℝ} (hσ0 : 0 < σ) (hδ : 0 < δ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hφ : γ / 2 ≤ φ) (hs : 0 < s) (hs2 : s ≤ 2 * θ) :
    8 * δ / φ * (2 * δ * (δ ^ (-η) * ((2 * (2 * φ * (2 * δ / s))) / δ) ^ (1 - σ))) ≤
      128 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ / s := by
  have hφ0 : 0 < φ := by linarith
  have hX : (2 * (2 * φ * (2 * δ / s))) / δ = 8 * φ / s := by
    field_simp; ring
  rw [hX]
  have hXpos : 0 < 8 * φ / s := by positivity
  have hpow : (8 * φ / s) ^ (1 - σ) = (8 * φ / s) / (8 * φ / s) ^ σ := by
    rw [Real.rpow_sub hXpos, Real.rpow_one]
  have hkey : 1 ≤ (θ / γ) ^ σ * (8 * φ / s) ^ σ := by
    rw [← Real.mul_rpow (by positivity) hXpos.le]
    apply Real.one_le_rpow _ hσ0.le
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hs2 hγ.le
    have h2 := mul_le_mul_of_nonneg_left hφ hθ.le
    have h3 : 0 ≤ θ * φ := by positivity
    linarith
  have hXσ : 0 < (8 * φ / s) ^ σ := Real.rpow_pos_of_pos hXpos σ
  have hηpos : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
  rw [hpow]
  calc 8 * δ / φ * (2 * δ * (δ ^ (-η) * ((8 * φ / s) / (8 * φ / s) ^ σ)))
      = 128 * δ ^ 2 * δ ^ (-η) / s * (1 / (8 * φ / s) ^ σ) := by
        field_simp
        norm_num
    _ ≤ 128 * δ ^ 2 * δ ^ (-η) / s * (θ / γ) ^ σ := by
        gcongr
        rw [div_le_iff₀ hXσ]
        linarith
    _ = 128 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ / s := by ring


lemma nh_phi_le_two {f : ℝ → ℝ} {z : ℝ} {v : Space} (hv : ‖v‖ = 1) (hF : |f z| ≤ 1) :
    |v 0 + f z * v 1| ≤ 2 := by
  calc |v 0 + f z * v 1| ≤ |v 0| + |f z * v 1| := abs_add_le _ _
    _ = |v 0| + |f z| * |v 1| := by rw [abs_mul]
    _ ≤ 1 + 1 * 1 := by gcongr; exacts [nh_abs_coord_v hv 0, nh_abs_coord_v hv 1]
    _ = 2 := by norm_num

lemma nh_le_L {δ Δ a : ℝ} (hδ : 0 < δ) (h1 : Δ ≤ 1) (h2 : Δ * a ≤ 2 * δ) :
    Δ ≤ 2 * δ / max a (2 * δ) := by
  rw [le_div_iff₀ (lt_max_of_lt_right (by linarith))]
  rcases le_total a (2 * δ) with h | h
  · rw [max_eq_right h]
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 2 * δ)
    linarith
  · rw [max_eq_left h]; exact h2

/-- At a height where the tube crosses the grains at angle `≳ γ`, its slice is sparse. -/
lemma nh_trans_height {σ η θ δ γ z : ℝ} {f : ℝ → ℝ} {E S : Set Space} {x v : Space}
    (hσ0 : 0 < σ) (hδ : 0 < δ) (hδθ : δ ≤ θ) (hγ : 10 * θ ≤ γ)
    (hv : ‖v‖ = 1) (hv2 : |v 2| < θ) (hF : |f z| ≤ 1) (hφ : γ / 2 ≤ |v 0 + f z * v 1|)
    (hAD : AD δ (1 - σ) (δ ^ (-η)) (PS f E z))
    (hST : S ⊆ Tube δ x v) (hSE : S ⊆ E) :
    ∫⁻ u, volume (grainFib f S u z) ≤
      ENNReal.ofReal (128 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ / max |v 2| (2 * δ)) := by
  set φ := |v 0 + f z * v 1| with hφdef
  set s := max |v 2| (2 * δ) with hsdef
  set L := 2 * δ / s with hLdef
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hγ0 : 0 < γ := by linarith
  have hs : 0 < s := lt_max_of_lt_right (by linarith)
  have hs2 : s ≤ 2 * θ := max_le (by linarith [abs_nonneg (v 2)]) (by linarith)
  have hφ0 : 0 < φ := by linarith
  have hφ2 : φ ≤ 2 := nh_phi_le_two hv hF
  have hL : 0 < L := by positivity
  have hφL : 4 * δ ≤ φ * L := by
    have e : φ * L = 2 * δ * φ / s := by simp only [hLdef]; ring
    rw [e, le_div_iff₀ hs]
    have h1 := mul_le_mul_of_nonneg_left hs2 (by positivity : (0:ℝ) ≤ 4 * δ)
    have h2 := mul_le_mul_of_nonneg_left hφ (by positivity : (0:ℝ) ≤ 2 * δ)
    have h3 := mul_le_mul_of_nonneg_left hγ hδ.le
    have h4 : 0 ≤ δ * γ := by positivity
    linarith
  have hD : ∀ u, volume (grainFib f (Tube δ x v) u z) ≤ ENNReal.ofReal (8 * δ / φ) := by
    intro u
    apply nh_fibre_le hv hF
    intro Δ _ _ _ h3
    rw [le_div_iff₀ hφ0]
    have := mul_le_mul_of_nonneg_left hφ2 (by positivity : (0:ℝ) ≤ 2 * δ)
    linarith
  have hR := nh_PS_diam (x := x) (R := 2 * φ * L) hv hF (fun Δ _ h1 h2 => by
      have := mul_le_mul_of_nonneg_right (nh_le_L hδ h1 h2) hφ0.le
      linarith)
  refine (nh_slice_le hST hSE hD).trans ?_
  have hvol : volume (PS f E z ∩ PS f (Tube δ x v) z) ≤
      ENNReal.ofReal (2 * δ * (δ ^ (-η) * ((2 * (2 * φ * L)) / δ) ^ (1 - σ))) := by
    rcases (PS f (Tube δ x v) z).eq_empty_or_nonempty with h | ⟨u0, hu0⟩
    · rw [h, inter_empty, measure_empty]; exact zero_le
    · apply volume_le_of_ad (a := u0 - 2 * φ * L) hδ.le (by linarith)
      · intro u hu
        have := abs_le.mp (hR u hu.2 u0 hu0)
        constructor <;> linarith [this.1, this.2]
      · exact ad_mono hAD inter_subset_left
  calc ENNReal.ofReal (8 * δ / φ) * volume (PS f E z ∩ PS f (Tube δ x v) z)
      ≤ ENNReal.ofReal (8 * δ / φ) *
          ENNReal.ofReal (2 * δ * (δ ^ (-η) * ((2 * (2 * φ * L)) / δ) ^ (1 - σ))) := by
        gcongr
    _ = ENNReal.ofReal (8 * δ / φ *
          (2 * δ * (δ ^ (-η) * ((2 * (2 * φ * L)) / δ) ^ (1 - σ)))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (nh_trans_arith hσ0 hδ hθ hγ0 hφ hs hs2)

lemma nh_height_mem {δ : ℝ} {x v p : Space} (hball : Tube δ x v ⊆ ball 0 1)
    (hp : p ∈ Tube δ x v) : p 2 ∈ Icc (-1 : ℝ) 1 := by
  have := abs_lt.mp (nh_abs_coord_ball (hball hp) 2)
  exact ⟨this.1.le, this.2.le⟩

/-- Changing the height changes the transversality by at most the height difference. -/
lemma nh_phi_shift {f : ℝ → ℝ} {z z' : ℝ} {v : Space} (hv : ‖v‖ = 1) :
    |v 0 + f z' * v 1| ≤ |v 0 + f z * v 1| + |f z - f z'| := by
  have e : v 0 + f z' * v 1 = (v 0 + f z * v 1) + (-(f z - f z') * v 1) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_neg]
  exact add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) (nh_abs_coord_v hv 1))

/-- The heights of a point of a tube and of its base point are close. -/
lemma nh_height_close {δ : ℝ} {x v p : Space} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hp : p ∈ Tube δ x v) : |p 2 - x 2| ≤ |v 2| + 2 * δ := by
  obtain ⟨Δ, -, h1, h2a, -⟩ := nh_pair (F := 0) hv (by simp) hp (nh_mem_tube_self hδ x v)
  have := mul_le_of_le_one_left (abs_nonneg (v 2)) h1
  linarith

/-- A nearly horizontal tube crossing the grains carries little shading. -/
lemma nh_trans_tube {σ η θ δ γ : ℝ} {f : ℝ → ℝ} {E Y : Set Space} {x v : Space}
    (hσ0 : 0 < σ) (hδ : 0 < δ) (hδθ : δ ≤ θ) (hγ : 10 * θ ≤ γ)
    (hv : ‖v‖ = 1) (hball : Tube δ x v ⊆ ball 0 1) (hY : MeasurableSet Y)
    (hYT : Y ⊆ Tube δ x v) (hYE : Y ⊆ E)
    (hf : Continuous f) (hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1)
    (hfL : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'|)
    (hG : GlobalGrains σ η δ f E)
    (hv2 : |v 2| < θ) (hφ : γ ≤ |v 0 + f (x 2) * v 1|) :
    volume Y ≤ ENNReal.ofReal (256 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ) := by
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hγ0 : 0 < γ := by linarith
  have hx2 : x 2 ∈ Icc (-1 : ℝ) 1 := nh_height_mem hball (nh_mem_tube_self hδ x v)
  rw [volume_eq_lintegral_grainFib hf hY]
  refine (nh_lintegral_height_le hYT (H := |v 2| + 2 * δ)
    (A := 128 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ / max |v 2| (2 * δ)) ?_ ?_).trans ?_
  · intro p hp p' hp'
    obtain ⟨Δ, -, h1, h2a, -⟩ := nh_pair (F := 0) hv (by simp) hp hp'
    have := mul_le_of_le_one_left (abs_nonneg (v 2)) h1
    linarith
  · rintro z ⟨p, hp, rfl⟩
    have hz := nh_height_mem hball hp
    refine nh_trans_height hσ0 hδ hδθ hγ hv hv2 (hf1 _ hz) ?_ (hG _ hz) hYT hYE
    have h1 := nh_phi_shift (f := f) (z := p 2) (z' := x 2) hv
    have h2 := hfL _ hz _ hx2
    have h3 := nh_height_close hδ hv hp
    linarith
  · rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs : 0 < max |v 2| (2 * δ) := lt_max_of_lt_right (by linarith)
    have hP : 0 ≤ 128 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ := by positivity
    calc 128 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ / max |v 2| (2 * δ) * (|v 2| + 2 * δ)
        ≤ 128 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ / max |v 2| (2 * δ) *
            (2 * max |v 2| (2 * δ)) := by
          gcongr
          linarith [le_max_left |v 2| (2 * δ), le_max_right |v 2| (2 * δ)]
      _ = 256 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ := by
          field_simp; ring

/-! ### Tubes along the grains: counting in thin boxes -/

/-- The thin box adapted to the grains at height `z`. -/
def nh_box (F z c h w : ℝ) : Set Space :=
  ball (0 : Space) 1 ∩ {q : Space | |q 2 - z| ≤ h} ∩ {q : Space | |q 0 + F * q 1 - c| ≤ w}

lemma nh_box_measurable (F z c h w : ℝ) : MeasurableSet (nh_box F z c h w) := by
  refine (measurableSet_ball.inter ?_).inter ?_
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_le (by fun_prop) measurable_const

lemma nh_box_convex (F z c h w : ℝ) : Convex ℝ (nh_box F z c h w) := by
  refine ((convex_ball _ _).inter ?_).inter ?_
  · have : {q : Space | |q 2 - z| ≤ h} = (fun q : Space => q 2) ⁻¹' Icc (z - h) (z + h) := by
      ext q; simp only [mem_ofPred_eq, mem_preimage, mem_Icc, abs_le]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [this]
    refine (convex_Icc _ _).is_linear_preimage ?_
    exact { map_add := fun a b => by simp, map_smul := fun a b => by simp }
  · have : {q : Space | |q 0 + F * q 1 - c| ≤ w} =
        (fun q : Space => q 0 + F * q 1) ⁻¹' Icc (c - w) (c + w) := by
      ext q; simp only [mem_ofPred_eq, mem_preimage, mem_Icc, abs_le]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [this]
    refine (convex_Icc _ _).is_linear_preimage ?_
    exact { map_add := fun a b => by simp; ring, map_smul := fun a b => by simp; ring }

lemma nh_box_fib {F z c h w z' u y : ℝ}
    (hy : y ∈ grainFib (fun _ => F) (nh_box F z c h w) u z') :
    |z' - z| ≤ h ∧ |u - c| ≤ w ∧ |y| < 1 := by
  rw [mem_grainFib] at hy
  obtain ⟨⟨hb, hz⟩, hc⟩ := hy
  simp only [mem_ofPred_eq, ofTwist_zero, ofTwist_one, ofTwist_two] at hz hc
  have e : u - F * y + F * y - c = u - c := by ring
  rw [e] at hc
  refine ⟨hz, hc, ?_⟩
  simpa using nh_abs_coord_ball hb 1

lemma nh_box_volume (F z c h w : ℝ) (hw : 0 ≤ w) :
    volume (nh_box F z c h w) ≤ ENNReal.ofReal (8 * h * w) := by
  rw [volume_eq_lintegral_grainFib (f := fun _ => F) continuous_const (nh_box_measurable _ _ _ _ _)]
  have hinner : ∀ z', ∫⁻ u, volume (grainFib (fun _ => F) (nh_box F z c h w) u z') ≤
      (Icc (z - h) (z + h)).indicator (fun _ => ENNReal.ofReal 2 * ENNReal.ofReal (2 * w)) z' := by
    intro z'
    by_cases hz' : z' ∈ Icc (z - h) (z + h)
    · rw [indicator_of_mem hz']
      calc ∫⁻ u, volume (grainFib (fun _ => F) (nh_box F z c h w) u z')
          ≤ ∫⁻ u, (Icc (c - w) (c + w)).indicator (fun _ => ENNReal.ofReal 2) u := by
            apply lintegral_mono; intro u
            by_cases hu : u ∈ Icc (c - w) (c + w)
            · rw [indicator_of_mem hu]
              apply nh_volume_le_of_abs
              intro y hy y' hy'
              have h1 := abs_lt.mp (nh_box_fib hy).2.2
              have h2 := abs_lt.mp (nh_box_fib hy').2.2
              rw [abs_le]; constructor <;> linarith
            · rw [indicator_of_notMem hu]
              have : grainFib (fun _ => F) (nh_box F z c h w) u z' = ∅ := by
                ext y
                simp only [mem_empty_iff_false, iff_false]
                intro hy
                have := abs_le.mp (nh_box_fib hy).2.1
                exact hu ⟨by linarith, by linarith⟩
              simp only [this, measure_empty, le_refl]
        _ = ENNReal.ofReal 2 * ENNReal.ofReal (2 * w) := by
            rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
            ring_nf
    · rw [indicator_of_notMem hz']
      have : ∀ u, grainFib (fun _ => F) (nh_box F z c h w) u z' = ∅ := by
        intro u
        ext y
        simp only [mem_empty_iff_false, iff_false]
        intro hy
        have := abs_le.mp (nh_box_fib hy).1
        exact hz' ⟨by linarith, by linarith⟩
      simp [this]
  calc ∫⁻ z', ∫⁻ u, volume (grainFib (fun _ => F) (nh_box F z c h w) u z')
      ≤ ∫⁻ z', (Icc (z - h) (z + h)).indicator
          (fun _ => ENNReal.ofReal 2 * ENNReal.ofReal (2 * w)) z' := lintegral_mono hinner
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (2 * w) * ENNReal.ofReal (2 * h) := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
        ring_nf
    _ = ENNReal.ofReal (8 * h * w) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        ring_nf


/-- Global convex counts in a thin box adapted to the grains. -/
lemma nh_count_box {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} (hδ : 0 < δ)
    (hcount : GlobalCount η δ n x v) (F z c h w : ℝ) (hh : 0 ≤ h) (hw : 0 ≤ w) :
    (({i | Tube δ (x i) (v i) ⊆ nh_box F z c h w}.ncard : ℕ) : ℝ) ≤
      δ ^ (-η) * n * (8 * h * w) := by
  have h1 := hcount (nh_box F z c h w) (nh_box_convex F z c h w)
  have h2 := h1.trans (mul_le_mul_right (nh_box_volume F z c h w hw) _)
  rw [← ENNReal.ofReal_mul (by positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2

/-- A tube along the grains through height `z` lies in a thin box around its twisted
position. -/
lemma nh_tube_sub_box {θ δ γ z c t : ℝ} {f : ℝ → ℝ} {x v q : Space}
    (hδ : 0 < δ) (hδθ : δ ≤ θ) (hγ : 10 * θ ≤ γ) (hv : ‖v‖ = 1)
    (hball : Tube δ x v ⊆ ball 0 1) (hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1)
    (hfL : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'|)
    (hv2 : |v 2| < θ) (hvt : |v 2| ≤ t) (hφ : |v 0 + f (x 2) * v 1| < γ)
    (hq : q ∈ Tube δ x v) (hqz : q 2 = z) (hqc : |twist f q - c| ≤ γ) :
    Tube δ x v ⊆ nh_box (f z) z c (t + 2 * δ) (3 * γ) := by
  have hz : z ∈ Icc (-1 : ℝ) 1 := hqz ▸ nh_height_mem hball hq
  have hx2 : x 2 ∈ Icc (-1 : ℝ) 1 := nh_height_mem hball (nh_mem_tube_self hδ x v)
  have hF := hf1 z hz
  have hshift := nh_phi_shift (f := f) (z := x 2) (z' := z) hv
  have hfz := hfL _ hx2 _ hz
  have hqx := nh_height_close hδ hv hq
  rw [hqz] at hqx
  have hzx : |x 2 - z| = |z - x 2| := abs_sub_comm _ _
  intro p hp
  obtain ⟨Δ, h0, h1, h2a, -, h0a, -, -⟩ := nh_pair (F := f z) hv hF hp hq
  rw [hqz] at h2a
  have htw : twist f q = q 0 + f z * q 1 := by rw [twist, hqz]
  rw [htw] at hqc
  refine ⟨⟨hball hp, ?_⟩, ?_⟩
  · show |p 2 - z| ≤ t + 2 * δ
    have := mul_le_of_le_one_left (abs_nonneg (v 2)) h1
    linarith
  · show |p 0 + f z * p 1 - c| ≤ 3 * γ
    have hφz : |v 0 + f z * v 1| ≤ γ + 3 * θ := by linarith
    have hφz0 := abs_nonneg (v 0 + f z * v 1)
    have hdiff : |(p 0 + f z * p 1) - (q 0 + f z * q 1)| ≤ γ + 7 * θ := by
      have := mul_le_of_le_one_left hφz0 h1
      linarith
    calc |p 0 + f z * p 1 - c| = |((p 0 + f z * p 1) - (q 0 + f z * q 1)) +
          (q 0 + f z * q 1 - c)| := by ring_nf
      _ ≤ |(p 0 + f z * p 1) - (q 0 + f z * q 1)| + |q 0 + f z * q 1 - c| := abs_add_le _ _
      _ ≤ 3 * γ := by linarith

lemma nh_count_arith {σ γ : ℝ} (hσ0 : 0 ≤ σ) (hγ : 0 < γ) : (4 / γ) ^ (1 - σ) * γ ≤ 4 * γ ^ σ := by
  rw [Real.div_rpow (by norm_num) hγ.le, Real.rpow_sub hγ, Real.rpow_one]
  have h4 : (4 : ℝ) ^ (1 - σ) ≤ 4 := by
    calc (4 : ℝ) ^ (1 - σ) ≤ 4 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one _
  have hγσ : 0 < γ ^ σ := Real.rpow_pos_of_pos hγ σ
  calc 4 ^ (1 - σ) / (γ / γ ^ σ) * γ = 4 ^ (1 - σ) * γ ^ σ := by
        field_simp
    _ ≤ 4 * γ ^ σ := by gcongr

lemma nh_rpow_two_mul {δ η : ℝ} (hδ : 0 < δ) : δ ^ (-η) * δ ^ (-η) = δ ^ (-2 * η) := by
  rw [← Real.rpow_add hδ]; ring_nf

/-- Tubes along the grains through a fixed height are few. -/
lemma nh_count {σ η θ δ γ z t : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {f : ℝ → ℝ} (hσ0 : 0 < σ) (hδ : 0 < δ) (hδθ : δ ≤ θ) (hγ : 10 * θ ≤ γ) (hγ1 : γ ≤ 1)
    (hfam : Family δ n x v Y) (hcount : GlobalCount η δ n x v)
    (hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1)
    (hfL : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'|)
    (hAD : AD δ (1 - σ) (δ ^ (-η)) (PS f (⋃ i, Y i) z)) (ht : 0 ≤ t) :
    (({i | |v i 2| < θ ∧ |v i 0 + f (x i 2) * v i 1| < γ ∧ (∃ q ∈ Y i, q 2 = z) ∧
        |v i 2| ≤ t}.ncard : ℕ) : ℝ) ≤ 96 * δ ^ (-2 * η) * n * γ ^ σ * (t + 2 * δ) := by
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hγ0 : 0 < γ := by linarith
  obtain ⟨m, c, hcov, hm⟩ := hAD γ 4 (-2) (by linarith) (by linarith)
  have hsub : {i | |v i 2| < θ ∧ |v i 0 + f (x i 2) * v i 1| < γ ∧ (∃ q ∈ Y i, q 2 = z) ∧
      |v i 2| ≤ t} ⊆
      ⋃ k, {i | Tube δ (x i) (v i) ⊆ nh_box (f z) z (c k) (t + 2 * δ) (3 * γ)} := by
    rintro i ⟨hv2, hφ, ⟨q, hqY, hqz⟩, hvt⟩
    have hqT := hfam.sub i hqY
    have hqE : twist f q ∈ PS f (⋃ i, Y i) z := ⟨q, mem_iUnion.mpr ⟨i, hqY⟩, Prod.ext rfl hqz⟩
    have hq2 : twist f q ∈ Icc (-2 : ℝ) (-2 + 4) := by
      have h0 := nh_abs_coord_ball (hfam.ball i hqT) 0
      have h1 := nh_abs_coord_ball (hfam.ball i hqT) 1
      have hF := hf1 _ (nh_height_mem (hfam.ball i) hqT)
      have hb : |twist f q| ≤ 2 := by
        calc |twist f q| ≤ |q 0| + |f (q 2)| * |q 1| := by
              rw [twist, ← abs_mul]; exact abs_add_le _ _
          _ ≤ 1 + 1 * 1 := by gcongr
          _ = 2 := by norm_num
      have := abs_le.mp hb
      constructor <;> linarith
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov ⟨hqE, hq2⟩)
    rw [mem_closedBall, Real.dist_eq] at hk
    exact mem_iUnion.mpr ⟨k, nh_tube_sub_box hδ hδθ hγ (hfam.unit i) (hfam.ball i) hf1 hfL
      hv2 hvt hφ hqT hqz hk⟩
  have hcard := (Set.ncard_le_ncard hsub).trans (Set.ncard_iUnion_le_of_fintype _)
  have hcardR : (({i | |v i 2| < θ ∧ |v i 0 + f (x i 2) * v i 1| < γ ∧ (∃ q ∈ Y i, q 2 = z) ∧
        |v i 2| ≤ t}.ncard : ℕ) : ℝ) ≤
      ∑ k, (({i | Tube δ (x i) (v i) ⊆ nh_box (f z) z (c k) (t + 2 * δ) (3 * γ)}.ncard
        : ℕ) : ℝ) := by
    exact_mod_cast hcard
  refine hcardR.trans ?_
  have hbox : ∀ k, (({i | Tube δ (x i) (v i) ⊆ nh_box (f z) z (c k) (t + 2 * δ) (3 * γ)}.ncard
      : ℕ) : ℝ) ≤ δ ^ (-η) * n * (8 * (t + 2 * δ) * (3 * γ)) :=
    fun k => nh_count_box hδ hcount _ _ _ _ _ (by positivity) (by positivity)
  refine (Finset.sum_le_sum fun k _ => hbox k).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hca := nh_count_arith hσ0.le hγ0
  have hη : 0 < δ ^ (-η) := Real.rpow_pos_of_pos hδ _
  rw [← nh_rpow_two_mul hδ]
  calc (m : ℝ) * (δ ^ (-η) * n * (8 * (t + 2 * δ) * (3 * γ)))
      ≤ (δ ^ (-η) * (4 / γ) ^ (1 - σ)) * (δ ^ (-η) * n * (8 * (t + 2 * δ) * (3 * γ))) := by
        gcongr
    _ = 24 * (δ ^ (-η) * δ ^ (-η) * n * (t + 2 * δ)) * ((4 / γ) ^ (1 - σ) * γ) := by ring
    _ ≤ 24 * (δ ^ (-η) * δ ^ (-η) * n * (t + 2 * δ)) * (4 * γ ^ σ) := by gcongr
    _ = 96 * (δ ^ (-η) * δ ^ (-η)) * n * γ ^ σ * (t + 2 * δ) := by ring


/-- The area of a horizontal slice of a tube is `≲ δ² / |v 2| + δ²`. -/
lemma nh_area_height {δ z : ℝ} {f : ℝ → ℝ} {E S : Set Space} {x v : Space} (hδ : 0 < δ)
    (hv : ‖v‖ = 1) (hF : |f z| ≤ 1) (hST : S ⊆ Tube δ x v) (hSE : S ⊆ E) :
    ∫⁻ u, volume (grainFib f S u z) ≤
      ENNReal.ofReal (24 * δ ^ 2 / max |v 2| (2 * δ) + 8 * δ ^ 2) := by
  set φ := |v 0 + f z * v 1| with hφdef
  set s := max |v 2| (2 * δ) with hsdef
  set L := 2 * δ / s with hLdef
  have hs : 0 < s := lt_max_of_lt_right (by linarith)
  have hL : 0 < L := by positivity
  have hφ0 : 0 ≤ φ := abs_nonneg _
  have hφ2 : φ ≤ 2 := nh_phi_le_two hv hF
  have hden : 0 < 4 * δ + φ * L := by positivity
  have hD : ∀ u, volume (grainFib f (Tube δ x v) u z) ≤
      ENNReal.ofReal (8 * δ * L / (4 * δ + φ * L) + 2 * δ) := by
    intro u
    apply nh_fibre_le hv hF
    intro Δ _ h1 h2 h3
    have hΔL := nh_le_L hδ h1 h2
    have : Δ ≤ 8 * δ * L / (4 * δ + φ * L) := by
      rw [le_div_iff₀ hden]
      have k1 := mul_le_mul_of_nonneg_left hΔL (by positivity : (0:ℝ) ≤ 4 * δ)
      have k2 := mul_le_mul_of_nonneg_right h3 hL.le
      linarith
    linarith
  have hR := nh_PS_diam (x := x) (R := φ * L + 4 * δ) hv hF (fun Δ _ h1 h2 => by
    have := mul_le_mul_of_nonneg_right (nh_le_L hδ h1 h2) hφ0
    linarith)
  refine (nh_slice_le hST hSE hD).trans ?_
  have hvol : volume (PS f E z ∩ PS f (Tube δ x v) z) ≤ ENNReal.ofReal (φ * L + 4 * δ) :=
    (measure_mono inter_subset_right).trans (nh_volume_le_of_abs hR)
  calc ENNReal.ofReal (8 * δ * L / (4 * δ + φ * L) + 2 * δ) *
        volume (PS f E z ∩ PS f (Tube δ x v) z)
      ≤ ENNReal.ofReal (8 * δ * L / (4 * δ + φ * L) + 2 * δ) *
          ENNReal.ofReal (φ * L + 4 * δ) := by gcongr
    _ = ENNReal.ofReal ((8 * δ * L / (4 * δ + φ * L) + 2 * δ) * (φ * L + 4 * δ)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : 8 * δ * L / (4 * δ + φ * L) * (φ * L + 4 * δ) = 8 * δ * L := by
          field_simp; ring
        have e2 : 24 * δ ^ 2 / s = 12 * δ * L := by
          simp only [hLdef]; field_simp; ring
        rw [add_mul, e1, e2]
        have := mul_le_mul_of_nonneg_left hφ2 (by positivity : (0:ℝ) ≤ 2 * δ * L)
        linarith

/-- Dyadic summation: if at most `B t` of the `s i` lie below `t`, then `∑ 1 / s i` is at most
`2 B` per dyadic scale. -/
lemma nh_dyadic {ι : Type*} (s : ι → ℝ) {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B) :
    ∀ (J : ℕ) (S : Finset ι) (b : ℝ), b ≤ 2 ^ J * a → (∀ i ∈ S, a ≤ s i ∧ s i ≤ b) →
    (∀ t, a ≤ t → t ≤ b → ((S.filter (fun i => s i ≤ t)).card : ℝ) ≤ B * t) →
    ∑ i ∈ S, 1 / s i ≤ 2 * B * (J + 1) := by
  intro J
  induction J with
  | zero =>
    intro S b hb hS hcnt
    rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · simp only [Finset.sum_empty]; positivity
    have hab : a ≤ b := (hS i0 hi0).1.trans (hS i0 hi0).2
    have hall : S.filter (fun i => s i ≤ b) = S :=
      Finset.filter_true_of_mem (fun i hi => (hS i hi).2)
    have hc := hcnt b hab le_rfl
    rw [hall] at hc
    have hb' : b ≤ a := by simpa using hb
    calc ∑ i ∈ S, 1 / s i ≤ ∑ i ∈ S, 1 / a :=
          Finset.sum_le_sum (fun i hi => one_div_le_one_div_of_le ha (hS i hi).1)
      _ = S.card / a := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ B * b / a := by gcongr
      _ ≤ B * a / a := by gcongr
      _ = B := by field_simp
      _ ≤ 2 * B * ((0 : ℕ) + 1) := by push_cast; linarith
  | succ J ih =>
    intro S b hb hS hcnt
    rcases S.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · simp only [Finset.sum_empty]; positivity
    have hab : a ≤ b := (hS i0 hi0).1.trans (hS i0 hi0).2
    have hb0 : 0 < b := ha.trans_le hab
    rw [← Finset.sum_filter_add_sum_filter_not S (fun i => s i ≤ b / 2)]
    have h1 : ∑ i ∈ S.filter (fun i => s i ≤ b / 2), 1 / s i ≤ 2 * B * (J + 1) := by
      apply ih (S.filter (fun i => s i ≤ b / 2)) (b / 2)
      · rw [pow_succ] at hb; linarith
      · intro i hi
        rw [Finset.mem_filter] at hi
        exact ⟨(hS i hi.1).1, hi.2⟩
      · intro t ht1 ht2
        refine le_trans ?_ (hcnt t ht1 (by linarith))
        rw [Finset.filter_filter]
        exact_mod_cast Finset.card_le_card (fun i hi => by
          simp only [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, hi.2.2⟩)
    have hall : S.filter (fun i => s i ≤ b) = S :=
      Finset.filter_true_of_mem (fun i hi => (hS i hi).2)
    have hc := hcnt b hab le_rfl
    rw [hall] at hc
    have h2 : ∑ i ∈ S.filter (fun i => ¬ s i ≤ b / 2), 1 / s i ≤ 2 * B := by
      calc ∑ i ∈ S.filter (fun i => ¬ s i ≤ b / 2), 1 / s i
          ≤ ∑ i ∈ S.filter (fun i => ¬ s i ≤ b / 2), 2 / b := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_filter, not_le] at hi
            have hsi : 0 < s i := by linarith
            rw [div_le_div_iff₀ hsi hb0]
            linarith
        _ = ((S.filter (fun i => ¬ s i ≤ b / 2)).card : ℝ) * (2 / b) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (S.card : ℝ) * (2 / b) := by
            gcongr
            exact Finset.filter_subset _ _
        _ ≤ B * b * (2 / b) := by gcongr
        _ = 2 * B := by field_simp
    push_cast
    linarith

/-- At a fixed height, the tubes along the grains carry little slice area in total. -/
lemma nh_AG_height {σ η θ δ γ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {f : ℝ → ℝ} {J : ℕ}
    (hσ0 : 0 < σ) (hδ : 0 < δ) (hδθ : δ ≤ θ) (hγ : 10 * θ ≤ γ) (hγ1 : γ ≤ 1)
    (hJ : θ ≤ 2 ^ J * δ)
    (hfam : Family δ n x v Y) (hcount : GlobalCount η δ n x v)
    (hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1)
    (hfL : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'|)
    (hG : GlobalGrains σ η δ f (⋃ i, Y i)) (z : ℝ) :
    ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
        (fun i => ¬ γ ≤ |v i 0 + f (x i 2) * v i 1|),
        ∫⁻ u, volume (grainFib f (Y i) u z) ≤
      (Icc (-1 : ℝ) 1).indicator
        (fun _ => ENNReal.ofReal (10000 * (J + 1) * (δ ^ (-2 * η) * n * γ ^ σ) * δ ^ 2)) z := by
  classical
  set AG := (Finset.univ.filter (fun i => |v i 2| < θ)).filter
    (fun i => ¬ γ ≤ |v i 0 + f (x i 2) * v i 1|) with hAG
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hγ0 : 0 < γ := by linarith
  by_cases hz : z ∈ Icc (-1 : ℝ) 1
  swap
  · rw [indicator_of_notMem hz]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i _
    apply nh_slice_eq_zero
    rintro ⟨q, hq, rfl⟩
    exact hz (nh_height_mem (hfam.ball i) (hfam.sub i hq))
  rw [indicator_of_mem hz]
  set Sz := AG.filter (fun i => ∃ q ∈ Y i, q 2 = z) with hSz
  have hsplit : ∑ i ∈ AG, ∫⁻ u, volume (grainFib f (Y i) u z) ≤
      ∑ i ∈ Sz, ENNReal.ofReal (24 * δ ^ 2 / max |v i 2| (2 * δ) + 8 * δ ^ 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not AG (fun i => ∃ q ∈ Y i, q 2 = z)]
    have h0 : ∑ i ∈ AG.filter (fun i => ¬ ∃ q ∈ Y i, q 2 = z),
        ∫⁻ u, volume (grainFib f (Y i) u z) = 0 :=
      Finset.sum_eq_zero (fun i hi => nh_slice_eq_zero (Finset.mem_filter.mp hi).2)
    rw [h0, add_zero]
    apply Finset.sum_le_sum
    intro i _
    exact nh_area_height hδ (hfam.unit i) (hf1 z hz) (hfam.sub i) (subset_iUnion Y i)
  refine hsplit.trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set P := δ ^ (-2 * η) * n * γ ^ σ with hP
  have hP0 : 0 ≤ P := by positivity
  have hcnt : ∀ t, 0 ≤ t →
      ((Sz.filter (fun i => |v i 2| ≤ t)).card : ℝ) ≤ 96 * P * (t + 2 * δ) := by
    intro t ht
    have h := nh_count hσ0 hδ hδθ hγ hγ1 hfam hcount hf1 hfL (hG z hz) ht
    rw [ncard_setOf] at h
    refine le_trans ?_ (h.trans (le_of_eq (by rw [hP]; ring)))
    exact_mod_cast Finset.card_le_card (fun i hi => by
      simp only [hSz, hAG, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi ⊢
      exact ⟨hi.1.1.1, hi.1.1.2, hi.1.2, hi.2⟩)
  have hcardS : (Sz.card : ℝ) ≤ 96 * P * (θ + 2 * δ) := by
    have h := hcnt θ hθ.le
    have hS : Sz.filter (fun i => |v i 2| ≤ θ) = Sz := Finset.filter_true_of_mem (fun i hi => by
      simp only [hSz, hAG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi.1.1.le)
    rwa [hS] at h
  have hdy := nh_dyadic (fun i => max |v i 2| (2 * δ)) (a := 2 * δ) (B := 192 * P)
    (by positivity) (by positivity) J Sz (2 * θ) (by rw [mul_left_comm]; linarith)
    (fun i hi => by
      simp only [hSz, hAG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨le_max_right _ _, max_le (by linarith [hi.1.1]) (by linarith)⟩)
    (fun t ht1 _ => by
      have h := hcnt t (by linarith)
      have h' := mul_le_mul_of_nonneg_left ht1 (by positivity : (0:ℝ) ≤ 96 * P)
      refine le_trans ?_ (h.trans (by linarith))
      exact_mod_cast Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter] at hi ⊢
        exact ⟨hi.1, (le_max_left _ _).trans hi.2⟩))
  have hsum : ∑ i ∈ Sz, (24 * δ ^ 2 / max |v i 2| (2 * δ) + 8 * δ ^ 2) =
      24 * δ ^ 2 * ∑ i ∈ Sz, 1 / max |v i 2| (2 * δ) + (Sz.card : ℝ) * (8 * δ ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  have hθ1 : θ + 2 * δ ≤ (J : ℝ) + 1 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    linarith
  have hδ2 : 0 ≤ δ ^ 2 := by positivity
  calc 24 * δ ^ 2 * ∑ i ∈ Sz, 1 / max |v i 2| (2 * δ) + (Sz.card : ℝ) * (8 * δ ^ 2)
      ≤ 24 * δ ^ 2 * (2 * (192 * P) * (J + 1)) + 96 * P * (θ + 2 * δ) * (8 * δ ^ 2) := by
        gcongr
    _ ≤ 24 * δ ^ 2 * (2 * (192 * P) * (J + 1)) + 96 * P * (J + 1) * (8 * δ ^ 2) := by
        gcongr
    _ ≤ 10000 * (J + 1) * P * δ ^ 2 := by
        have : 0 ≤ (J + 1 : ℝ) * P * δ ^ 2 := by positivity
        linarith

/-! ### Summing up -/

lemma nh_sum_lintegral_le {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ z, g i z ≤ ∫⁻ z, ∑ i ∈ s, g i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

lemma nh_log_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ J : ℕ, 1 ≤ 2 ^ J * δ ∧ (J : ℝ) + 1 ≤ 3 * (1 + Real.log (1 / δ)) := by
  have hl0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  set x := Real.log (1 / δ) / Real.log 2 with hx
  have hx0 : 0 ≤ x := by positivity
  refine ⟨⌈x⌉₊, ?_, ?_⟩
  · have hJ : Real.log (1 / δ) ≤ (⌈x⌉₊ : ℝ) * Real.log 2 := by
      have := Nat.le_ceil x
      rw [hx, div_le_iff₀ hl2p] at this
      exact this
    have h := Real.exp_le_exp.mpr hJ
    rw [Real.exp_log (by positivity), ← Real.log_pow, Real.exp_log (by positivity)] at h
    rw [div_le_iff₀ hδ] at h
    linarith
  · have h1 := Nat.ceil_lt_add_one hx0
    have h2 : x ≤ 3 / 2 * Real.log (1 / δ) := by
      rw [hx, div_le_iff₀ hl2p]
      have := mul_le_mul_of_nonneg_left hl2.le hl0
      linarith
    linarith


/-- The tubes along the grains carry little mass in total. -/
lemma nh_AG_total {σ η θ δ γ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {f : ℝ → ℝ} {J : ℕ}
    (hσ0 : 0 < σ) (hδ : 0 < δ) (hδθ : δ ≤ θ) (hγ : 10 * θ ≤ γ) (hγ1 : γ ≤ 1)
    (hJ : θ ≤ 2 ^ J * δ)
    (hfam : Family δ n x v Y) (hcount : GlobalCount η δ n x v) (hf : Continuous f)
    (hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1)
    (hfL : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'|)
    (hG : GlobalGrains σ η δ f (⋃ i, Y i)) :
    ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
        (fun i => ¬ γ ≤ |v i 0 + f (x i 2) * v i 1|), volume (Y i) ≤
      ENNReal.ofReal (2 * (10000 * (J + 1) * (δ ^ (-2 * η) * n * γ ^ σ) * δ ^ 2)) := by
  have hγ0 : 0 < γ := by linarith [hδ.trans_le hδθ]
  calc ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
        (fun i => ¬ γ ≤ |v i 0 + f (x i 2) * v i 1|), volume (Y i)
      = ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
          (fun i => ¬ γ ≤ |v i 0 + f (x i 2) * v i 1|),
          ∫⁻ z, ∫⁻ u, volume (grainFib f (Y i) u z) :=
        Finset.sum_congr rfl (fun i _ => volume_eq_lintegral_grainFib hf (hfam.meas i))
    _ ≤ ∫⁻ z, ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
          (fun i => ¬ γ ≤ |v i 0 + f (x i 2) * v i 1|),
          ∫⁻ u, volume (grainFib f (Y i) u z) := nh_sum_lintegral_le _ _
    _ ≤ ∫⁻ z, (Icc (-1 : ℝ) 1).indicator
          (fun _ => ENNReal.ofReal (10000 * (J + 1) * (δ ^ (-2 * η) * n * γ ^ σ) * δ ^ 2)) z :=
        lintegral_mono (fun z => nh_AG_height hσ0 hδ hδθ hγ hγ1 hJ hfam hcount hf1 hfL hG z)
    _ = ENNReal.ofReal (2 * (10000 * (J + 1) * (δ ^ (-2 * η) * n * γ ^ σ) * δ ^ 2)) := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

/-- The tubes crossing the grains carry little mass in total. -/
lemma nh_T_total {σ η θ δ γ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    {f : ℝ → ℝ}
    (hσ0 : 0 < σ) (hδ : 0 < δ) (hδθ : δ ≤ θ) (hγ : 10 * θ ≤ γ)
    (hfam : Family δ n x v Y) (hf : Continuous f)
    (hf1 : ∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1)
    (hfL : ∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'|)
    (hG : GlobalGrains σ η δ f (⋃ i, Y i)) :
    ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
        (fun i => γ ≤ |v i 0 + f (x i 2) * v i 1|), volume (Y i) ≤
      ENNReal.ofReal (n * (256 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ)) := by
  have hθ : 0 < θ := hδ.trans_le hδθ
  have hγ0 : 0 < γ := by linarith
  calc ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
        (fun i => γ ≤ |v i 0 + f (x i 2) * v i 1|), volume (Y i)
      ≤ ∑ i ∈ (Finset.univ.filter (fun i => |v i 2| < θ)).filter
        (fun i => γ ≤ |v i 0 + f (x i 2) * v i 1|),
          ENNReal.ofReal (256 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact nh_trans_tube hσ0 hδ hδθ hγ (hfam.unit i) (hfam.ball i) (hfam.meas i)
          (hfam.sub i) (subset_iUnion Y i) hf hf1 hfL hG hi.1 hi.2
    _ ≤ ∑ i : Fin n, ENNReal.ofReal (256 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ENNReal.ofReal (n * (256 * δ ^ 2 * δ ^ (-η) * (θ / γ) ^ σ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

theorem near_horizontal_mass : ∃ K : ℝ, 1 ≤ K ∧ ∀ (σ η θ δ : ℝ), 0 < σ → σ < 1 → 0 < η →
    0 < δ → δ ≤ 1 / 100 → δ ≤ θ → θ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space), Family δ n x v Y →
    GlobalCount η δ n x v →
    ∀ f : ℝ → ℝ, Continuous f → (∀ z ∈ Icc (-1 : ℝ) 1, |f z| ≤ 1) →
    (∀ z ∈ Icc (-1 : ℝ) 1, ∀ z' ∈ Icc (-1 : ℝ) 1, |f z - f z'| ≤ |z - z'|) →
    GlobalGrains σ η δ f (⋃ i, Y i) →
    ∑ i ∈ Finset.univ.filter (fun i => |v i 2| < θ), volume (Y i) ≤
      ENNReal.ofReal (K * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by
  refine ⟨100000, by norm_num, ?_⟩
  intro σ η θ δ hσ0 hσ1 hη hδ hδ1 hδθ hθ1 n x v Y hfam hcount f hf hf1 hfL hG
  have hθ : 0 < θ := hδ.trans_le hδθ
  set γ := Real.sqrt θ with hγdef
  have hγ0 : 0 < γ := Real.sqrt_pos.mpr hθ
  have hγ10 : γ ≤ 1 / 10 := by
    rw [hγdef, show (1 / 10 : ℝ) = Real.sqrt (1 / 100) by
      rw [show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hθ1
  have hγsq : γ * γ = θ := Real.mul_self_sqrt hθ.le
  have hγ : 10 * θ ≤ γ := by
    have := mul_le_mul_of_nonneg_left hγ10 hγ0.le
    linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hθγ : θ / γ = γ := by rw [← hγsq]; field_simp
  have hγσ : γ ^ σ ≤ θ ^ (σ / 4) := by
    rw [hγdef, Real.sqrt_eq_rpow, ← Real.rpow_mul hθ.le]
    exact Real.rpow_le_rpow_of_exponent_ge hθ (by linarith) (by linarith)
  obtain ⟨J, hJ1, hJlog⟩ := nh_log_bound hδ (by linarith)
  have hJ : θ ≤ 2 ^ J * δ := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun i => γ ≤ |v i 0 + f (x i 2) * v i 1|)]
  refine (add_le_add (nh_T_total hσ0 hδ hδθ hγ hfam hf hf1 hfL hG)
    (nh_AG_total hσ0 hδ hδθ hγ hγ1 hJ hfam hcount hf hf1 hfL hG)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hθγ]
  have hl0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hηle : δ ^ (-η) ≤ δ ^ (-2 * η) :=
    Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
  have hA : 0 ≤ δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2 := by positivity
  have hγσ0 : 0 ≤ γ ^ σ := by positivity
  have hη0 : 0 ≤ δ ^ (-η) := by positivity
  have hη20 : 0 ≤ δ ^ (-2 * η) := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hδ2 : 0 ≤ δ ^ 2 := by positivity
  have h1 : (n : ℝ) * (256 * δ ^ 2 * δ ^ (-η) * γ ^ σ) ≤
      256 * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by
    have := mul_le_mul hηle hγσ hγσ0 hη20
    calc (n : ℝ) * (256 * δ ^ 2 * δ ^ (-η) * γ ^ σ) =
        256 * (n * δ ^ 2) * (δ ^ (-η) * γ ^ σ) := by ring
      _ ≤ 256 * (n * δ ^ 2) * (δ ^ (-2 * η) * θ ^ (σ / 4)) := by gcongr
      _ = 256 * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by ring
  have h2 : 2 * (10000 * (J + 1) * (δ ^ (-2 * η) * n * γ ^ σ) * δ ^ 2) ≤
      20000 * (J + 1) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by
    have hJ0 : (0 : ℝ) ≤ J + 1 := by positivity
    calc 2 * (10000 * (J + 1) * (δ ^ (-2 * η) * n * γ ^ σ) * δ ^ 2) =
        20000 * (J + 1) * (δ ^ (-2 * η) * n * δ ^ 2) * γ ^ σ := by ring
      _ ≤ 20000 * (J + 1) * (δ ^ (-2 * η) * n * δ ^ 2) * θ ^ (σ / 4) := by gcongr
      _ = 20000 * (J + 1) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by ring
  have h3 : 20000 * ((J : ℝ) + 1) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) ≤
      60000 * (1 + Real.log (1 / δ)) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ hA
    linarith
  have h4 : 256 * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) ≤
      256 * (1 + Real.log (1 / δ)) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by
    have : (256 : ℝ) ≤ 256 * (1 + Real.log (1 / δ)) := by linarith
    exact mul_le_mul_of_nonneg_right this hA
  calc (n : ℝ) * (256 * δ ^ 2 * δ ^ (-η) * γ ^ σ) +
        2 * (10000 * (J + 1) * (δ ^ (-2 * η) * n * γ ^ σ) * δ ^ 2)
      ≤ 256 * (1 + Real.log (1 / δ)) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) +
        60000 * (1 + Real.log (1 / δ)) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by
        linarith
    _ ≤ 100000 * (1 + Real.log (1 / δ)) * δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2 := by
        have : 0 ≤ (1 + Real.log (1 / δ)) * (δ ^ (-2 * η) * θ ^ (σ / 4) * n * δ ^ 2) := by
          positivity
        linarith

end WangZahlLot.Obl.wz_grains_nonsingular_slices
