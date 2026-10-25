-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.ReplicatedMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Replication
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.ClassMass

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

lemma ncard_reindex_real {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : β → Prop) :
    (ncard {a | P (e a)} : ℝ) = (ncard {b | P b} : ℝ) := by
  classical
  simp only [WangZahlLot.Obl.wz_nsp_translation_model.ncard_eq_sum]
  exact e.sum_comp (fun b => if P b then (1 : ℝ) else 0)

lemma CinematicMomentAt.fintype {r η ε : ℝ} {f : ℝ → ℝ}
    (hC : CinematicMomentAt r η ε f) {ι : Type*} [Fintype ι] (q : ι → Space)
    (hnorm : ∀ i, ‖q i‖ ≤ 10)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (q i) (q j))
    (hcount : ∀ (b : Space) (s : ℝ), r ≤ s → s ≤ 1 →
      (ncard {i | q i ∈ ball b s} : ℝ) ≤ r ^ (-η) * (s / r)) :
    (∫⁻ p : ℝ × ℝ, multiplicity (fun i => graphStrip r f 0 (q i)) p ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (r ^ (-ε)) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hc := hC (Fintype.card ι) (fun i => q (e i)) (fun i => hnorm _)
    (fun i j hij => hsep _ _ (e.injective.ne hij)) (fun b s hrs hs1 => by
      rw [ncard_reindex_real e (fun i => q i ∈ ball b s)]
      exact hcount b s hrs hs1)
  have hm (p : ℝ × ℝ) :
      multiplicity (fun i => graphStrip r f 0 (q (e i))) p =
        multiplicity (fun i => graphStrip r f 0 (q i)) p := by
    exact e.sum_comp (fun i => (graphStrip r f 0 (q i)).indicator (fun _ => (1 : ℝ≥0∞)) p)
  simpa only [hm] using hc

/-- The planar action of a translation in cinematic parameter space. -/
def cinematicShear {f : ℝ → ℝ} (hf : Measurable f) (t : Space) :
    (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  horizontalShear (h := fun z => t 0 + t 1 * f z + t 2 * z * f z) (by fun_prop)

lemma cinematicShear_graphStrip {f : ℝ → ℝ} (hf : Measurable f)
    (r c : ℝ) (q t : Space) :
    cinematicShear hf t '' graphStrip r f c q ⊆ graphStrip r f c (q + t) := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨hp.1, ?_⟩
  change |p.1 + (t 0 + t 1 * f p.2 + t 2 * p.2 * f p.2) -
    ((q + t) 0 + c * p.2 + (q + t) 1 * f p.2 + (q + t) 2 * p.2 * f p.2)| ≤ r
  have he : p.1 + (t 0 + t 1 * f p.2 + t 2 * p.2 * f p.2) -
      ((q + t) 0 + c * p.2 + (q + t) 1 * f p.2 + (q + t) 2 * p.2 * f p.2) =
      p.1 - (q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2) := by
    simp only [PiLp.add_apply]
    ring
  rw [he]
  exact hp.2

lemma volume_cinematicShear_image {f : ℝ → ℝ} (hf : Measurable f)
    (t : Space) (E : Set (ℝ × ℝ)) : volume (cinematicShear hf t '' E) = volume E :=
  volume_horizontalShear_image _ E

/-- Replication amplifies the cubic mass bound by the square of the number of copies. -/
theorem replicated_planar_mass_bound {f : ℝ → ℝ} (hf : Continuous f)
    {r c η ε : ℝ} {m n : ℕ} (hm : 0 < m) (q : Fin n → Space) (t : Fin m → Space)
    (T : Fin n → Set (ℝ × ℝ)) (hT : ∀ i, T i ⊆ graphStrip r f c (q i))
    (hC : CinematicMomentAt r η ε f)
    (hnorm : ∀ p : Fin m × Fin n, ‖q p.2 + t p.1‖ ≤ 10)
    (hsep : ∀ p p' : Fin m × Fin n, p ≠ p' →
      r ≤ dist (q p.2 + t p.1) (q p'.2 + t p'.1))
    (hcount : ∀ (b : Space) (s : ℝ), r ≤ s → s ≤ 1 →
      (ncard {p : Fin m × Fin n | q p.2 + t p.1 ∈ ball b s} : ℝ) ≤
        r ^ (-η) * (s / r)) :
    (m : ℝ≥0∞) ^ 2 * (∑ i, volume (T i)) ^ 3 ≤
      volume (⋃ i, T i) * ENNReal.ofReal (r ^ (-ε)) ^ 2 := by
  classical
  let S (p : Fin m × Fin n) := graphStrip r f c (q p.2 + t p.1)
  let U (p : Fin m × Fin n) := cinematicShear hf.measurable (t p.1) '' T p.2
  have hUS (p : Fin m × Fin n) : U p ⊆ S p :=
    (image_mono (hT p.2)).trans (cinematicShear_graphStrip hf.measurable _ _ _ _)
  have hmoment : (∫⁻ p : ℝ × ℝ, multiplicity S p ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (r ^ (-ε)) := by
    dsimp only [S]
    rw [lintegral_graphStrip_shear]
    exact hC.fintype _ hnorm hsep hcount
  have hsum : (∑ p, volume (U p)) = (m : ℝ≥0∞) * ∑ i, volume (T i) := by
    simp only [U, volume_cinematicShear_image, Fintype.sum_prod_type, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hunion : volume (⋃ p, U p) ≤ (m : ℝ≥0∞) * volume (⋃ i, T i) := by
    have he : (⋃ p, U p) = ⋃ s, cinematicShear hf.measurable (t s) '' (⋃ i, T i) := by
      simp only [U, iUnion_prod', image_iUnion]
    rw [he]
    calc
      _ ≤ ∑ s, volume (cinematicShear hf.measurable (t s) '' (⋃ i, T i)) :=
        measure_iUnion_fintype_le volume _
      _ = _ := by simp only [volume_cinematicShear_image, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb := sum_outer_measure_cubed_le_moment (S := S) (T := U) volume
    (fun p => measurableSet_graphStrip hf r c (q p.2 + t p.1)) hUS
  rw [hsum] at hb
  have hh := hb.trans (mul_le_mul' hunion (pow_le_pow_left' hmoment 2))
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  apply (ENNReal.mul_le_mul_iff_right hm0 (by simp)).mp
  convert hh using 1 <;> ring

/-- A cinematic parameter class confined to a `rho`-ball has a quantitative area bound.
The bound holds for arbitrary planar subsets of its strips and uses outer volume. -/
theorem parameter_class_mass_bound {f : ℝ → ℝ} (hf : Continuous f)
    {r ρ c A η ε : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ1 : ρ ≤ 1) (hA : 0 ≤ A)
    {n : ℕ} (q : Fin n → Space) (a : Space) (T : Fin n → Set (ℝ × ℝ))
    (hT : ∀ i, T i ⊆ graphStrip r f c (q i))
    (hdiam : ∀ i, dist (q i) a ≤ ρ) (hnorm : ∀ i, ‖q i‖ ≤ 5)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (q i) (q j))
    (hn : (n : ℝ) ≤ A * (ρ / r))
    (hc : ∀ (b : Space) (s : ℝ), r ≤ s → s ≤ 1 →
      (ncard {i | q i ∈ ball b s} : ℝ) ≤ A * (s / r))
    (hC : CinematicMomentAt r η ε f) (hAη : 3456 * A ≤ r ^ (-η)) :
    (∑ i, volume (T i)) ^ 3 ≤
      ENNReal.ofReal (128000 * ρ) ^ 2 *
        (volume (⋃ i, T i) * ENNReal.ofReal (r ^ (-ε)) ^ 2) := by
  obtain ⟨m, t, hm, hcard, ht, hqnorm, hqsep, hqcount⟩ :=
    exists_parameter_replication hr hrρ hρ1 hA q a hdiam hnorm hsep hn hc
  have hb := replicated_planar_mass_bound hf hm q t T hT hC hqnorm hqsep
    (fun b s hrs hs1 => (hqcount b s hrs hs1).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hAη
        (div_nonneg (hr.le.trans hrs) hr.le)))
  have hρ : 0 < ρ := hr.trans_le hrρ
  have hcardE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (128000 * ρ) * (m : ℝ≥0∞) := by
    have hh := ENNReal.ofReal_le_ofReal hcard
    rw [ENNReal.ofReal_one] at hh
    convert hh using 1
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    _ ≤ (ENNReal.ofReal (128000 * ρ) * (m : ℝ≥0∞)) ^ 2 * (∑ i, volume (T i)) ^ 3 := by
      simpa only [one_pow, one_mul] using
        (mul_le_mul' (pow_le_pow_left' hcardE 2)
          (le_rfl : (∑ i, volume (T i)) ^ 3 ≤ (∑ i, volume (T i)) ^ 3))
    _ = ENNReal.ofReal (128000 * ρ) ^ 2 * ((m : ℝ≥0∞) ^ 2 * (∑ i, volume (T i)) ^ 3) := by
      rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl hb


/-- The replicated class bound transferred back to the mass of transverse tube shadings. -/
theorem tube_parameter_class_mass_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ h ρ c A η ε : ℝ} (hδ : 0 < δ) (hh : 0 ≤ h)
    (hrρ : 12 * δ + h ≤ ρ) (hρ1 : ρ ≤ 1) (hA : 0 ≤ A)
    {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space) (a : Space)
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hclass : ∀ i, |slope (v i) 0 - c| ≤ h)
    (hdiam : ∀ i, dist (parameters (x i) (v i)) a ≤ ρ)
    (hsep : ∀ i j, i ≠ j → 12 * δ + h ≤
      dist (parameters (x i) (v i)) (parameters (x j) (v j)))
    (hn : (n : ℝ) ≤ A * (ρ / (12 * δ + h)))
    (hc : ∀ (b : Space) (s : ℝ), 12 * δ + h ≤ s → s ≤ 1 →
      (ncard {i | parameters (x i) (v i) ∈ ball b s} : ℝ) ≤
        A * (s / (12 * δ + h)))
    (hC : CinematicMomentAt (12 * δ + h) η ε f)
    (hAη : 3456 * A ≤ (12 * δ + h) ^ (-η)) :
    (∑ i, volume (Y i)) ^ 3 ≤
      ENNReal.ofReal (6 * δ) ^ 3 * ENNReal.ofReal (128000 * ρ) ^ 2 *
        (volume (projection f '' (⋃ i, Y i)) *
          ENNReal.ofReal ((12 * δ + h) ^ (-ε)) ^ 2) := by
  have hnorm (i : Fin n) : ‖parameters (x i) (v i)‖ ≤ 5 := by
    have hx : x i ∈ Tube δ (x i) (v i) :=
      mem_thickening_iff.mpr ⟨x i, left_mem_segment ℝ _ _, by simpa using hδ⟩
    exact parameters_norm_le_five (by simpa using (mem_ball_zero_iff.mp (hball i hx)).le)
      (hv i) (htrans i)
  have hT (i : Fin n) : projection f '' Y i ⊆
      graphStrip (12 * δ + h) f c (parameters (x i) (v i)) :=
    ((image_mono (hY i)).trans
      (projection_tube_subset_strip hf hderiv hf0 (hv i) (htrans i) (hball i))).trans
        (graphStrip_subset_of_abs_sub_le (hclass i))
  have harea := parameter_class_mass_bound hf.continuous (by linarith : 0 < 12 * δ + h)
    hrρ hρ1 hA (fun i => parameters (x i) (v i)) a
    (fun i => projection f '' Y i) hT hdiam hnorm hsep hn hc hC hAη
  rw [← image_iUnion] at harea
  have hmass : (∑ i, volume (Y i)) ≤
      ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      volume_le_projection_volume hf.continuous.measurable hδ (hv i) (htrans i) (hY i)
  calc
    _ ≤ (ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i)) ^ 3 :=
      pow_le_pow_left' hmass 3
    _ = ENNReal.ofReal (6 * δ) ^ 3 * (∑ i, volume (projection f '' Y i)) ^ 3 :=
      mul_pow _ _ _
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal (6 * δ) ^ 3)) harea

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
