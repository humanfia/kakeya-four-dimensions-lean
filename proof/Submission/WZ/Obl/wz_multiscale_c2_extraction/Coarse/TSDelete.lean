-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSDelete.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSFibreMain
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.Incidence

/-!
# Fibre multiplicity deletion

Points where one fibre has too many shadings carry little mass: otherwise the
rescaled fibre, restricted to them, would be a frozen family at the finer scale
whose union is smaller than the volume lower bound allows.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical RealInnerProductSpace
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- Shadings of the fibre of `j`. -/
def fibreShading {n k : ℕ} (fc : Fin n → Fin k) (Y : Fin n → Set Space) (j : Fin k)
    (i : Fin n) : Set Space :=
  if fc i = j then Y i else ∅

theorem incidence_fibreShading {n k : ℕ} (fc : Fin n → Fin k) (Y : Fin n → Set Space)
    (j : Fin k) (p : Space) :
    incidence (fibreShading fc Y j) p = ({i | fc i = j ∧ p ∈ Y i}.ncard : ℝ) := by
  rw [incidence_eq_ncard]
  congr 2
  ext i
  simp only [fibreShading, mem_setOf_eq]
  split_ifs with h <;> simp [h]

/-- The high-multiplicity part of one fibre carries little mass. -/
theorem fibre_high_small {η δ ρ lam0 a b δ' ηs tc θ τ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hη : 0 < η)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hv : ∀ i, ‖v i‖ = 1) (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hhalf : ∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i)))
    (hY : ∀ i, MeasurableSet (Y i)) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hS : Separated η δ n x v)
    {k : ℕ} {z w : Fin k → Space}
    (huniq : ∀ i, ∃! j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j))
    (hfrostρ : ∀ j (W : Set Space), Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧
          tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal (δ ^ (-η) * ({i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j)}.ncard : ℝ)) *
          volume W)
    (hdilρ : ∀ i j j', Tube δ (x i) (v i) ⊆ Dilate ρ (z j) (w j) →
      Tube δ (x i) (v i) ⊆ Dilate ρ (z j') (w j') → j = j')
    (j0 : Fin k) (hw0 : ‖w j0‖ = 1)
    (hδρ : δ ≤ ρ) (hρ : ρ ≤ 1 / 1000) (hlam0 : lam0 ≤ 1 / 100) (hlamρ : ρ ≤ lam0)
    (hlam8 : 1 / 10 ^ 8 ≤ lam0)
    (ha : a = lam0 / ρ) (hb : b = 1 / (1 + 144 * lam0 ^ 2)) (hδ'def : δ' = b * a * δ)
    (hδ'small : δ' ≤ 1 / 10000000)
    (hC2a : 34 * δ ^ (-(2 * η)) ≤ δ' ^ (-ηs))
    (hC2b : δ' ^ ηs ≤ δ ^ (2 * η) / (34 * 10 ^ 7))
    (hC2c : 2312 * δ ^ (-η) / lam0 ^ 2 / tc ≤ δ' ^ (-ηs)) (htc : 0 < tc)
    (hlow : ∀ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space),
      Family ηs δ' m x' v' Y' → Separated ηs δ' m x' v' →
        ENNReal.ofReal (δ' ^ t) < volume (⋃ q, Y' q))
    (hθ : 0 < θ)
    (hτ : τ = ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈η⁻¹⌉₊ + 3) *
      (2 * δ' ^ ηs + 384 * tc * ((⌈η⁻¹⌉₊ + 3 : ℕ) : ℝ)))
    (hunion : b ^ 3 * a ^ 2 * (384 * δ ^ 2 / θ) ≤ δ' ^ t)
    (fc : Fin n → Fin k) (hfc : ∀ i, Tube δ (x i) (v i) ⊆ Tube ρ (z (fc i)) (w (fc i))) :
    ∑ i ∈ Finset.univ.filter (fun i => fc i = j0),
        (volume (Y i ∩ {p | θ * ({i | fc i = j0}.ncard : ℝ) <
          incidence (fibreShading fc Y j0) p})).toReal ≤
      τ * ({i | fc i = j0}.ncard : ℝ) * δ ^ 2 := by
  classical
  set H : Set Space := {p | θ * ({i | fc i = j0}.ncard : ℝ) <
    incidence (fibreShading fc Y j0) p} with hH_def
  have hfcu : ∀ i j, Tube δ (x i) (v i) ⊆ Tube ρ (z j) (w j) → j = fc i :=
    fun i j h => (huniq i).unique h (hfc i)
  have hfibre : Finset.univ.filter (fun i => Tube δ (x i) (v i) ⊆ Tube ρ (z j0) (w j0)) =
      Finset.univ.filter (fun i => fc i = j0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact (hfcu i j0 h).symm
    · intro h; rw [← h]; exact hfc i
  have hFcard : ({i | fc i = j0}.ncard : ℝ) =
      ((Finset.univ.filter (fun i => fc i = j0)).card : ℝ) := by
    rw [WangZahlLot.Obl.wz_separated_cover_refinement.ncard_setOf]
  have hYfin : ∀ i, volume (Y i) ≤ ENNReal.ofReal (384 * δ ^ 2) := fun i =>
    (measure_mono (hYT i)).trans
      (WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ (by linarith) _ _ (hv i))
  have hHmeas : MeasurableSet H :=
    measurableSet_lt measurable_const (measurable_incidence (fun i => by
      unfold fibreShading; split_ifs; exacts [hY i, MeasurableSet.empty]))
  by_contra hbig
  push Not at hbig
  set F := Finset.univ.filter (fun i => fc i = j0) with hF_def
  set ω : Fin n → ℝ := fun i => if fc i = j0 then (volume (Y i ∩ H)).toReal else 0 with hω_def
  have hω0 : ∀ i, 0 ≤ ω i := by
    intro i; simp only [hω_def]; split_ifs <;> simp
  have hωM : ∀ i, ω i ≤ 384 * δ ^ 2 := by
    intro i
    simp only [hω_def]
    split_ifs
    · have h := (measure_mono (μ := volume) (inter_subset_left : Y i ∩ H ⊆ Y i)).trans (hYfin i)
      exact (ENNReal.toReal_le_of_le_ofReal (by positivity) h)
    · positivity
  have hsumF : ∑ i ∈ F, ω i = ∑ i ∈ F, (volume (Y i ∩ H)).toReal := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hω_def, (Finset.mem_filter.mp hi).2, if_true]
  obtain ⟨m, ι, hιinj, hιF, hιgeo, hιhalf, hιsep, hιmass⟩ := fibre_family (lam0 := lam0)
    (a := a) (b := b) (δ' := δ') (η' := ηs) (t := tc) (Mw := 384 * δ ^ 2) hδ hδ1 hη hv hball
    hhalf hS huniq hfrostρ hdilρ j0 hw0 rfl hδρ hρ hlam0 hlamρ hlam8 ha hb hδ'def hδ'small
    hC2a hC2b hC2c htc ω hω0 hωM (by positivity)
  rw [hfibre] at hιmass
  -- notation for the rescaled family
  set w0 := w j0 with hw0_def
  set c0 := z j0 + (1 / 2 : ℝ) • w j0 with hc0_def
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hlam0pos : 0 < lam0 := lt_of_lt_of_le hρ0 hlamρ
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have hbhalf : 1 / 2 ≤ b := by
    rw [hb, le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg lam0]
  have hFpos : (0 : ℝ) < F.card := by
    rcases Nat.eq_zero_or_pos F.card with h0 | h0
    · exfalso
      have hFe : F = ∅ := Finset.card_eq_zero.mp h0
      rw [hFcard, hFe] at hbig
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, Finset.sum_empty] at hbig
      exact lt_irrefl _ hbig
    · exact_mod_cast h0
  rw [hFcard] at hbig
  have hδ'0 : 0 < δ' := by rw [hδ'def]; positivity
  have hδ'η : 0 ≤ δ' ^ ηs := Real.rpow_nonneg hδ'0.le ηs
  -- the retained rescaled mass is large
  set L : ℕ := ⌈η⁻¹⌉₊ + 3
  set B : ℝ := ((10 ^ 61 + 1 : ℕ) : ℝ) ^ L
  have hBpos : 0 < B := by positivity
  have hret : 2 * δ' ^ ηs * F.card * δ ^ 2 < ∑ q, ω (ι q) := by
    have h1 : τ * F.card * δ ^ 2 / B < (∑ i ∈ F, (volume (Y i ∩ H)).toReal) / B :=
      div_lt_div_of_pos_right hbig hBpos
    have h2 : τ * F.card * δ ^ 2 / B = (2 * δ' ^ ηs + 384 * tc * (L : ℝ)) * F.card * δ ^ 2 := by
      rw [hτ]; field_simp
    have h3 := hιmass
    rw [← hsumF] at h1
    have h4 : (∑ i ∈ F, ω i) / B - 384 * δ ^ 2 * tc * ((L : ℝ) * F.card) ≤ ∑ q, ω (ι q) := h3
    nlinarith
  -- the retained tubes lie in the fibre
  have hιfc : ∀ q, fc (ι q) = j0 := fun q => (hfcu _ j0 (hιF q)).symm
  have hmF : (m : ℝ) ≤ F.card := by
    have h := Finset.card_le_card (show Finset.univ.image ι ⊆ F from by
      intro i hi
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hιfc q⟩)
    rw [Finset.card_image_of_injective _ hιinj, Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      subst h0
      have : ∑ q : Fin 0, ω (ι q) = 0 := Finset.sum_empty
      rw [this] at hret
      have : 0 ≤ 2 * δ' ^ ηs * F.card * δ ^ 2 := by
        have := hFpos.le; positivity
      linarith
    · exact h0
  -- the rescaled family
  set Y' : Fin m → Set Space := fun q => resc w0 c0 a b '' (Y (ι q) ∩ H) with hY'_def
  have hY'vol : ∀ q, volume (Y' q) = ENNReal.ofReal (b ^ 3 * a ^ 2) *
      ENNReal.ofReal (ω (ι q)) := by
    intro q
    simp only [hY'_def, hω_def, hιfc q, if_true]
    rw [volume_image_resc hw0 hb0.le, ENNReal.ofReal_toReal]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono inter_subset_left).trans (hYfin _))
  have hFam : Family ηs δ' m
      (fun q => resc w0 c0 a b (orStart w0 (x (ι q)) (v (ι q))))
      (fun q => ndir w0 a (orDir w0 (v (ι q)))) Y' := by
    refine ⟨hm0, fun q => (hιgeo q).1, fun q => (hιgeo q).2.1, hιhalf, ?_, ?_, ?_⟩
    · intro q
      exact measurableSet_image_resc hw0 ha0.ne' hb0.ne' ((hY _).inter hHmeas)
    · intro q
      exact (image_mono (inter_subset_left.trans (hYT _))).trans (hιgeo q).2.2
    · rw [Finset.sum_congr rfl (fun q _ => hY'vol q), ← Finset.mul_sum,
        ← ENNReal.ofReal_sum_of_nonneg (fun q _ => hω0 _), ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hδ'2 : δ' ^ 2 = b ^ 2 * a ^ 2 * δ ^ 2 := by rw [hδ'def]; ring
      rw [hδ'2]
      have hpos : 0 ≤ δ' ^ ηs := hδ'η
      calc δ' ^ ηs * (m : ℝ) * (b ^ 2 * a ^ 2 * δ ^ 2)
          ≤ δ' ^ ηs * (F.card : ℝ) * (b ^ 2 * a ^ 2 * δ ^ 2) := by gcongr
        _ ≤ b ^ 3 * a ^ 2 * (2 * δ' ^ ηs * F.card * δ ^ 2) := by
            have : 0 ≤ δ' ^ ηs * (F.card : ℝ) * (a ^ 2 * δ ^ 2) * b ^ 2 := by positivity
            nlinarith
        _ ≤ b ^ 3 * a ^ 2 * ∑ q, ω (ι q) :=
            mul_le_mul_of_nonneg_left hret.le (by positivity)
  have hlt := hlow m _ _ Y' hFam (hιsep hm0)
  -- but the union is small
  have hU : (⋃ q, Y' q) ⊆ resc w0 c0 a b '' H := by
    intro p hp
    obtain ⟨q, hq⟩ := mem_iUnion.mp hp
    exact image_mono inter_subset_right hq
  have hHvol : volume H ≤ ENNReal.ofReal (384 * δ ^ 2 / θ) := by
    have hYF : ∀ i, MeasurableSet (fibreShading fc Y j0 i) := fun i => by
      unfold fibreShading; split_ifs; exacts [hY i, MeasurableSet.empty]
    have hYFfin : ∀ i, volume (fibreShading fc Y j0 i) ≠ ⊤ := fun i => by
      unfold fibreShading; split_ifs
      · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hYfin i)
      · simp
    have hmk := high_incidence_volume hYF hYFfin (θ * F.card)
    have hmass : shadingMass (fibreShading fc Y j0) ≤ F.card * (384 * δ ^ 2) := by
      unfold shadingMass
      calc ∑ i, (volume (fibreShading fc Y j0 i)).toReal
          = ∑ i ∈ F, (volume (Y i)).toReal := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => fc i = j0)]
            have h0 : ∑ i ∈ Finset.univ.filter (fun i => ¬fc i = j0),
                (volume (fibreShading fc Y j0 i)).toReal = 0 :=
              Finset.sum_eq_zero (fun i hi => by
                simp [fibreShading, (Finset.mem_filter.mp hi).2])
            rw [h0, add_zero]
            apply Finset.sum_congr rfl
            intro i hi
            simp [fibreShading, (Finset.mem_filter.mp hi).2]
        _ ≤ ∑ i ∈ F, 384 * δ ^ 2 := Finset.sum_le_sum (fun i _ =>
            ENNReal.toReal_le_of_le_ofReal (by positivity) (hYfin i))
        _ = F.card * (384 * δ ^ 2) := by simp
    have hHsub : H ⊆ {p | θ * F.card ≤ incidence (fibreShading fc Y j0) p} := by
      intro p hp
      have : θ * ({i | fc i = j0}.ncard : ℝ) < incidence (fibreShading fc Y j0) p := hp
      rw [hFcard] at this
      exact this.le
    have hθF : 0 < θ * F.card := mul_pos hθ hFpos
    have hsubB : {p | θ * F.card ≤ incidence (fibreShading fc Y j0) p} ⊆ ball 0 1 := by
      intro p hp
      by_contra hpb
      have hnot : p ∉ ⋃ i, fibreShading fc Y j0 i := by
        intro hpu
        obtain ⟨i, hi⟩ := mem_iUnion.mp hpu
        unfold fibreShading at hi
        split_ifs at hi
        · exact hpb (hball i (hYT i hi))
        · exact hi
      have hz := incidence_eq_zero_of_notMem (fibreShading fc Y j0) hnot
      have : θ * F.card ≤ incidence (fibreShading fc Y j0) p := hp
      linarith
    have hfin : volume {p | θ * F.card ≤ incidence (fibreShading fc Y j0) p} ≠ ⊤ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hsubB)
    have hr : (volume {p | θ * F.card ≤ incidence (fibreShading fc Y j0) p}).toReal ≤
        384 * δ ^ 2 / θ := by
      rw [le_div_iff₀ hθ]
      have h1 := hmk.trans hmass
      have h2 : θ * F.card * (volume {p | θ * F.card ≤
          incidence (fibreShading fc Y j0) p}).toReal ≤ F.card * (384 * δ ^ 2) := h1
      nlinarith
    calc volume H ≤ volume {p | θ * F.card ≤ incidence (fibreShading fc Y j0) p} :=
          measure_mono hHsub
      _ = ENNReal.ofReal (volume {p | θ * F.card ≤
            incidence (fibreShading fc Y j0) p}).toReal := (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (384 * δ ^ 2 / θ) := ENNReal.ofReal_le_ofReal hr
  have hsmall : volume (⋃ q, Y' q) ≤ ENNReal.ofReal (δ' ^ t) := by
    calc volume (⋃ q, Y' q) ≤ volume (resc w0 c0 a b '' H) := measure_mono hU
      _ = ENNReal.ofReal (b ^ 3 * a ^ 2) * volume H := volume_image_resc hw0 hb0.le H
      _ ≤ ENNReal.ofReal (b ^ 3 * a ^ 2) * ENNReal.ofReal (384 * δ ^ 2 / θ) := by gcongr
      _ = ENNReal.ofReal (b ^ 3 * a ^ 2 * (384 * δ ^ 2 / θ)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (δ' ^ t) := ENNReal.ofReal_le_ofReal hunion
  exact absurd hlt (not_lt.mpr hsmall)

/-- Deleting the high-multiplicity part of every fibre. -/
theorem fibre_deletion_all {δ θ τ : ℝ} (hθ : 0 < θ)
    {n k : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    (hYfin : ∀ i, volume (Y i) ≠ ⊤) (fc : Fin n → Fin k)
    (hsmall : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => fc i = j),
        (volume (Y i ∩ {p | θ * ({i | fc i = j}.ncard : ℝ) <
          incidence (fibreShading fc Y j) p})).toReal ≤
      τ * ({i | fc i = j}.ncard : ℝ) * δ ^ 2) :
    ∃ Yb : Fin n → Set Space, (∀ i, Yb i ⊆ Y i) ∧ (∀ i, MeasurableSet (Yb i)) ∧
      ∑ i, (volume (Y i)).toReal - τ * n * δ ^ 2 ≤ ∑ i, (volume (Yb i)).toReal ∧
      ∀ j p, ({i | fc i = j ∧ p ∈ Yb i}.ncard : ℝ) ≤ θ * ({i | fc i = j}.ncard : ℝ) := by
  classical
  set H : Fin k → Set Space := fun j => {p | θ * ({i | fc i = j}.ncard : ℝ) <
    incidence (fibreShading fc Y j) p} with hH_def
  have hHm : ∀ j, MeasurableSet (H j) := fun j =>
    measurableSet_lt measurable_const (measurable_incidence (fun i => by
      unfold fibreShading; split_ifs; exacts [hY i, MeasurableSet.empty]))
  refine ⟨fun i => Y i \ H (fc i), fun i => diff_subset, fun i => (hY i).diff (hHm _), ?_, ?_⟩
  · -- mass loss
    have hsplit : ∀ i, (volume (Y i)).toReal =
        (volume (Y i \ H (fc i))).toReal + (volume (Y i ∩ H (fc i))).toReal := by
      intro i
      rw [← ENNReal.toReal_add (ne_top_of_le_ne_top (hYfin i) (measure_mono diff_subset))
        (ne_top_of_le_ne_top (hYfin i) (measure_mono inter_subset_left)),
        add_comm, ← measure_inter_add_diff (Y i) (hHm (fc i))]
    have hloss : ∑ i, (volume (Y i ∩ H (fc i))).toReal ≤ τ * n * δ ^ 2 := by
      rw [← Finset.sum_fiberwise Finset.univ fc (fun i => (volume (Y i ∩ H (fc i))).toReal)]
      calc ∑ j, ∑ i ∈ Finset.univ.filter (fun i => fc i = j), (volume (Y i ∩ H (fc i))).toReal
          = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => fc i = j), (volume (Y i ∩ H j)).toReal := by
            apply Finset.sum_congr rfl; intro j _
            apply Finset.sum_congr rfl; intro i hi
            rw [(Finset.mem_filter.mp hi).2]
        _ ≤ ∑ j, τ * ({i | fc i = j}.ncard : ℝ) * δ ^ 2 := Finset.sum_le_sum (fun j _ => hsmall j)
        _ = τ * n * δ ^ 2 := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]
            congr 2
            have : ∑ j, ({i | fc i = j}.ncard : ℝ) = ∑ j, ((Finset.univ.filter
                (fun i => fc i = j)).card : ℝ) := by
              apply Finset.sum_congr rfl; intro j _
              rw [WangZahlLot.Obl.wz_separated_cover_refinement.ncard_setOf]
            rw [this]
            have h := Finset.card_eq_sum_card_fiberwise (f := fc) (s := Finset.univ)
              (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
            rw [Finset.card_univ, Fintype.card_fin] at h
            exact_mod_cast h.symm
    have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsplit i)
    rw [Finset.sum_add_distrib] at this
    linarith
  · intro j p
    by_cases hp : p ∈ H j
    · have : {i | fc i = j ∧ p ∈ Y i \ H (fc i)} = ∅ := by
        ext i
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        intro hij hpi
        rw [hij] at hpi
        exact hpi.2 hp
      rw [this, Set.ncard_empty, Nat.cast_zero]
      positivity
    · have hle : ({i | fc i = j ∧ p ∈ Y i \ H (fc i)}.ncard : ℝ) ≤
          ({i | fc i = j ∧ p ∈ Y i}.ncard : ℝ) := by
        have hsub : {i | fc i = j ∧ p ∈ Y i \ H (fc i)} ⊆ {i | fc i = j ∧ p ∈ Y i} :=
          fun i hi => ⟨hi.1, hi.2.1⟩
        exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
      have hinc := incidence_fibreShading fc Y j p
      simp only [hH_def, mem_setOf_eq, not_lt] at hp
      linarith

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
