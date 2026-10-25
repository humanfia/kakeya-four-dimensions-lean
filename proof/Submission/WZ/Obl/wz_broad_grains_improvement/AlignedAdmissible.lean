-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedAdmissible.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedPreparation
import Submission.WZ.Obl.wz_multiscale_finite_tower.DenseRestriction
import Submission.WZ.Obl.wz_multiscale_finite_tower.WeightedSeparation
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Containers

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_multiscale_finite_tower (AlignedFamily axisMidpoint)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (doubled SlabBound)

set_option maxHeartbeats 800000

private lemma centered_root_norm {u q : V} (hu : ‖u‖ = 1)
    (hq : q ∈ doubled 1 (-(1 / 2 : ℝ) • u) u) : ‖q‖ < 3 := by
  obtain ⟨t, ht, hnear⟩ :=
    WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  have he : -(1 / 2 : ℝ) • u - (1 / 2 : ℝ) • u + t • (2 • u) =
      (2 * t - 1) • u := by module
  change ‖q - (-(1 / 2 : ℝ) • u - (1 / 2 : ℝ) • u + t • (2 • u))‖ < 2 * 1 at hnear
  rw [he] at hnear
  have ht' : |2 * t - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnorm : ‖(2 * t - 1) • u‖ ≤ 1 := by
    simpa only [norm_smul, Real.norm_eq_abs, hu, mul_one] using ht'
  have hh := norm_add_le (q - (2 * t - 1) • u) ((2 * t - 1) • u)
  rw [sub_add_cancel] at hh
  linarith

private lemma centered_root_buffer {u p : V} (hu : ‖u‖ = 1)
    (hp : ‖p‖ ≤ 7 / 8) {b : ℝ} (hb : |b| ≤ 1 / 100) :
    AffineMap.homothety p b '' doubled 1 (-(1 / 2 : ℝ) • u) u ⊆ I := by
  rintro _ ⟨q, hq, rfl⟩
  have hq' := centered_root_norm hu hq
  have hnorm : ‖AffineMap.homothety p b q‖ ≤ ‖p‖ + |b| * (‖q‖ + ‖p‖) := by
    change ‖b • (q - p) + p‖ ≤ _
    calc
      _ ≤ ‖b • (q - p)‖ + ‖p‖ := norm_add_le _ _
      _ = |b| * ‖q - p‖ + ‖p‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |b| * (‖q‖ + ‖p‖) + ‖p‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by ring
  have hbound : |b| * (‖q‖ + ‖p‖) ≤ (1 / 100 : ℝ) * (3 + 7 / 8) := by
    exact mul_le_mul hb (by linarith) (by positivity) (by norm_num)
  change dist (AffineMap.homothety p b q) 0 < 1
  rw [dist_zero_right]
  linarith

/-- An aligned family has the global unit-ball slab bound with a fixed loss.
The interior midpoint bound supplies the buffer needed to compare the root
domain with the unit ball. -/
theorem aligned_family_frostman {d lam K₀ L₀ h : ℝ} {u : V} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} (hd : 0 < d)
    (hF : AlignedFamily d lam K₀ L₀ u h n x v Y) :
    F d (16000000 * L₀) n x v := by
  have hp (i : Fin n) : axisMidpoint (x i) (v i) ∈ T d (x i) (v i) := by
    apply self_subset_thickening hd
    simpa only [axisMidpoint, zero_smul, add_zero] using
      WangZahlLot.Obl.wz_rescaled_fibre_alternatives.centered_segment
        (x i) (v i) (a := 0) (by norm_num)
  have hsub : I ⊆ doubled 1 (-(1 / 2 : ℝ) • u) u :=
    WangZahlLot.Obl.wz_multiscale_finite_tower.centered_doubled_root_contains_ball u
  have hs := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slabBound_of_comparable
    (D := I) (E := doubled 1 (-(1 / 2 : ℝ) • u) u)
    (a := 1 / 100) (B := 1) (C := 1)
    (P := fun _ : Fin n => True)
    (U := fun i => T d (x i) (v i)) (V := fun i => T d (x i) (v i))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun i => axisMidpoint (x i) (v i))
    (fun i _ => hp i) (fun i _ => (hF.ball i).trans hsub)
    (fun i _ => by simp)
    (fun i _ => centered_root_buffer hF.root_unit (hF.midpoint i) (by norm_num))
    (fun i _ => centered_root_buffer hF.root_unit (hF.midpoint i) (by norm_num))
    (by simpa only [ENNReal.ofReal_one, one_mul] using
      (measure_mono hsub : μ I ≤ μ (doubled 1 (-(1 / 2 : ℝ) • u) u))) hF.slab
  have hs' : SlabBound I (2000000 * L₀) (fun _ : Fin n => True)
      (fun i => T d (x i) (v i)) := by norm_num at hs ⊢; exact hs
  intro w t r hw hr
  have hraw := hs' w t r hw hr
  simp only [WangZahlLot.Obl.wz_rescaled_fibre_alternatives.slab,
    true_and, Set.ofPred_true, Set.ncard_univ, Nat.card_fin] at hraw
  have hball : (1 : ENNReal) ≤ 8 * μ I := by
    calc
      _ = 8 * O (1 / 8 : ℝ) := by
        rw [show (8 : ENNReal) = O (8 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        norm_num [O]
      _ ≤ _ := mul_le_mul_right
        WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_unit_ball_lower (8 : ENNReal)
  calc
    _ ≤ O (q n {i | T d (x i) (v i) ⊆ I ∩ Q w t r}) * (8 * μ I) := by
      simpa only [mul_one] using mul_le_mul_right hball
        (O (q n {i | T d (x i) (v i) ⊆ I ∩ Q w t r}))
    _ = 8 * (O (q n {i | T d (x i) (v i) ⊆ I ∩ Q w t r}) * μ I) := by ac_rfl
    _ ≤ 8 * (O (2000000 * L₀ * n) * μ (I ∩ Q w t r)) := mul_le_mul_right hraw 8
    _ = _ := by
      rw [← mul_assoc, show (8 : ENNReal) = O (8 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      congr 2
      ring

/-- Essential separation of an aligned family retains any fraction allowed by
the weighted conflict bound. Alignment, individual density, and convex counts
are unchanged; the relative slab coefficient pays the cardinality ratio. -/
theorem aligned_family_distinct {d lam K₀ L₀ h τ : ℝ} {u : V} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1 / 100000) (hlam : 0 < lam) (hK : 0 ≤ K₀)
    (hτ : 0 ≤ τ) (hcost : τ * (10000000000000 * K₀) ≤ 1)
    (hF : AlignedFamily d lam K₀ L₀ u h n x v Y) :
    ∃ (m : ℕ) (e : Fin m → Fin n), Function.Injective e ∧ m ≤ n ∧
      AlignedFamily d lam K₀ (L₀ * n / m) u h m (x ∘ e) (v ∘ e) (Y ∘ e) ∧
      X d m (x ∘ e) (v ∘ e) ∧
      O τ * (∑ i, μ (Y i)) ≤ ∑ i, μ (Y (e i)) ∧
      (τ * lam / 56) * n ≤ m := by
  classical
  have hfin (i : Fin n) : μ (Y i) ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono ((hF.shading i).trans (hF.ball i)))
  have hpos : 0 < ∑ i, (μ (Y i)).toReal := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hF.nonempty
    have hm := (ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.sum_ne_top.mpr (fun i _ => hfin i))).mp hF.mass_lower
    rw [ENNReal.toReal_sum (fun i _ => hfin i)] at hm
    exact (by positivity : 0 < lam * n * d ^ 2).trans_le hm
  obtain ⟨S, hS, hweight, hsep⟩ :=
    WangZahlLot.Obl.wz_multiscale_finite_tower.weighted_distinct_selection hd hd1 hK
      x v hF.unit hF.count (fun i => (μ (Y i)).toReal)
      (fun _ => ENNReal.toReal_nonneg) hpos
  have hretR : τ * (∑ i, (μ (Y i)).toReal) ≤ ∑ i ∈ S, (μ (Y i)).toReal := by
    calc
      _ ≤ τ * ((10000000000000 * K₀) * ∑ i ∈ S, (μ (Y i)).toReal) :=
        mul_le_mul_of_nonneg_left hweight hτ
      _ = (τ * (10000000000000 * K₀)) * ∑ i ∈ S, (μ (Y i)).toReal := by ring
      _ ≤ 1 * ∑ i ∈ S, (μ (Y i)).toReal := by
        exact mul_le_mul_of_nonneg_right hcost (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      _ = _ := one_mul _
  have hret : O τ * (∑ i, μ (Y i)) ≤ ∑ i ∈ S, μ (Y i) := by
    apply (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.mpr (fun i _ => hfin i)))
      (ENNReal.sum_ne_top.mpr (fun i _ => hfin i))).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hτ,
      ENNReal.toReal_sum (fun i _ => hfin i), ENNReal.toReal_sum (fun i _ => hfin i)]
    exact hretR
  let e := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate S
  have he : Function.Injective e := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_injective S
  have hm : 0 < S.card := Finset.card_pos.mpr hS
  have hmR : (0 : ℝ) < S.card := Nat.cast_pos.mpr hm
  have hsum : (∑ i, μ (Y (e i))) = ∑ i ∈ S, μ (Y i) :=
    WangZahlLot.Obl.wz_tower_balanced_refinement.sum_enumerate S (fun i => μ (Y i))
  refine ⟨S.card, e, he, ?_, ?_, ?_, by rwa [hsum], ?_⟩
  · simpa using (Finset.card_le_univ S)
  · exact hF.reindex e he hm (Y ∘ e) (fun i => hF.measurable (e i))
      (fun _ => Subset.rfl) (fun i => hF.density (e i))
      (by rw [div_mul_cancel₀ _ hmR.ne'])
  · intro i j hij
    exact hsep (e i) (WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem S i)
      (e j) (WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem S j) (fun h => hij (he h))
  · exact WangZahlLot.Obl.wz_multiscale_finite_tower.retained_subset_cardinality hd hτ S
      hF.mass_lower (fun i _ => (measure_mono (hF.shading i)).trans
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper hd.le
          (hd1.trans (by norm_num)) _ _ (hF.unit i))) hret

/-- Initial scalar alignment can be combined with essential separation without
losing normalized admissibility. Every loss is an arbitrarily small power of
the bottom scale, and the retained union is contained in the original union. -/
theorem prepare_aligned_admissible {ε D₀ : ℝ} (hε : 0 < ε) (hD : 0 < D₀) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ D₀ ∧ d₀ ≤ 1 / 100000 ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ n x v Y,
      A d η (d ^ (-η)) (d ^ (-η)) n x v Y →
    ∃ (m : ℕ) (x' v' : Fin m → V) (Z : Fin m → Set V) (u : V) (h : ℝ),
      A d ε (d ^ (-ε)) (d ^ (-ε)) m x' v' Z ∧
      AlignedFamily d (d ^ ε) (d ^ (-ε)) (d ^ (-ε)) u h m x' v' Z ∧
      m ≤ n ∧ (⋃ i, Z i) ⊆ (⋃ i, Y i) ∧
      O (d ^ ε) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Z i) := by
  let θ := ε / 10
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨d₁, hd₁, hd₁D, hcut⟩ :=
    WangZahlLot.Obl.wz_multiscale_finite_tower.exists_scale_cutoff
      (1 / 1000000000000000) θ D₀ (by norm_num) hθ hD
  obtain ⟨η₀, d₀, hη₀, hd₀, hd₀₁, hd₀small, hprepare⟩ :=
    WangZahlLot.Obl.wz_multiscale_finite_tower.prepare_aligned_family hθ hd₁
  refine ⟨min η₀ ε, d₀, lt_min hη₀ hε, min_le_right _ _, hd₀,
    hd₀₁.trans hd₁D, hd₀small, ?_⟩
  intro d hd hdd n x v Y hA
  have hdsmall : d ≤ 1 / 100000 := hdd.trans hd₀small
  have hd1 : d ≤ 1 := hdsmall.trans (by norm_num)
  have hbase : 1000000000000000 * d ^ θ ≤ 1 := by
    have hh := hcut d hd (hdd.trans hd₀₁)
    linarith
  have hcoef (C₀ b : ℝ) (hC : 0 ≤ C₀) (hCB : C₀ ≤ 1000000000000000)
      (hb : θ ≤ b) : C₀ * d ^ b ≤ 1 :=
    WangZahlLot.Obl.wz_multiscale_finite_tower.power_coefficient_bound hd hd1 hC hCB hb hbase
  have hA₀ : A d η₀ (d ^ (-η₀)) (d ^ (-η₀)) n x v Y :=
    admissible_mono hd hd1 (min_le_left _ _) hA
  obtain ⟨m, x₀, v₀, Y₀, u, h, hF₀, hmn, hU₀, hmass₀⟩ :=
    hprepare d hd hdd n x v Y hA₀
  have hcost : d ^ (2 * θ) * (10000000000000 * d ^ (-θ)) ≤ 1 := by
    calc
      _ = 10000000000000 * d ^ θ := by
        rw [mul_left_comm, ← Real.rpow_add hd]
        congr 1
        congr 1
        ring
      _ ≤ 1 := hcoef _ _ (by norm_num) (by norm_num) le_rfl
  obtain ⟨k, e, he, hkm, hF, hsep, hret, hcard⟩ := aligned_family_distinct
    hd hdsmall (Real.rpow_pos_of_pos hd θ) (Real.rpow_nonneg hd.le (-θ))
    (Real.rpow_nonneg hd.le (2 * θ)) hcost hF₀
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hF.nonempty
  have hcard' : (d ^ (3 * θ) / 56) * m ≤ k := by
    simpa only [← Real.rpow_add hd, show 2 * θ + θ = 3 * θ by ring] using hcard
  have hratio : d ^ (-θ) * m / k ≤ 56 * d ^ (-(4 * θ)) := by
    apply (div_le_iff₀ hk).mpr
    have hh := mul_le_mul_of_nonneg_left hcard' (by positivity : 0 ≤ 56 * d ^ (-(4 * θ)))
    have hid : (56 * d ^ (-(4 * θ))) * (d ^ (3 * θ) / 56 * m) = d ^ (-θ) * m := by
      calc
        _ = (d ^ (-(4 * θ)) * d ^ (3 * θ)) * m := by ring
        _ = _ := by rw [← Real.rpow_add hd]; congr 2; ring
    rwa [hid] at hh
  have hroot : 16000000 * (d ^ (-θ) * m / k) ≤ d ^ (-ε) := by
    calc
      _ ≤ 16000000 * (56 * d ^ (-(4 * θ))) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 896000000 * d ^ (-(4 * θ)) := by ring
      _ ≤ d ^ (-ε) := WangZahlLot.Obl.wz_multiscale_finite_tower.inverse_power_error_bound hd
        (hcoef _ _ (by norm_num) (by norm_num) (by dsimp [θ]; linarith))
  have hroot' : d ^ (-θ) * m / k ≤ d ^ (-ε) := by
    have hn : 0 ≤ d ^ (-θ) * m / k := by positivity
    linarith
  have hθε : θ ≤ ε := by dsimp [θ]; linarith
  have hden : d ^ ε ≤ d ^ θ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hθε
  have hKT : d ^ (-θ) ≤ d ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθε)
  have hF' := hF.mono hden hKT hroot'
  have hFrost : F d (d ^ (-ε)) k (x₀ ∘ e) (v₀ ∘ e) := by
    intro w t r hw hr
    exact (aligned_family_frostman hd hF w t r hw hr).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hroot (Nat.cast_nonneg k))) _)
  refine ⟨k, x₀ ∘ e, v₀ ∘ e, Y₀ ∘ e, u, h,
    ⟨hF'.nonempty, fun i => ⟨hF'.unit i, hF'.ball i, hF'.measurable i, hF'.shading i⟩,
      hsep, hF'.mass_lower, hF'.count, hFrost⟩,
    hF', hkm.trans hmn, ?_, ?_⟩
  · exact (iUnion_subset fun i => subset_iUnion Y₀ (e i)).trans hU₀
  · have hkeep : O (d ^ (3 * θ)) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Y₀ (e i)) := by
      calc
        _ = O (d ^ (2 * θ)) * (O (d ^ θ) * ∑ i, μ (Y i)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),
            ← Real.rpow_add hd]
          congr 3
          ring
        _ ≤ O (d ^ (2 * θ)) * (∑ i, μ (Y₀ i)) := mul_le_mul_right hmass₀ _
        _ ≤ _ := hret
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by dsimp [θ]; linarith : 3 * θ ≤ ε))) _).trans hkeep

end WangZahlLot.Obl.wz_broad_grains_improvement
