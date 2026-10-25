-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.AlignedFinal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedPreparation
import Submission.WZ.Obl.wz_multiscale_finite_tower.WeightedSeparation
import Submission.WZ.Obl.wz_multiscale_finite_tower.Restriction
import Submission.WZ.Obl.wz_multiscale_finite_tower.Refinement
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Containers

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective sum_enumerate)

lemma KatzTao.to_frostman {d K : ℝ} {n : ℕ} {x v : Fin n → Space}
    (hK : KatzTao d K n x v) (hd : 0 < d) (hn : 0 < n) :
    Frostman d (K / (n * d ^ 2)) n x v := by
  intro u t r hu hr
  have hslab : Convex ℝ {p : Space | |inner ℝ u p - t| ≤ r} :=
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.slab_convex (innerSL ℝ u) t r
  have hh := hK _ ((convex_ball (0 : Space) 1).inter hslab)
  have hd2 : ENNReal.ofReal (d ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hd)).ne'
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hc : ENNReal.ofReal (K / (n * d ^ 2) * n) * ENNReal.ofReal (d ^ 2) = ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_mul' (sq_nonneg d)]
    congr 1
    field_simp
  apply (ENNReal.mul_le_mul_iff_left hd2 ENNReal.ofReal_ne_top).mp
  calc
    _ = ENNReal.ofReal (({i | Tube d (x i) (v i) ⊆ Metric.ball 0 1 ∩
        {p | |inner ℝ u p - t| ≤ r}}.ncard : ℝ) * d ^ 2) :=
      (ENNReal.ofReal_mul' (sq_nonneg d)).symm
    _ ≤ _ := hh
    _ = (ENNReal.ofReal (K / (n * d ^ 2) * n) *
        volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})) * ENNReal.ofReal (d ^ 2) := by
      rw [← hc]
      ac_rfl

/-- After the hierarchy is constructed, weighted essential separation gives
exactly the admissible refinement required by the frozen theorem. -/
theorem retained_tower_of_aligned_family {d θ ε g h : ℝ} {B n : ℕ} {u : Space}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hd : 0 < d) (hd1 : d ≤ 1 / 100000) (hθε : θ ≤ ε)
    (hsmall : 10000000000000 * d ^ (ε - θ) ≤ 1)
    (hF : AlignedFamily d (d ^ θ) (d ^ (-θ)) (d ^ (-θ)) u h n x v Y)
    (hT : Tower false d (d ^ (-θ)) g B n x v) : RetainedTower d ε g B n Y := by
  classical
  have hdle1 : d ≤ 1 := hd1.trans (by norm_num)
  have hfin (i : Fin n) : volume (Y i) ≠ ⊤ := ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono ((hF.shading i).trans (hF.ball i)))
  let w := fun i => (volume (Y i)).toReal
  have hw (i : Fin n) : 0 ≤ w i := ENNReal.toReal_nonneg
  have hpos : 0 < ∑ i, w i := by
    let i : Fin n := ⟨0, hF.nonempty⟩
    have hv : 0 < volume (Y i) :=
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < d ^ θ * d ^ 2)).trans_le (hF.density i)
    exact Finset.sum_pos' (fun i _ => hw i) ⟨i, Finset.mem_univ _, ENNReal.toReal_pos hv.ne' (hfin i)⟩
  obtain ⟨S, hS, hweight, hsep⟩ := weighted_distinct_selection hd hd1
    (Real.rpow_nonneg hd.le _) x v hF.unit hF.count w hw hpos
  have hcoeff : d ^ ε * (10000000000000 * d ^ (-θ)) ≤ 1 := by
    rw [mul_left_comm, ← mul_assoc, mul_assoc, ← Real.rpow_add hd]
    simpa only [sub_eq_add_neg] using hsmall
  have hmassR : d ^ ε * (∑ i, w i) ≤ ∑ i ∈ S, w i := by
    calc
      _ ≤ d ^ ε * ((10000000000000 * d ^ (-θ)) * ∑ i ∈ S, w i) :=
        mul_le_mul_of_nonneg_left hweight (Real.rpow_nonneg hd.le _)
      _ = (d ^ ε * (10000000000000 * d ^ (-θ))) * ∑ i ∈ S, w i := (mul_assoc _ _ _).symm
      _ ≤ 1 * ∑ i ∈ S, w i := mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg fun i _ => hw i)
      _ = _ := one_mul _
  have hmass : ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i ∈ S, volume (Y i) := by
    have hh := ENNReal.ofReal_le_ofReal hmassR
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)] at hh
    simpa only [w, ENNReal.ofReal_toReal (hfin _)] using hh
  let m := S.card
  let f : Fin m → Fin n := enumerate S
  have hm : 0 < m := Finset.card_pos.mpr hS
  have hf : Function.Injective f := enumerate_injective S
  have hden : ENNReal.ofReal (d ^ ε * m * d ^ 2) ≤ ∑ i : Fin m, volume (Y (f i)) := by
    calc
      _ = ∑ _i : Fin m, ENNReal.ofReal (d ^ ε * d ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
        congr 1
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge hd hdle1 hθε) (sq_nonneg d))).trans (hF.density (f i))
  have hK := hF.count.comp f hf
  have hA : Admissible d ε (d ^ (-θ)) (d ^ (-θ) / (m * d ^ 2)) m (x ∘ f) (v ∘ f) (Y ∘ f) := by
    refine ⟨hm, fun i => ⟨hF.unit (f i), hF.ball (f i), hF.measurable (f i), hF.shading (f i)⟩,
      ?_, hden, hK, hK.to_frostman hd hm⟩
    intro i j hij
    exact hsep (f i) (enumerate_mem S i) (f j) (enumerate_mem S j) (fun he => hij (hf he))
  refine ⟨m, x ∘ f, v ∘ f, Y ∘ f, d ^ (-θ), d ^ (-θ) / (m * d ^ 2), hA, ?_, ?_, ?_⟩
  · exact iUnion_subset fun i => subset_iUnion Y (f i)
  · change ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ i : Fin S.card, volume (Y (enumerate S i))
    rw [sum_enumerate S (fun i => volume (Y i))]
    exact hmass
  · exact (hT.restrict hF.nonempty hm f hf).mono hd hdle1
      (Real.rpow_le_rpow_of_exponent_ge hd hdle1 (neg_le_neg hθε)) le_rfl le_rfl

end WangZahlLot.Obl.wz_multiscale_finite_tower
