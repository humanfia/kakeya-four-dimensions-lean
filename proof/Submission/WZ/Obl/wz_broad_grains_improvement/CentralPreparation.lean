-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CentralPreparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.CentralAlignedFamily
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedAdmissible

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_multiscale_finite_tower
  (AlignedFamily axisMidpoint exists_scale_cutoff power_coefficient_bound
    inverse_power_error_bound density_power_bound)

set_option maxHeartbeats 800000

/-- Alignment of central rows with an injective map back to the original family.
The whole selected shading is retained, and all fixed losses are absorbed into
an arbitrarily small power. -/
theorem prepare_central_family {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1/100000 ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ n x v Y,
      A d η (d^(-η)) (d^(-η)) n x v Y →
      (∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1/2) →
      (∀ i, Y i ⊆ closedBall 0 (1/2)) →
    ∃ (m : ℕ) (j : Fin m → Fin n) (u : V), Function.Injective j ∧ m ≤ n ∧
      AlignedFamily d (d^ε) (d^(-ε)) (d^(-ε)) u 0 m
        (fun i => recenterStart (x (j i)) (v (j i))) (v ∘ j) (Y ∘ j) ∧
      O (d^ε) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Y (j i)) := by
  obtain ⟨C, hC, hinit⟩ := central_aligned_family
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let η := ε/10
  have hη : 0 < η := by dsimp [η]; positivity
  let B : ℝ := 1000000000000000*C
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨d₀,hd₀,hd₀D,hcut⟩ := exists_scale_cutoff (1/B) η
    (min D (1/100000)) (by positivity) hη (lt_min hD (by norm_num))
  refine ⟨η,d₀,hη,by dsimp [η]; linarith,hd₀,
    hd₀D.trans (min_le_left _ _),hd₀D.trans (min_le_right _ _),?_⟩
  intro d hd hdd n x v Y hA hmid hcentral
  have hd1 : d ≤ 1 := (hdd.trans (hd₀D.trans (min_le_right _ _))).trans (by norm_num)
  have hbase : B*d^η ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hcut d hd hdd) hB.le
    simpa only [mul_one_div_cancel hB.ne'] using hh
  have hcoef (c a : ℝ) (hc : 0 ≤ c) (hcB : c ≤ B) (ha : η ≤ a) : c*d^a ≤ 1 :=
    power_coefficient_bound hd hd1 hc hcB ha hbase
  obtain ⟨m,j,u,hj,hmn,hF,hmass⟩ := hinit hd
    (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hd.le _) hA hmid hcentral
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hF.nonempty
  have hcard : d^η/(112*C)*n ≤ m := by
    have hh := ((mul_le_mul' (a := O (1/(2*C))) le_rfl hA.2.2.2.1).trans hmass).trans
      (hF.mass_le hd.le hd1)
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(2*C))] at hh
    have hh' := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 56*(m:ℝ)*d^2)).mp hh
    have hc : (1/(2*C))*(d^η*n) ≤ 56*m := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
      convert hh' using 1 <;> ring
    have he : d^η/(112*C)*n = (1/56:ℝ)*((1/(2*C))*(d^η*n)) := by ring
    rw [he]
    linarith
  have hden : d^ε ≤ d^η/2 := density_power_bound hd (by norm_num)
    (hcoef 2 (ε-η) (by norm_num) (by dsimp [B]; nlinarith) (by dsimp [η]; linarith))
  have hcount : d^(-η)*WangZahlLot.Obl.wz_rescaled_fibre_alternatives.convexExpansionLoss 2 ≤
      d^(-ε) := by
    have hh := inverse_power_error_bound hd (hcoef 512000 (ε-η) (by norm_num)
      (by dsimp [B]; nlinarith) (by dsimp [η]; linarith))
    norm_num [WangZahlLot.Obl.wz_rescaled_fibre_alternatives.convexExpansionLoss] at ⊢
    simpa only [mul_comm] using hh
  have hroot : 512000000*d^(-η)*n/m ≤ d^(-ε) := by
    have hbound : (512000000*(112*C))*d^(-(2*η)) ≤ d^(-ε) :=
      inverse_power_error_bound hd (hcoef _ (ε-2*η) (by positivity)
        (by dsimp [B]; nlinarith) (by dsimp [η]; linarith))
    have he : ((512000000*(112*C))*d^(-(2*η)))*(d^η/(112*C)*n) =
        512000000*d^(-η)*n := by
      have hp : d^(-(2*η))*d^η = d^(-η) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = (512000000*(d^(-(2*η))*d^η))*n := by field_simp
        _ = _ := by rw [hp]
    apply (div_le_iff₀ hm).mpr
    rw [← he]
    exact (mul_le_mul_of_nonneg_left hcard (by positivity)).trans
      (mul_le_mul_of_nonneg_right hbound hm.le)
  have hret : d^ε ≤ 1/(2*C) := by
    have hh := hcoef (2*C) ε (by positivity) (by dsimp [B]; nlinarith)
      (by dsimp [η]; linarith)
    exact (le_div_iff₀ (by positivity : 0 < 2*C)).mpr (by nlinarith)
  exact ⟨m,j,u,hj,hmn,hF.mono hden hcount hroot,
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hret) le_rfl).trans hmass⟩



/-- Central alignment with strict tube separation and normalized admissibility.
The original index of every retained full shading remains explicit. -/
theorem prepare_central_admissible {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1/100000 ∧
    ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ n x v Y,
      A d η (d^(-η)) (d^(-η)) n x v Y →
      (∀ i, ‖axisMidpoint (x i) (v i)‖ ≤ 1/2) →
      (∀ i, Y i ⊆ closedBall 0 (1/2)) →
    ∃ (m : ℕ) (j : Fin m → Fin n) (u : V), Function.Injective j ∧ m ≤ n ∧
      A d ε (d^(-ε)) (d^(-ε)) m
        (fun i => recenterStart (x (j i)) (v (j i))) (v ∘ j) (Y ∘ j) ∧
      AlignedFamily d (d^ε) (d^(-ε)) (d^(-ε)) u 0 m
        (fun i => recenterStart (x (j i)) (v (j i))) (v ∘ j) (Y ∘ j) ∧
      O (d^ε) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Y (j i)) := by
  let θ := ε/10
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθε : θ ≤ ε := by dsimp [θ]; linarith
  obtain ⟨d₁,hd₁,hd₁D,hcut⟩ := exists_scale_cutoff
    (1/1000000000000000) θ D (by norm_num) hθ hD
  obtain ⟨η,d₀,hη,hηθ,hd₀,hd₀₁,hd₀small,hprepare⟩ := prepare_central_family hθ hd₁
  refine ⟨η,d₀,hη,hηθ.trans hθε,hd₀,hd₀₁.trans hd₁D,hd₀small,?_⟩
  intro d hd hdd n x v Y hA hmid hcentral
  have hdsmall : d ≤ 1/100000 := hdd.trans hd₀small
  have hd1 : d ≤ 1 := hdsmall.trans (by norm_num)
  have hbase : 1000000000000000*d^θ ≤ 1 := by
    have hh := hcut d hd (hdd.trans hd₀₁)
    linarith
  have hcoef (C₀ b : ℝ) (hC : 0 ≤ C₀) (hCB : C₀ ≤ 1000000000000000)
      (hb : θ ≤ b) : C₀*d^b ≤ 1 :=
    power_coefficient_bound hd hd1 hC hCB hb hbase
  obtain ⟨m,j,u,hj,hmn,hF₀,hmass₀⟩ := hprepare d hd hdd n x v Y hA hmid hcentral
  have hcost : d^(2*θ)*(10000000000000*d^(-θ)) ≤ 1 := by
    calc
      _ = 10000000000000*d^θ := by
        rw [mul_left_comm,← Real.rpow_add hd]
        congr 1
        congr 1
        ring
      _ ≤ 1 := hcoef _ _ (by norm_num) (by norm_num) le_rfl
  obtain ⟨k,e,he,hkm,hF,hsep,hret,hcard⟩ := aligned_family_distinct hd hdsmall
    (Real.rpow_pos_of_pos hd θ) (Real.rpow_nonneg hd.le (-θ))
    (Real.rpow_nonneg hd.le (2*θ)) hcost hF₀
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hF.nonempty
  have hcard' : (d^(3*θ)/56)*m ≤ k := by
    simpa only [← Real.rpow_add hd,show 2*θ+θ=3*θ by ring] using hcard
  have hratio : d^(-θ)*m/k ≤ 56*d^(-(4*θ)) := by
    apply (div_le_iff₀ hk).mpr
    have hh := mul_le_mul_of_nonneg_left hcard' (by positivity : 0 ≤ 56*d^(-(4*θ)))
    have hid : (56*d^(-(4*θ)))*(d^(3*θ)/56*m) = d^(-θ)*m := by
      calc
        _ = (d^(-(4*θ))*d^(3*θ))*m := by ring
        _ = _ := by rw [← Real.rpow_add hd]; congr 2; ring
    rwa [hid] at hh
  have hroot : 16000000*(d^(-θ)*m/k) ≤ d^(-ε) := by
    calc
      _ ≤ 16000000*(56*d^(-(4*θ))) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 896000000*d^(-(4*θ)) := by ring
      _ ≤ _ := inverse_power_error_bound hd
        (hcoef _ _ (by norm_num) (by norm_num) (by dsimp [θ]; linarith))
  have hroot' : d^(-θ)*m/k ≤ d^(-ε) := by
    have hn : 0 ≤ d^(-θ)*m/k := by positivity
    linarith
  have hden : d^ε ≤ d^θ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hθε
  have hKT : d^(-θ) ≤ d^(-ε) := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθε)
  have hF' := hF.mono hden hKT hroot'
  have hFrost : F d (d^(-ε)) k
      (fun i => recenterStart (x (j (e i))) (v (j (e i)))) (v ∘ j ∘ e) := by
    intro w t r hw hr
    exact (aligned_family_frostman hd hF w t r hw hr).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hroot (Nat.cast_nonneg k))) _)
  refine ⟨k,j ∘ e,u,hj.comp he,hkm.trans hmn,
    ⟨hF'.nonempty,fun i => ⟨hF'.unit i,hF'.ball i,hF'.measurable i,hF'.shading i⟩,
      hsep,hF'.mass_lower,hF'.count,hFrost⟩,hF',?_⟩
  have hkeep : O (d^(3*θ))*(∑ i, μ (Y i)) ≤ ∑ i, μ (Y (j (e i))) := by
    calc
      _ = O (d^(2*θ))*(O (d^θ)*∑ i, μ (Y i)) := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le _),← Real.rpow_add hd]
        congr 3
        ring
      _ ≤ O (d^(2*θ))*(∑ i, μ (Y (j i))) := mul_le_mul_right hmass₀ _
      _ ≤ _ := hret
  exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by dsimp [θ]; linarith : 3*θ ≤ ε))) _).trans hkeep

end WangZahlLot.Obl.wz_broad_grains_improvement
