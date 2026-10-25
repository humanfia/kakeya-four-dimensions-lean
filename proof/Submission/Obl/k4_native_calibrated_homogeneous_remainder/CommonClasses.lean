import Submission.Obl.k4_native_calibrated_homogeneous_remainder.ParameterSelection
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WeightClasses
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.GeometryParameters
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WorldDomination

/-! Select common growth classes for world weights and chart density ratios. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_tempered_grid_selection

structure SelectedClasses {p q : Data} {r h w : ℝ} (a : RemainderGeometry p q r h w) where
  ψ : ℕ → ℕ
  increasing : StrictMono ψ
  K : ℕ → ℝ
  keep : (k : ℕ) → Finset (Fin (q.W (ψ k)))
  β : ℝ
  A : ℝ
  subpower : Subpower (q.N ∘ ψ) K
  old_slack : ∀ k, q.K (ψ k) ≤ K k
  valid : RawValid (keepWorlds (q.reindex ψ) keep K)
  weight_sum : ∀ k, 0 < keptWeightSum (q.reindex ψ) keep k ∧
    keptWeightSum (q.reindex ψ) keep k ≤ 1
  inverse_weight_sum : ∀ k, (keptWeightSum (q.reindex ψ) keep k)⁻¹ ≤ K k
  weight_band : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b ∈ keep k,
    q.N (ψ k) ^ (-β - ε) ≤ q.ω (ψ k) b ∧ q.ω (ψ k) b ≤ q.N (ψ k) ^ (-β + ε)
  ratio_band : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b ∈ keep k,
    q.N (ψ k) ^ (A - ε) ≤ a.densityRatio (ψ k) b ∧
      a.densityRatio (ψ k) b ≤ q.N (ψ k) ^ (A + ε)

theorem common_world_classes {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (hq : RawValid q) :
    Nonempty (SelectedClasses a) := by
  have hq0 := hq
  rcases hq with ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, M, D, hfmt⟩
  let C : ℝ := ((M + 3 * a.M + 3 : ℕ) : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hMC : (M : ℝ) < C := by dsimp [C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) a.M]
  have hRC : ((3 * a.M + 1 : ℕ) : ℝ) ≤ C := by
    dsimp [C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) M]
  let f : (k : ℕ) → ℕ → Fin (q.W k) → ℝ := fun k j b =>
    if j = 0 then weightExponent C (q.N k) (q.ω k b)
    else boundedExponent C (q.N k) (a.densityRatio k b)
  have hf : ∀ k j b, |f k j b| ≤ C := by
    intro k j b
    dsimp [f]
    split_ifs
    · exact abs_weightExponent_le _ _ _ hC
    · exact abs_boundedExponent _ _ _ hC
  obtain ⟨ψ, B, keep, α, hψ, hB, hα, hfit, hmass⟩ := finite_world_parameter_selection
    q.N hN hNt q.W (fun k b => ENNReal.ofReal (q.ω k b) * selected q k b univ) f C hC hf
  have hrawψ := hq0.reindex hψ.tendsto_atTop
  have hKψ : Subpower (q.N ∘ ψ) (q.K ∘ ψ) := hrawψ.2.2.1
  let K : ℕ → ℝ := fun k => q.K (ψ k) * (B k : ℝ)
  have hKret : Subpower (q.N ∘ ψ) K := subpower_mul
    (fun k => by change 0 < q.N (ψ k); linarith [hN (ψ k)]) hKψ hB
  have hKdom : ∀ k, q.K (ψ k) ≤ K k := fun k =>
    le_mul_of_one_le_right (by linarith [hK.1 (ψ k)]) (hB.1 k)
  have hrawmass (k : ℕ) : ENNReal.ofReal ((q.K (ψ k))⁻¹) ≤
      ∑ b, ENNReal.ofReal (q.ω (ψ k) b) * selected q (ψ k) b univ :=
    (hfmt (ψ k)).2.2.2.2
  have hBpos : ∀ k, 0 < B k := by
    intro k
    exact_mod_cast (show (0 : ℝ) < B k by linarith [hB.1 k])
  have hretain : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤
      ∑ b ∈ keep k, ENNReal.ofReal (q.ω (ψ k) b) * selected q (ψ k) b univ := fun k =>
    inverse_mass_after_finite_loss (by linarith [hK.1 (ψ k)]) (hBpos k) (hrawmass k) (hmass k)
  obtain ⟨hvalid, hnorm⟩ := hrawψ.keep_worlds keep K hKret hKdom hretain
  have hω : ∀ k b, 0 ≤ q.ω (ψ k) b ∧ q.ω (ψ k) b ≤ 1 := by
    intro k b
    refine ⟨(hfmt (ψ k)).2.1 b, ?_⟩
    have hh := Finset.single_le_sum (fun b _ => (hfmt (ψ k)).2.1 b) (Finset.mem_univ b)
    simpa only [(hfmt (ψ k)).2.2.1] using hh
  have hretain' : ∀ k, ENNReal.ofReal ((q.K (ψ k))⁻¹) ≤ ENNReal.ofReal (B k : ℝ) *
      ∑ b ∈ keep k, ENNReal.ofReal (q.ω (ψ k) b) * selected q (ψ k) b univ := by
    intro k
    simpa only [ENNReal.ofReal_natCast] using (hrawmass k).trans (hmass k)
  have hweight := clipped_weight_class (q.N ∘ ψ) (q.K ∘ ψ) (fun k => (B k : ℝ))
    (fun k => hN (ψ k)) (hNt.comp hψ.tendsto_atTop) hKψ hB
    (fun k => q.W (ψ k)) M (fun k => (hfmt (ψ k)).1)
    (fun k b => q.ω (ψ k) b) (fun k b => selected q (ψ k) b univ) keep hω
    (fun k b => hq0.selected_mass_le_one (ψ k) b) hretain' C (α 0) hC hMC
    (fun ε hε => by simpa only [f, ite_eq_left rfl, Function.comp_apply] using hfit 0 ε hε)
  have hactual : ∀ k b, boundedExponent C (q.N k) (a.densityRatio k b) =
      logarithmicExponent (q.N k) (a.densityRatio k b) := by
    intro k b
    have hrange := a.densityRatio_bounds hp k b
    apply boundedExponent_eq (by linarith [hN k])
    · exact (Real.rpow_le_rpow_of_exponent_le (by linarith [hN k]) (neg_le_neg hRC)).trans hrange.2.1
    · exact hrange.2.2.trans (by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [hN k]) hRC)
  refine ⟨{
    ψ := ψ
    increasing := hψ
    K := K
    keep := keep
    β := α 0
    A := -α 1
    subpower := hKret
    old_slack := hKdom
    valid := hvalid
    weight_sum := hnorm
    inverse_weight_sum := keptWeightSum_inv_bound hrawψ keep K
      (fun k => by linarith [hKret.1 k]) (fun k => (hnorm k).1) hretain
    weight_band := ?_
    ratio_band := ?_ }⟩
  · intro ε hε
    filter_upwards [hweight.2 ε hε] with k hk b hb
    exact (hk b hb).2
  · intro ε hε
    filter_upwards [hfit 1 ε hε] with k hk b hb
    have hfit' : |logarithmicExponent (q.N (ψ k)) (a.densityRatio (ψ k) b) - α 1| ≤ ε := by
      have hh := hk b hb
      change |boundedExponent C (q.N (ψ k)) (a.densityRatio (ψ k) b) - α 1| < ε at hh
      rw [hactual] at hh
      exact hh.le
    exact power_band_of_exponent_fit (by linarith [hN (ψ k)])
      (a.densityRatio_bounds hp (ψ k) b).1 hfit'

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
