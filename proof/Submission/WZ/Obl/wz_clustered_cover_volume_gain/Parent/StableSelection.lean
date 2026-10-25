-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.StableSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseStability
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoverSize
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Parameters

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open Finset MeasureTheory
open wz_concentrated_convex_factorization (coefficient)

/-- The numerical conditions for weighted stable selection can be met uniformly
at all sufficiently small scales. The mass comparison has no unspecified constant. -/
theorem stable_selection_parameters {ν : ℝ} (hν : 0 < ν) {C : ℝ} (hC : 0 < C) :
    ∃ (p : ℕ) (d : ℝ), 0 < p ∧ 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      δ ≤ 1 / 2 ∧ C * δ ≤ 1 ∧
      (δ ^ (ν / 20)) ^ p * δ ^ (-(6 : ℝ)) ≤ 1 ∧
      2 ≤ δ ^ 2 * (δ ^ (-(ν / 20))) ^ (2 * p) ∧
      δ ^ (ν + ν / 20) * (2 * δ ^ (-(ν / 20)) * (2 * p + 1 : ℝ)) ≤
        δ ^ (ν / 20) ∧
      384 ≤ δ ^ (-ν) := by
  obtain ⟨p, d, hp, hd, h⟩ :=
    wz_concentrated_convex_factorization.choose_parameters C ν hC hν
  refine ⟨p, d, hp, hd, ?_⟩
  intro δ hδ hδd
  obtain ⟨hhalf, hCd, hsmall, hgrid, hmass, hlarge⟩ := h δ hδ hδd
  have hδ1 : δ ≤ 1 := by linarith
  have hr : 1 ≤ δ ^ (-(ν / 20)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  refine ⟨hhalf, hCd, hsmall, ?_, ?_, ?_⟩
  · have he : δ ^ 2 * (δ ^ (-(ν / 20))) ^ (2 * p) =
        (δ * (δ ^ (-(ν / 20))) ^ p) ^ 2 := by
      rw [mul_comm 2 p, pow_mul, mul_pow]
    rw [he]
    nlinarith
  · have hcancel : δ ^ (ν + ν / 20) * δ ^ (-(ν / 20)) = δ ^ ν := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = δ ^ ν * (2 * (2 * p + 1 : ℝ)) := by
        calc
          _ = (δ ^ (ν + ν / 20) * δ ^ (-(ν / 20))) * (2 * (2 * p + 1 : ℝ)) := by ring
          _ = _ := by rw [hcancel]
      _ ≤ δ ^ ν * (4 * (p + 1 : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδ.le _)
        nlinarith [sq_nonneg (p : ℝ)]
      _ ≤ _ := hmass
  · apply le_trans _ hlarge
    have hp2 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    have hbase' : (2 : ℝ) ≤ 1024 * 2 ^ p * (δ ^ (-(ν / 20))) ^ 2 := by
      calc
        2 ≤ 1024 := by norm_num
        _ ≤ 1024 * 2 ^ p := le_mul_of_one_le_right (by norm_num) hp2
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)
    nlinarith

/-- Power-scale version of the weighted stable selection. -/
theorem stable_coarse_tubes_power {ν : ℝ} (hν : 0 < ν) {C : ℝ} (hC : 0 < C) :
    ∃ (p : ℕ) (d : ℝ), 0 < p ∧ 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      δ ≤ 1 / 2 ∧ C * δ ≤ 1 ∧ 384 ≤ δ ^ (-ν) ∧
      ∀ (ρ U : ℝ), 0 < ρ → ρ ≤ 1 → 0 < U →
      ∀ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space)
        (a : Fin N → ℝ),
      (∀ k, a k ≤ U) → 0 < ∑ k, a k →
      δ ^ 2 * U * N ≤ (∑ k, a k) / 2 →
      (N : ℝ) / ρ ≤ δ ^ (-(6 : ℝ)) →
      ∃ Q : Finset (Fin N), Q.Nonempty ∧
        δ ^ (ν + ν / 20) * (∑ k, a k) ≤ ∑ k ∈ Q, a k ∧
        (∀ k ∈ Q, ∀ k' ∈ Q, a k ≤ δ ^ (-(ν / 20)) * a k') ∧
        (∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
          coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) Q ≤
            2 ^ p * coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) R) := by
  obtain ⟨p, d, hp, hd, hparams⟩ := stable_selection_parameters hν hC
  refine ⟨p, d, hp, hd, ?_⟩
  intro δ hδ hδd
  obtain ⟨hhalf, hCd, hsmall, hgrid, hmass, hlarge⟩ := hparams δ hδ hδd
  refine ⟨hhalf, hCd, hlarge, ?_⟩
  intro ρ U hρ hρ1 hU N y w a ha hpos htail hcoef
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨Q, -, hQ, hkeep, hcomp, hstable⟩ := stable_coarse_tubes hρ hρ1 y w
    Finset.univ a hU (sq_pos_of_pos hδ) (by nlinarith) (by
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith))
    (fun k _ => ha k) hpos (by simpa using htail) (2 * p) p hp hgrid
    (Real.rpow_nonneg hδ.le _) (by
      exact (mul_le_mul_of_nonneg_left hcoef (pow_nonneg (Real.rpow_nonneg hδ.le _) _)).trans hsmall)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hkeep
  have hQmass : 0 ≤ ∑ k ∈ Q, a k := by
    have hpositive : 0 < δ ^ (ν / 20) * ∑ k, a k :=
      mul_pos (Real.rpow_pos_of_pos hδ _) hpos
    have hc : 0 < 2 * δ ^ (-(ν / 20)) * (2 * p + 1 : ℝ) := by positivity
    exact (pos_of_mul_pos_right (hpositive.trans_le hkeep) hc.le).le
  refine ⟨Q, hQ, ?_, hcomp, hstable⟩
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hδ (ν / 20))).mp
  calc
    _ = δ ^ (ν + ν / 20) * (δ ^ (ν / 20) * ∑ k, a k) := by ring
    _ ≤ δ ^ (ν + ν / 20) *
        (2 * δ ^ (-(ν / 20)) * (2 * p + 1 : ℝ) * ∑ k ∈ Q, a k) :=
      mul_le_mul_of_nonneg_left hkeep (Real.rpow_nonneg hδ.le _)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hmass hQmass]


/-- The remaining Frostman normalization constant fits into the target error
once the three input losses are chosen below `ν / 20`. -/
theorem stable_refinement_budget {δ ν η h ζ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hν : 0 ≤ ν)
    (hη : η ≤ ν / 20) (hh : h ≤ ν / 20) (hνζ : 4 * ν ≤ ζ)
    (hconstant : 384 ≤ δ ^ (-ν)) :
    384 * δ ^ (-((h + ν + ν / 20) + η + 2 * h)) ≤ δ ^ (-ζ) := by
  calc
    _ ≤ δ ^ (-ν) * δ ^ (-((h + ν + ν / 20) + η + 2 * h)) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-ν + -((h + ν + ν / 20) + η + 2 * h)) :=
      (Real.rpow_add hδ _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
