-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.DegreeLogLoss.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatExit

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- The dyadic degree count is bounded by any fixed positive power of the
number of vertices, with a constant depending only on that power. -/
theorem nat_log_two_add_one_le_rpow {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    (Nat.log 2 m:ℝ)+1 ≤ (1+(ε*Real.log 2)⁻¹)*(m:ℝ)^ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : 0 < ε*Real.log 2 := mul_pos hε hlog2
  have hlog := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.natLog_two_le_log hm
  have hupper := Real.log_natCast_le_rpow_div m hε
  have hnatlog : (Nat.log 2 m:ℝ) ≤ (m:ℝ)^ε/(ε*Real.log 2) := by
    apply (le_div_iff₀ hprod).mpr
    have hh := mul_le_mul_of_nonneg_right (hlog.trans hupper) hε.le
    rw [div_mul_cancel₀ _ hε.ne'] at hh
    nlinarith only [hh]
  have hone : 1 ≤ (m:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hm) hε.le
  rw [div_eq_mul_inv] at hnatlog
  nlinarith only [hnatlog, hone]

/-- Four powers of the degree-regularization logarithm fit into any
prescribed inverse scale power under a polynomial coefficient packing cap. -/
theorem exists_degree_log_loss (ε : ℝ) (hε : 0 < ε) (P : ℝ) (hP : 0 < P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ), 0 < δ → ∀ m : ℕ, 1 ≤ m →
      (m:ℝ)*δ^6 ≤ P → (((Nat.log 2 m:ℝ)+1)^4) ≤ C*δ^(-ε) := by
  let η : ℝ := ε/24
  have hη : 0 < η := by dsimp [η]; positivity
  let A : ℝ := 1+(η*Real.log 2)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(A*P^η)^4, by positivity, ?_⟩
  intro δ hδ m hm hpack
  have hmP : (m:ℝ) ≤ P/δ^6 := (le_div_iff₀ (pow_pos hδ 6)).mpr hpack
  have hmass : (m:ℝ)^η ≤ P^η*δ^(-6*η) := by
    calc
      _ ≤ (P/δ^6)^η := Real.rpow_le_rpow (Nat.cast_nonneg _) hmP hη.le
      _ = P^η/(δ^6)^η := Real.div_rpow hP.le (pow_nonneg hδ.le _) η
      _ = P^η/δ^(6*η) := by rw [← Real.rpow_natCast_mul hδ.le 6 η]; norm_num
      _ = _ := by
        rw [show -6*η=-(6*η) by ring, Real.rpow_neg hδ.le]
        ring
  have hlog := nat_log_two_add_one_le_rpow hm hη
  have hb : (Nat.log 2 m:ℝ)+1 ≤ (A*P^η)*δ^(-6*η) := by
    have hh := mul_le_mul_of_nonneg_left hmass hA.le
    dsimp [A] at *
    nlinarith only [hlog, hh]
  have hp := pow_le_pow_left₀ (show 0 ≤ (Nat.log 2 m:ℝ)+1 by positivity) hb 4
  calc
    _ ≤ ((A*P^η)*δ^(-6*η))^4 := hp
    _ = (A*P^η)^4*δ^((-6*η)*4) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hδ.le (-6*η) 4]
      norm_num
    _ = _ := by congr 2; dsimp [η]; ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
