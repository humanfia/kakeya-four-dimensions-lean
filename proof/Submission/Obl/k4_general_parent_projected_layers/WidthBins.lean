import Mathlib

namespace Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- A power-grid width class with ratio N^tau. Its index set is independent of N. -/
def widthBin (N tau beta : ℝ) : ℤ := ⌊Real.log beta / (tau * Real.log N)⌋

def widthIndices (A B tau : ℝ) : Finset ℤ :=
  Finset.Icc (⌊-A / tau⌋ - 1) ⌈B / tau⌉

theorem widthBin_bounds {N tau beta : ℝ} (hN : 1 < N) (htau : 0 < tau) (hb : 0 < beta) :
    N ^ (tau * (widthBin N tau beta : ℝ)) ≤ beta ∧
      beta ≤ N ^ (tau * ((widthBin N tau beta : ℝ) + 1)) := by
  have hN0 : 0 < N := by linarith
  have hden : 0 < tau * Real.log N := mul_pos htau (Real.log_pos hN)
  have hlo := (le_div_iff₀ hden).mp (Int.floor_le (Real.log beta / (tau * Real.log N)))
  have hhi := (div_lt_iff₀ hden).mp (Int.lt_floor_add_one (Real.log beta / (tau * Real.log N)))
  constructor
  · rw [Real.rpow_def_of_pos hN0]
    apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log hb)
    change Real.log N * (tau * (widthBin N tau beta : ℝ)) ≤ Real.log beta
    dsimp [widthBin]
    nlinarith
  · rw [Real.rpow_def_of_pos hN0]
    calc
      beta = Real.exp (Real.log beta) := (Real.exp_log hb).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        change Real.log beta ≤ Real.log N * (tau * ((widthBin N tau beta : ℝ) + 1))
        dsimp [widthBin]
        nlinarith

theorem widthBin_factor_bound {N tau beta : ℝ} (hN : 1 < N) (htau : 0 < tau) (hb : 0 < beta) :
    beta ≤ N ^ tau * N ^ (tau * (widthBin N tau beta : ℝ)) := by
  have H := (widthBin_bounds hN htau hb).2
  convert H using 1
  rw [← Real.rpow_add (by linarith : 0 < N)]
  congr 1
  ring

theorem widthBin_mem {N tau beta A B : ℝ} (hN : 1 < N) (htau : 0 < tau) (hb : 0 < beta)
    (hlo : N ^ (-A) ≤ beta) (hhi : beta ≤ N ^ B) :
    widthBin N tau beta ∈ widthIndices A B tau := by
  obtain ⟨hblo, hbhi⟩ := widthBin_bounds hN htau hb
  have hexplo : -A ≤ tau * ((widthBin N tau beta : ℝ) + 1) :=
    (Real.rpow_le_rpow_left_iff hN).mp (hlo.trans hbhi)
  have hexphi : tau * (widthBin N tau beta : ℝ) ≤ B :=
    (Real.rpow_le_rpow_left_iff hN).mp (hblo.trans hhi)
  have hlow : -A / tau ≤ (widthBin N tau beta : ℝ) + 1 :=
    (div_le_iff₀ htau).mpr (by nlinarith)
  have hhigh : (widthBin N tau beta : ℝ) ≤ B / tau :=
    (le_div_iff₀ htau).mpr (by nlinarith)
  simp only [widthIndices, Finset.mem_Icc]
  constructor
  · have h : ((⌊-A / tau⌋ : ℤ) : ℝ) - 1 ≤ (widthBin N tau beta : ℝ) := by
      linarith [Int.floor_le (-A / tau)]
    exact_mod_cast h
  · have h := hhigh.trans (Int.le_ceil (B / tau))
    exact_mod_cast h

theorem widthIndices_nonempty {A B tau : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (htau : 0 < tau) :
    (widthIndices A B tau).Nonempty := by
  refine ⟨0, ?_⟩
  simp only [widthIndices, Finset.mem_Icc]
  constructor
  · have hf := Int.floor_le (-A / tau)
    have hneg : -A / tau ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) htau.le
    have h : ((⌊-A / tau⌋ : ℤ) : ℝ) - 1 ≤ 0 := by linarith
    exact_mod_cast h
  · have h := (div_nonneg hB htau.le).trans (Int.le_ceil (B / tau))
    exact_mod_cast h

end

end Submission.Obl.k4_general_parent_projected_layers
