-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.GrainPotential.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_broad_grains_move_one.Glue
import Submission.WZ.Obl.wz_grains_finite_terminal_iteration

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

/-- The bounded logarithmic potential used by the grain iteration. -/
def grainPotential (ζ ρ c : ℝ) : ℝ := 4*Real.log c+ζ*Real.log ρ

/-- The uniform increase in the potential at every progress step. -/
def grainIncrement (ζ d : ℝ) : ℝ := -ζ*(ζ/2000)*Real.log d

theorem grain_increment_pos {ζ d : ℝ} (hζ : 0 < ζ) (hd : 0 < d) (hd1 : d < 1) :
    0 < grainIncrement ζ d := by
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos hζ) (by positivity))
    (Real.log_neg hd hd1)

/-- Every nondegenerate grain state has both scales in the fine-to-unit range. -/
theorem state_scale_bounds {ω ζ d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {t : Bool} (hd : 0 < d) (hD : D ω ζ d h ρ c n x v Y t) :
    d ≤ c ∧ c ≤ 1 ∧ d ≤ ρ ∧ ρ ≤ 1 := by
  obtain ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,hstop⟩ := hD
  obtain ⟨hc,hc1,hρ,hρ1⟩ := WangZahlLot.Obl.wz_broad_grains_move_one.H_scales hd hH
  have hda := WangZahlLot.Obl.wz_broad_grains_move_one.H_fine_le hH
  refine ⟨?_,hc1,?_,hρ1⟩
  · exact hda.trans (by nlinarith only [mul_nonneg hc.le (sub_nonneg.mpr hρ1)])
  · exact hda.trans (by nlinarith only [mul_nonneg hρ.le (sub_nonneg.mpr hc1)])

theorem grain_potential_bounds {ω ζ d h ρ c : ℝ} {n : ℕ} {x v : Fin n → V}
    {Y : Fin n → Set V} {t : Bool} (hζ : 0 ≤ ζ) (hd : 0 < d)
    (hD : D ω ζ d h ρ c n x v Y t) :
    (4+ζ)*Real.log d ≤ grainPotential ζ ρ c ∧ grainPotential ζ ρ c ≤ 0 := by
  obtain ⟨hdc,hc1,hdρ,hρ1⟩ := state_scale_bounds hd hD
  have hlc := Real.log_le_log hd hdc
  have hlρ := mul_le_mul_of_nonneg_left (Real.log_le_log hd hdρ) hζ
  have hc := Real.log_nonpos (hd.le.trans hdc) hc1
  have hρ := mul_nonpos_of_nonneg_of_nonpos hζ (Real.log_nonpos (hd.le.trans hdρ) hρ1)
  dsimp [grainPotential]
  constructor <;> nlinarith

/-- The accepted scalar potential inequality applies to the exact two forms
of geometric progress in the frozen improvement statement. -/
theorem grain_potential_progress {ω ζ d h h' ρ c ρ' c' : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hζ : 0 < ζ) (hζmax : ζ ≤ 2000) (hd : 0 < d) (hd1 : d < 1)
    (hD : D ω ζ d h ρ c n x v Y false) (hD' : D ω ζ d h' ρ' c' n x v Y false)
    (hprogress : d^(-ζ/2)*c ≤ c' ∨ c ≤ c' ∧ d^(-ζ/2000)*ρ ≤ ρ') :
    grainPotential ζ ρ c+grainIncrement ζ d ≤ grainPotential ζ ρ' c' := by
  obtain ⟨hdc,hc1,hdρ,hρ1⟩ := state_scale_bounds hd hD
  obtain ⟨hdc',hc1',hdρ',hρ1'⟩ := state_scale_bounds hd hD'
  have hc : 0 < c := hd.trans_le hdc
  have hρ : 0 < ρ := hd.trans_le hdρ
  have hlogmul (a b : ℝ) (hb : 0 < b) : Real.log (d^a*b)=a*Real.log d+Real.log b := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hd a).ne' hb.ne',Real.log_rpow hd]
  have hs := WangZahlLot.Obl.wz_grains_finite_terminal_iteration.potential_step
    (lc := Real.log c) (lρ := Real.log ρ) (lc' := Real.log c') (lρ' := Real.log ρ')
    hζ hζmax (Real.log_neg hd hd1) (Real.log_nonpos hρ.le hρ1)
    (Real.log_le_log hd hdρ') (by
      rcases hprogress with hc' | ⟨hcc',hρ'⟩
      · left
        have hh := Real.log_le_log (by positivity : 0<d^(-ζ/2)*c) hc'
        simpa only [hlogmul _ _ hc] using hh
      · right
        refine ⟨Real.log_le_log hc hcc',?_⟩
        have hh := Real.log_le_log (by positivity : 0<d^(-ζ/2000)*ρ) hρ'
        simpa only [hlogmul _ _ hρ] using hh)
  dsimp [grainPotential,grainIncrement]
  nlinarith only [hs]

theorem terminal_to_stage_three {ω ζ d h ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hD : D ω ζ d h ρ c n x v Y true) : J ω ζ d h ρ c n x v Y 3 := by
  obtain ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,hstop⟩ := hD
  have hs := hstop rfl
  exact ⟨S,Z,N,y,w,f,a,g,hC,hbase,hg,hBr,hH,fun _ => hs.2.1,fun _ => hs.1,fun _ => hs.2.2⟩

theorem terminal_mono {ω ζ d h h' ρ c : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hD : D ω ζ d h ρ c n x v Y true) : D ω ζ d h' ρ c n x v Y true :=
  stage_three_to_terminal (stage_mono hd hd1 hh (terminal_to_stage_three hD))

end WangZahlLot.Obl.wz_broad_grains_improvement
