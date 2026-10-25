import Submission.Obl.k4_coarsened_outer_horizon_composition.Preparation
import Submission.Obl.k4_finite_width_output_exclusion.Horizon
import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The accepted own-depth preparation need not impose a width exponent.
Every such system nevertheless has asymptotic narrowness at least zero. -/
lemma known_plain_zero {p : Data} (hp : Valid p) {r h : ℝ}
    (hk : k4_coarsened_outer_horizon_composition.known p.N p.K p.L p.W p.ω p.ν p.E p.B p.f r h) :
    Known p r h 0 := by
  obtain ⟨M, D, hk⟩ := hk
  refine ⟨M, D, ?_⟩
  intro ε hε
  apply (hk (ε / 2) (by positivity)).mono
  rintro k ⟨κ, hκ, hκN, T, C, γ, j, c, u, Q, R, A, F, lst,
    hT, hC, hsep, hlist, hchart, hmass⟩
  let a : Atlas p k := ⟨T, C, γ, j, c, u, Q, R, A, F, lst⟩
  have hN : 0 < p.N k := hp.scale_pos k
  have hκ0 : 0 ≤ κ := by linarith
  have hpow : (p.N k ^ (ε / 2)) ^ 2 = p.N k ^ ε := by
    rw [← Real.rpow_two, ← Real.rpow_mul hN.le]
    congr 1
    ring
  refine ⟨κ, hκ, hκN.trans (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k)
    (by linarith)), a, hT.trans ?_, ?_, ⟨hC, hsep, hchart, hmass⟩, hlist⟩
  · exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one k) (by linarith)
  · intro b
    have hdet := (det_time_bound hκ0 (hchart b)).trans (pow_le_pow_left₀ hκ0 hκN 2)
    simpa only [neg_zero, zero_add, hpow] using hdet

/-- Coarsening costs at most the global horizon minus the available remaining
rate. The density cap of the coarsened problem may be chosen separately. -/
lemma horizon_coarsened_lower (hc : Composition) (hi : Initial)
    {p : Data} (hp : Valid p) {r d U : ℝ} {G}
    (hr : 0 ≤ r) (hrL : r < p.L)
    (hout : Valid {p with L := r, d := d, G := G})
    (hupper : ∀ q : Data, Valid q → q.d = p.d → q.S = p.S → q.η = p.η →
      Horizon q ≤ U * q.L) :
    Horizon p ≤ Horizon {p with L := r, d := d, G := G} + U * (p.L - r) := by
  let out : Data := {p with L := r, d := d, G := G}
  have houtV : Valid out := hout
  have hlower : Horizon p - U * (p.L - r) ≤ Horizon out := by
    apply le_csInf (costs_nonempty hi houtV)
    intro h hh
    have hk := k4_coarsened_outer_horizon_composition.own_depth_preparation
      out.N out.K out.L out.d out.S out.η out.W out.ω out.ν out.E out.P out.B out.f out.g out.G
      houtV h hh
    have hk' : k4_coarsened_outer_horizon_composition.known
        p.N p.K p.L p.W p.ω p.ν p.E p.B p.f r h :=
      k4_coarsened_outer_horizon_composition.known_finer
        (fun k => hp.scale_ge_one k) hrL.le hk
    obtain ⟨q, hq, hqL, hqd, hqS, hqη, hcost, hnarrow⟩ :=
      hc p hp r h 0 hr hrL (known_plain_zero hp hk')
    have hcomp := horizon_composition_le hi hp hq hcost
    have hu := hupper q hq hqd hqS hqη
    rw [hqL] at hu
    linarith
  linarith

lemma horizon_coarsened_lower_le (hc : Composition) (hi : Initial)
    {p : Data} (hp : Valid p) {r d U : ℝ} {G}
    (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (hout : Valid {p with L := r, d := d, G := G})
    (hupper : ∀ q : Data, Valid q → q.d = p.d → q.S = p.S → q.η = p.η →
      Horizon q ≤ U * q.L) :
    Horizon p ≤ Horizon {p with L := r, d := d, G := G} + U * (p.L - r) := by
  rcases eq_or_lt_of_le hrL with heq | hlt
  · subst r
    change Horizon p ≤ Horizon p + U * (p.L - p.L)
    simp
  · exact horizon_coarsened_lower hc hi hp hr hlt hout hupper

end
end Submission.Obl.k4_raw_critical_segment_forests
