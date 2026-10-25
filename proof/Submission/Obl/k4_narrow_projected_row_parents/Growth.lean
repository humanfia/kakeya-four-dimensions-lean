import Submission.Obl.k4_narrow_projected_row_parents.RowReadyOf
import Submission.Obl.k4_discrete_of_terminal_charts.Horizon

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter

/-- Finite addition preserves the subpower loss convention. -/
theorem Model.Subpow.add {N f g : ℕ → ℝ} (hNp : ∀ k, 0 < N k)
    (hNt : Tendsto N atTop atTop) (hf : Model.Subpow N f) (hg : Model.Subpow N g) :
    Model.Subpow N (fun k => f k + g k) := by
  intro ε hε
  have h2 : ∀ᶠ k in atTop, 2 ≤ N k ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hNt).eventually_ge_atTop _
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity), h2] with k hkf hkg hk2
  calc f k + g k ≤ 2 * N k ^ (ε / 2) := by linarith
    _ ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hk2 (Real.rpow_nonneg (hNp k).le _)
    _ = N k ^ ε := by rw [← Real.rpow_add (hNp k)]; congr 1; ring

/-- The explicit losses in the two-velocity row count remain subpower. -/
theorem rowReadyBound_subpow {N M C K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hM1 : ∀ k, 1 ≤ M k) (hC1 : ∀ k, 1 ≤ C k) (hK1 : ∀ k, 1 ≤ K k)
    (hM : Model.Subpow N M) (hC : Model.Subpow N C) (hK : Model.Subpow N K) :
    Model.Subpow N (fun k => rowReadyBound (M k) (C k) (K k)) := by
  have hNp : ∀ k, 0 < N k := fun k => lt_of_lt_of_le zero_lt_one (hN k)
  have hM0 : ∀ k, 0 ≤ M k := fun k => zero_le_one.trans (hM1 k)
  have hC0 : ∀ k, 0 ≤ C k := fun k => zero_le_one.trans (hC1 k)
  have hK0 : ∀ k, 0 ≤ K k := fun k => zero_le_one.trans (hK1 k)
  have hc (a : ℝ) : Model.Subpow N (fun _ => a) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_const hNt a
  have hm {f g : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
      (hf : Model.Subpow N f) (hg : Model.Subpow N g) :
      Model.Subpow N (fun k => f k * g k) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_mul hNp hf0 hg0 hf hg
  have hp {f : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hf : Model.Subpow N f) (j : ℕ) :
      Model.Subpow N (fun k => f k ^ j) :=
    Submission.Obl.k4_discrete_of_terminal_charts.subpower_pow hN hf0 hf j
  have ha {f g : ℕ → ℝ} (hf : Model.Subpow N f) (hg : Model.Subpow N g) :
      Model.Subpow N (fun k => f k + g k) := hf.add hNp hNt hg
  have hMadd := ha hM (hc 1)
  have htwoc := hm (fun _ => by norm_num) hC0 (hc 2) hC
  have htwoc2 := hp (fun k => by positivity [hC0 k]) htwoc 2
  have hbase := hm (fun k => by positivity [hC0 k])
    (fun k => by positivity [hM0 k]) htwoc2 hMadd
  have hbase3 := hm (fun _ => by norm_num) (fun k => by positivity [hC0 k, hM0 k]) (hc 3) hbase
  have hC2 := hp hC0 hC 2
  have hinner := ha (ha (hc 4) hC) hbase3
  have h12c2 := hm (fun _ => by norm_num) (fun k => by positivity) (hc 12) hC2
  have hinner' := hm (fun k => by positivity) (fun k => by positivity [hC0 k, hM0 k]) h12c2 hinner
  have hinner'' := ha hinner' (hc 2)
  have hinner2 := hp (fun k => by positivity [hC0 k, hM0 k]) hinner'' 2
  have h18m := hm (fun _ => by norm_num) hM0 (hc 18) hM
  have h18mk := hm (fun k => by positivity [hM0 k]) hK0 h18m hK
  have hden := hm (fun _ => by norm_num) (fun k => by positivity) (hc 2)
    (hp (fun k => by positivity [hM0 k, hK0 k]) h18mk 2)
  have hbig := hm (fun k => by positivity) (fun k => by positivity) hC2 hinner2
  have hbig' := hm (fun k => by positivity) (fun k => by positivity) hbig hden
  have h2m := hm (fun _ => by norm_num) hM0 (hc 2) hM
  have htotal := ha (ha h2m hbase3) hbig'
  intro ε hε
  filter_upwards [htotal ε hε] with k hk
  convert hk using 1
  unfold rowReadyBound
  have hmne : M k ≠ 0 := (lt_of_lt_of_le zero_lt_one (hM1 k)).ne'
  have hkne : K k ≠ 0 := (lt_of_lt_of_le zero_lt_one (hK1 k)).ne'
  field_simp

end Submission.Obl.k4_narrow_projected_row_parents
