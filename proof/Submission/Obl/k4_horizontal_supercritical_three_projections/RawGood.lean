import Submission.Obl.k4_horizontal_supercritical_three_projections.RawAsymptotics
import Submission.Obl.k4_horizontal_supercritical_three_projections.RawInterface

/-!
# Almost-everywhere good lines of the original law

The original incidence law sees only bounded horizontal contact trajectories:
this is `OriginalGood`, and the hidden coordinate is bounded by `K` on `[0,1]`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter Parent
open scoped ENNReal

noncomputable section

namespace HorizontalModel

variable {α : Type} [MeasurableSpace α] {m : HorizontalModel α}

/-- A `ν`-a.e. property of trajectories holds `μ`-a.e. for incidences. -/
theorem Valid.ae_of_ae_nu (h : m.Valid) (k : ℕ) {Pr : α → Prop}
    (hP : ∀ᵐ l ∂m.ν k, Pr l) : ∀ᵐ p ∂m.μ k, Pr p.1 := by
  have hdom := (h.basic k).2.2.2.1
  have hnull : m.ν k {l | ¬ Pr l} = 0 := by rwa [ae_iff] at hP
  rw [ae_iff]
  apply le_antisymm _ bot_le
  calc m.μ k {p : α × ℝ | ¬ Pr p.1} ≤ m.μ k ({l | ¬ Pr l} ×ˢ univ) :=
        measure_mono (fun p hp => ⟨hp, trivial⟩)
    _ ≤ (ENNReal.ofReal (m.K k) • (m.ν k).prod volume) ({l | ¬ Pr l} ×ˢ univ) := hdom _
    _ = 0 := by
        rw [Measure.smul_apply, Measure.prod_prod, hnull, zero_mul, smul_zero]

theorem Valid.ae_time (h : m.Valid) (k : ℕ) : ∀ᵐ p ∂m.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  refine measure_mono_null ?_ (h.basic k).2.2.2.2.2.1
  intro p hp
  exact fun h => hp h.2

/-- If a depth has no true block, the cover makes the incidence law null. -/
theorem AtDepth.ae_of_empty {k : ℕ} {s R : ℝ} (hA : m.AtDepth k s R)
    (hn : m.n k s = 0) {Pr : α × ℝ → Prop} : ∀ᵐ p ∂m.μ k, Pr p := by
  obtain ⟨-, -, -, -, -, hcover, -⟩ := hA
  filter_upwards [hcover] with p hp
  obtain ⟨i, -⟩ := hp
  exact absurd i.2 (by omega)

/-- The hidden coordinate is bounded on the whole unit time interval, and the
horizontal contact holds, `μ`-a.e., at every index where a depth is prepared. -/
theorem AtDepth.ae_hidden_contact (h : m.Valid) {k : ℕ} {s R : ℝ}
    (hA : m.AtDepth k s R) :
    ∀ᵐ p ∂m.μ k, (∀ t ∈ Icc (0 : ℝ) 1, |m.b k p.1 2 + t * m.b k p.1 5| ≤ m.K k) ∧
      |m.b k p.1 4 + m.b k p.1 0| ≤ m.N k ^ (-m.e₀) := by
  by_cases hn : m.n k s = 0
  · exact hA.ae_of_empty hn
  have hi : 0 < m.n k s := Nat.pos_of_ne_zero hn
  obtain ⟨-, -, -, -, hblk, -, -⟩ := hA
  obtain ⟨hP, hcontact, -⟩ := (hblk ⟨0, hi⟩).2.2.2.2.2.2.2.2 rfl
  have hbase := (h.basic k).2.2.2.2.2.2.2.2.2
  filter_upwards [hbase, hcontact] with p hp hc
  refine ⟨fun t ht => ?_, hc⟩
  have := (hp.1 t ht).1
  rwa [hP, MvPolynomial.eval_X] at this

/-- **Original good lines**: `μ`-a.e. trajectory is bounded with horizontal contact. -/
theorem Valid.originalGood (h : m.Valid) {s : ℝ} (hs : 0 < s) (hsU : s ≤ m.U) :
    OriginalGood m.N m.K m.e₀ m.b m.μ := by
  set R : ℝ := 1 + 1 / s with hR
  have hR1 : 1 < R := by
    rw [hR]
    have : 0 < 1 / s := by positivity
    linarith
  have hRs : R⁻¹ ≤ s := by
    rw [hR, inv_le_comm₀ (by positivity) hs]
    have : 1 / s ≤ 1 + 1 / s := by linarith
    simpa [one_div] using this
  filter_upwards [h.prepared R hR1] with k hk
  have hA := hk s hRs hsU
  have hbound := h.ae_of_ae_nu k (h.basic k).2.2.2.2.2.2.2.2.1
  filter_upwards [hA.ae_hidden_contact h, hbound] with p hp hb
  obtain ⟨hx, hc⟩ := hp
  have h0 := hx 0 ⟨le_rfl, zero_le_one⟩
  have h1 := hx 1 ⟨zero_le_one, le_rfl⟩
  simp only [zero_mul, add_zero, one_mul] at h0 h1
  have hK := h.K_ge k
  have a0 := abs_nonneg (m.b k p.1 0)
  have a1 := abs_nonneg (m.b k p.1 1)
  have a3 := abs_nonneg (m.b k p.1 3)
  have a4 := abs_nonneg (m.b k p.1 4)
  refine ⟨fun e => ?_, by linarith, by linarith, hc⟩
  fin_cases e
  · show |m.b k p.1 0| ≤ 3 * m.K k; linarith
  · show |m.b k p.1 1| ≤ 3 * m.K k; linarith
  · show |m.b k p.1 2| ≤ 3 * m.K k; linarith
  · show |m.b k p.1 3| ≤ 3 * m.K k; linarith
  · show |m.b k p.1 4| ≤ 3 * m.K k; linarith
  · show |m.b k p.1 5| ≤ 3 * m.K k
    have : |m.b k p.1 5| ≤ |m.b k p.1 2 + m.b k p.1 5| + |m.b k p.1 2| := by
      calc |m.b k p.1 5| = |(m.b k p.1 2 + m.b k p.1 5) - m.b k p.1 2| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith

end HorizontalModel

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
