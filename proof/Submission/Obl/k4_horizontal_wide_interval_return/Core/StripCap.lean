import Submission.Obl.k4_horizontal_wide_interval_return.Core.Basics

/-!
# The chart strip cap

A chart of the three-layer datum fixes the velocity bin `⌊b₃/χ⌋` and the intercept bin
`⌊b₀/χ⌋`; with an interval of `b₁` and the horizontal relation `b₄ ≈ -b₀` its base points
`(t, b₀ + t b₃, b₁ + t b₄)` lie in a moving box.  A hidden window of width `≤ m β` around
a moving offset (varying by at most `θ ≤ β` across base cells of side `δ`) is then charged
to the frozen joint caps at hidden resolution `β`, with the original palette weight of
the velocity bin.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.Core

open MeasureTheory Set Filter
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Base points of a chart strip lie in a moving box of time radius `1/2`. -/
theorem chart_basePt_mem_movingBox {b : α → Fin 6 → ℝ} {p : α × ℝ} {χ : ℝ} {κ0 κ1 : ℤ}
    {ylo yhi ζ₀ : ℝ} (hχ : 0 < χ)
    (h3 : ⌊b p.1 3 / χ⌋ = κ0) (h0 : ⌊b p.1 0 / χ⌋ = κ1) (hlo : ylo ≤ b p.1 1)
    (hhi : b p.1 1 ≤ yhi) (ht : p.2 ∈ Icc (0 : ℝ) 1) (hh : |b p.1 4 + b p.1 0| ≤ ζ₀) :
    basePt b p ∈ movingBox (1 / 2) (1 / 2)
      ![(κ1 : ℝ) * χ + χ / 2, (ylo + yhi) / 2]
      ![(κ0 : ℝ) * χ + χ / 2, -((κ1 : ℝ) * χ + χ / 2)]
      ![χ, (yhi - ylo) / 2 + χ / 2 + ζ₀] := by
  have hb3lo : (κ0 : ℝ) * χ ≤ b p.1 3 := by
    have := Int.floor_le (b p.1 3 / χ); rw [h3, le_div_iff₀ hχ] at this; linarith
  have hb3hi : b p.1 3 < ((κ0 : ℝ) + 1) * χ := by
    have := Int.lt_floor_add_one (b p.1 3 / χ); rw [h3, div_lt_iff₀ hχ] at this; linarith
  have hb0lo : (κ1 : ℝ) * χ ≤ b p.1 0 := by
    have := Int.floor_le (b p.1 0 / χ); rw [h0, le_div_iff₀ hχ] at this; linarith
  have hb0hi : b p.1 0 < ((κ1 : ℝ) + 1) * χ := by
    have := Int.lt_floor_add_one (b p.1 0 / χ); rw [h0, div_lt_iff₀ hχ] at this; linarith
  obtain ⟨ht0, ht1⟩ := ht
  rw [abs_le] at hh
  refine ⟨?_, ?_⟩
  · show |p.2 - 1 / 2| ≤ 1 / 2
    rw [abs_le]; constructor <;> linarith
  · intro i
    fin_cases i
    · show |b p.1 0 + p.2 * b p.1 3 - ((κ1 : ℝ) * χ + χ / 2 + p.2 * ((κ0 : ℝ) * χ + χ / 2))| ≤ χ
      rw [abs_le]
      constructor <;> nlinarith
    · show |b p.1 1 + p.2 * b p.1 4 - ((ylo + yhi) / 2 + p.2 * -((κ1 : ℝ) * χ + χ / 2))| ≤
        (yhi - ylo) / 2 + χ / 2 + ζ₀
      have hb4lo : -((κ1 : ℝ) * χ + χ / 2) - (χ / 2 + ζ₀) ≤ b p.1 4 := by linarith
      have hb4hi : b p.1 4 ≤ -((κ1 : ℝ) * χ + χ / 2) + (χ / 2 + ζ₀) := by linarith
      have hz : 0 ≤ χ / 2 + ζ₀ := by linarith [abs_nonneg (b p.1 4 + b p.1 0)]
      rw [abs_le]
      constructor <;> nlinarith

/-- A value in a window of width `≤ m β` lies in one of `m` consecutive bins of width `β`. -/
theorem exists_window_bin {y W β : ℝ} {m : ℕ} (hm : 1 ≤ m) (hβ : 0 < β) (hW : W ≤ m * β)
    (h0 : 0 ≤ y) (h1 : y ≤ W) : ∃ j ∈ Finset.range m, (j : ℝ) * β ≤ y ∧ y ≤ ((j : ℝ) + 1) * β := by
  set f : ℕ := ⌊y / β⌋₊
  have hf1 : (f : ℝ) ≤ y / β := Nat.floor_le (div_nonneg h0 hβ.le)
  have hf2 : y / β < (f : ℝ) + 1 := Nat.lt_floor_add_one _
  have hf1' : (f : ℝ) * β ≤ y := by rwa [le_div_iff₀ hβ] at hf1
  have hf2' : y < ((f : ℝ) + 1) * β := by rwa [div_lt_iff₀ hβ] at hf2
  by_cases hfm : f < m
  · exact ⟨f, Finset.mem_range.mpr hfm, hf1', hf2'.le⟩
  · refine ⟨m - 1, Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · have hle : ((m - 1 : ℕ) : ℝ) ≤ f := by
        have : m - 1 ≤ f := by omega
        exact_mod_cast this
      nlinarith
    · have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub hm]; push_cast; ring
      rw [this]; linarith

/-- **Chart strip cap.** -/
theorem chart_strip_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s' v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s' v')
    {χ : ℝ} (hχ : χ = N ^ (-v')) (κ0 κ1 : ℤ) {ylo yhi ζ₀ W θ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hyl : ylo ≤ yhi) (hζ₀ : 0 ≤ ζ₀) (hW : W ≤ m * N ^ (-s'))
    (hθ : 0 ≤ θ) (hθa : θ ≤ N ^ (-s'))
    (hδχ : (|(κ0 : ℝ) * χ| + |(κ1 : ℝ) * χ| + χ + 1) * N ^ (-r) ≤ χ / 2)
    (hdr : N ^ (-r) ≤ 1 / 2)
    (o : ℝ → ℝ → ℝ) (E : Set (α × ℝ))
    (hE : ∀ p ∈ E, ⌊b p.1 3 / χ⌋ = κ0 ∧ ⌊b p.1 0 / χ⌋ = κ1 ∧ ylo ≤ b p.1 1 ∧
      b p.1 1 ≤ yhi ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ |b p.1 4 + b p.1 0| ≤ ζ₀ ∧
      o (basePt b p 0) (basePt b p 2) - W / 2 ≤ hidden b p ∧
      hidden b p ≤ o (basePt b p 0) (basePt b p 2) + W / 2)
    (ho : ∀ p ∈ E, ∀ y : Fin 3 → ℝ, (∀ i, |basePt b p i - y i| ≤ N ^ (-r)) →
      |o (basePt b p 0) (basePt b p 2) - o (y 0) (y 2)| ≤ θ) :
    μ E ≤ ENNReal.ofReal (3000 * K * m * χ * ((yhi - ylo) / 2 + χ / 2 + ζ₀) *
      (N ^ (-s')) ^ d) * π {w | ⌊w / χ⌋ = κ0} := by
  have hχpos : 0 < χ := by rw [hχ]; exact Real.rpow_pos_of_pos hN _
  have hδpos : 0 < N ^ (-r) := Real.rpow_pos_of_pos hN _
  have hβpos : 0 < N ^ (-s') := Real.rpow_pos_of_pos hN _
  set β := N ^ (-s') with hβ
  set δ := N ^ (-r) with hδ
  set L : ℝ := |(κ0 : ℝ) * χ| + |(κ1 : ℝ) * χ| + χ with hL
  set center : Fin 2 → ℝ := ![(κ1 : ℝ) * χ + χ / 2, (ylo + yhi) / 2] with hcenter
  set velocity : Fin 2 → ℝ := ![(κ0 : ℝ) * χ + χ / 2, -((κ1 : ℝ) * χ + χ / 2)]
    with hvelocity
  set width : Fin 2 → ℝ := ![χ, (yhi - ylo) / 2 + χ / 2 + ζ₀] with hwidth
  have hLnn : 0 ≤ L := by positivity
  have hvel : ∀ i, |velocity i| ≤ L := by
    intro i
    fin_cases i
    · show |(κ0 : ℝ) * χ + χ / 2| ≤ L
      have := abs_add_le ((κ0 : ℝ) * χ) (χ / 2)
      rw [abs_of_pos (by positivity : 0 < χ / 2)] at this
      rw [hL]; linarith [abs_nonneg ((κ1 : ℝ) * χ)]
    · show |-((κ1 : ℝ) * χ + χ / 2)| ≤ L
      rw [abs_neg]
      have := abs_add_le ((κ1 : ℝ) * χ) (χ / 2)
      rw [abs_of_pos (by positivity : 0 < χ / 2)] at this
      rw [hL]; linarith [abs_nonneg ((κ0 : ℝ) * χ)]
  have hLδ : L * δ ≤ χ / 2 := by
    have : L * δ ≤ (L + 1) * δ := by nlinarith
    rw [hL] at this ⊢; linarith
  have hδχ' : δ ≤ χ / 2 := by
    have : 1 * δ ≤ (L + 1) * δ := by nlinarith
    rw [hL] at this; linarith
  have hdw : ∀ i, δ ≤ width i := by
    intro i; fin_cases i
    · show δ ≤ χ; linarith
    · show δ ≤ (yhi - ylo) / 2 + χ / 2 + ζ₀; linarith
  have hmove : ∀ i, L * δ ≤ width i := by
    intro i; fin_cases i
    · show L * δ ≤ χ; linarith
    · show L * δ ≤ (yhi - ylo) / 2 + χ / 2 + ζ₀; linarith
  -- split the window into `m` bins
  let Ej : ℕ → Set (α × ℝ) := fun j => {p | p ∈ E ∧
    o (basePt b p 0) (basePt b p 2) - W / 2 + j * β ≤ hidden b p ∧
    hidden b p ≤ o (basePt b p 0) (basePt b p 2) - W / 2 + j * β + β}
  have hcover : E ⊆ ⋃ j ∈ Finset.range m, Ej j := by
    intro p hp
    obtain ⟨-, -, -, -, -, -, hlo, hhi⟩ := hE p hp
    obtain ⟨j, hj, h1, h2⟩ := exists_window_bin (y := hidden b p -
      (o (basePt b p 0) (basePt b p 2) - W / 2)) hm hβpos hW (by linarith) (by linarith)
    refine mem_iUnion₂.mpr ⟨j, hj, hp, by linarith, by linarith⟩
  have hbin : ∀ j, μ (Ej j) ≤ ENNReal.ofReal (3000 * K * width 0 * width 1 * β ^ d) *
      π {w | ⌊w / N ^ (-v')⌋ = κ0} := by
    intro j
    apply strip_window_cap hb hN hK hcap κ0
      (fun z => o (z 0) (z 2) - W / 2 + j * β) (Ej j) hθ hθa hLnn center velocity width
      hvel hdw hmove hdr
    · intro p hp y hy
      have := ho p hp.1 y hy
      calc |o (basePt b p 0) (basePt b p 2) - W / 2 + j * β - (o (y 0) (y 2) - W / 2 + j * β)|
          = |o (basePt b p 0) (basePt b p 2) - o (y 0) (y 2)| := by ring_nf
        _ ≤ θ := this
    · intro p hp
      obtain ⟨h3, h0, hlo, hhi, ht, hh, -, -⟩ := hE p hp.1
      refine ⟨by rw [← hχ]; exact h3, ?_, hp.2.1, ?_⟩
      · exact chart_basePt_mem_movingBox hχpos h3 h0 hlo hhi ht hh
      · have := hp.2.2; linarith
  have hπ : π {w | ⌊w / N ^ (-v')⌋ = κ0} = π {w | ⌊w / χ⌋ = κ0} := by rw [hχ]
  calc μ E ≤ μ (⋃ j ∈ Finset.range m, Ej j) := measure_mono hcover
    _ ≤ ∑ j ∈ Finset.range m, μ (Ej j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range m, ENNReal.ofReal (3000 * K * width 0 * width 1 * β ^ d) *
          π {w | ⌊w / N ^ (-v')⌋ = κ0} := Finset.sum_le_sum fun j _ => hbin j
    _ = (m : ENNReal) * (ENNReal.ofReal (3000 * K * width 0 * width 1 * β ^ d) *
          π {w | ⌊w / χ⌋ = κ0}) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hπ]
    _ = ENNReal.ofReal (3000 * K * m * χ * ((yhi - ylo) / 2 + χ / 2 + ζ₀) * β ^ d) *
          π {w | ⌊w / χ⌋ = κ0} := by
        rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        simp only [hwidth, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        ring

end

end Submission.Obl.k4_horizontal_wide_interval_return.Core
