import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortBound

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Filter
open Inherited.Native Inherited.Core Inherited.CompareSheets

noncomputable section

variable {α : Type} [MeasurableSpace α]

/- Adapted from this LOT tree g-oai-074, obligation o250, session x0879,
commit 525ce8d3c8ed1d02854b5f6c797e220d2ac13ddd, file
Submission/Obl/k4_horizontal_wide_interval_return/Native/ShortBound.lean.
This is the inherited sheet coefficient proof with the hidden accuracy
independent of the coarse time depth. Earlier provenance: none. -/
theorem sheet_entry_coefficients (cfg : Inherited.Data α) (k : ℕ) (s : ℝ) {ε R χ D : ℝ}
    {depth : Fin 3 → ℝ} (L : LayerDatum cfg k ε R χ D depth) {m ζ B a : ℝ} (hχ : 0 < χ)
    (hD : 0 < D) (hm : 0 < m)
    (hdrift : ζ + χ ≤ D / 4) (hsmallD : 4 * m + slotLen cfg k s * (ζ + χ) ≤ 4 * D)
    (ha : 0 < a) (h : Fin 3) (i : Fin (L.np h)) (jj : Fin (2 ^ cfg.T k s))
    (κ : Fin 3 → ℤ) {l : α} (hl : l ∈ pieceLab cfg k s L m h i jj κ)
    (hlζ : |cfg.b k l 4 + cfg.b k l 0| ≤ ζ)
    (hBsh : 8 * (11 * (160 * cfg.N k ^ ε) / a) ≤ B) :
    ∀ e, |sheetKeyCoeff (L.G h i) (a) χ m (slotLen cfg k s)
      (slotStart cfg k s jj) κ e| ≤ B := by
  obtain ⟨hlC, hκ⟩ := hl
  have hκ' : slotKey (cfg.b k) χ m (slotStart cfg k s jj) l = κ := hκ
  have hq0 : 0 < slotLen cfg k s := slotLen_pos cfg k s
  have hH := Inherited.CompareSheets.sheetCoeff_bound (L.degree h i) (L.strip h i)
  have hcoef := sheetKeyCoeff_bound (L.degree h i) hD hH ha κ (χ := χ) (m := m)
    (q := slotLen cfg k s) (t₀ := slotStart cfg k s jj)
    (fun τ hτ => by
      have ht := shortDefs_slot_time_unit cfg k s jj hτ
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    (fun τ hτ y hy => by
      have ht := shortDefs_slot_time_unit cfg k s jj hτ
      have hηl : etaFun ((L.qp h i 2 : ℝ) * D) (-((L.qp h i 1 : ℝ) * χ)) D
          (slotStart cfg k s jj + slotLen cfg k s * τ)
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4) ∈
            Icc (1 / 4 : ℝ) 1 :=
        L.etaFun_mem (p := (l, slotStart cfg k s jj + slotLen cfg k s * τ)) hlC hχ hD ht hlζ
          hdrift
      have hY := key_Y_near hχ hm.ne' hq0.le hκ' hlζ hτ
      have hsl := sliceY_mem (cfg.b k) m (slotStart cfg k s jj) l
      have hdY : |domY χ m (slotLen cfg k s) κ τ y -
          domY χ m (slotLen cfg k s) κ τ (sliceY (cfg.b k) m (slotStart cfg k s jj) l)| ≤
          4 * m := by
        have e : domY χ m (slotLen cfg k s) κ τ y -
            domY χ m (slotLen cfg k s) κ τ (sliceY (cfg.b k) m (slotStart cfg k s jj) l) =
            2 * m * (y - sliceY (cfg.b k) m (slotStart cfg k s jj) l) := by
          unfold domY; ring
        rw [e, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * m)]
        have : |y - sliceY (cfg.b k) m (slotStart cfg k s jj) l| ≤ 2 := by
          rw [abs_le]; constructor <;> linarith [hy.1, hy.2, hsl.1, hsl.2]
        nlinarith
      have hdiff : |domY χ m (slotLen cfg k s) κ τ y -
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)| ≤
          4 * m + slotLen cfg k s * (ζ + χ) := by
        have h1 := abs_sub_le (domY χ m (slotLen cfg k s) κ τ y)
          (domY χ m (slotLen cfg k s) κ τ (sliceY (cfg.b k) m (slotStart cfg k s jj) l))
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)
        rw [abs_sub_comm (domY χ m (slotLen cfg k s) κ τ
          (sliceY (cfg.b k) m (slotStart cfg k s jj) l))] at h1
        linarith
      have hdη := etaFun_sub (y₀ := (L.qp h i 2 : ℝ) * D) (v := -((L.qp h i 1 : ℝ) * χ)) hD
        (slotStart cfg k s jj + slotLen cfg k s * τ) (domY χ m (slotLen cfg k s) κ τ y)
        (slotStart cfg k s jj + slotLen cfg k s * τ)
        (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)
      simp only [sub_self, abs_zero, mul_zero, add_zero] at hdη
      have h1 : |domY χ m (slotLen cfg k s) κ τ y -
          (cfg.b k l 1 + (slotStart cfg k s jj + slotLen cfg k s * τ) * cfg.b k l 4)| /
          (4 * D) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hdη' := hdη.trans h1
      rw [abs_le] at hdη' ⊢
      obtain ⟨hη1, hη2⟩ := hηl
      constructor <;> linarith [hdη'.1, hdη'.2])
  intro e
  exact (hcoef e).trans hBsh

open scoped Classical in

/-- A positive occupied key has positive original palette weight. -/
theorem occupied_key_palette_pos {μ ρs : Measure (α × ℝ)} {π : Measure ℝ}
    [IsFiniteMeasure π] {b : α → Fin 6 → ℝ}
    {N K d r sp vp m t₀ q : ℝ} {key : Fin 3 → ℤ}
    (hcap : JointCapAt μ π b N K d r sp vp) (hρμ : ρs ≤ μ)
    (C : Set α) (hkey : ∀ l ∈ C, slotKey b (N ^ (-vp)) m t₀ l = key)
    (hpos : 0 < ρs (C ×ˢ Icc t₀ (t₀ + q))) :
    0 < (π {v | ⌊v / N ^ (-vp)⌋ = key 0}).toReal := by
  have hπ0 : π {v | ⌊v / N ^ (-vp)⌋ = key 0} ≠ 0 := by
    intro hz
    have hv := velocityBin_null hcap (key 0) hz
    have hsub : C ×ˢ Icc t₀ (t₀ + q) ⊆
        {p : α × ℝ | ⌊b p.1 3 / N ^ (-vp)⌋ = key 0} := by
      intro p hp
      exact congrFun (hkey p.1 hp.1) 0
    have hzero : ρs (C ×ˢ Icc t₀ (t₀ + q)) = 0 :=
      le_antisymm ((hρμ _).trans ((measure_mono hsub).trans hv.le)) bot_le
    exact hpos.ne' hzero
  exact ENNReal.toReal_pos hπ0 (measure_ne_top _ _)

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
