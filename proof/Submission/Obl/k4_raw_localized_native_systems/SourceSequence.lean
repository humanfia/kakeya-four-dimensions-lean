import Submission.Obl.k4_raw_localized_native_systems.HomogeneousSources

/-
Adapted from this LOT tree, o197, session x0690, `SourceSequence.lean` (commit
f7206748), renamed into this obligation's namespace.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Nested true source geometry with common width bands and vanishing actual
slack. The original problem and every full source assignment remain explicit. -/
structure HomogeneousSourceSequence (p : Data) (kr w ε q band : ℝ)
    (m M D : ℕ) (s r : ℕ → ℝ) where
  index : ℕ → ℕ
  mono : StrictMono index
  forest : (n : ℕ) → k4_raw_critical_segment_forests.Forest p (index n)
  width : (n : ℕ) → Fin (forest n).C → ℝ
  levelWidth : ℕ → ℕ → ℝ
  core : ∀ n, (forest n).Core M D m r
  prepared : ∀ n, (forest n).Prepared r (sourceLists (forest n) r)
  subpower : ∀ loss : ℝ, 0 < loss → ∀ᶠ n in atTop, (forest n).κ ≤ p.N (index n) ^ loss
  time : ∀ n i, i < m → p.N (index n) ^ (kr * s i - ε) ≤ (2 : ℝ) ^ (forest n).T i ∧
    (2 : ℝ) ^ (forest n).T i ≤ p.N (index n) ^ (kr * s i + ε) ∧
    (2 : ℝ) ^ (forest n).T i ≤ p.N (index n) ^ M
  width_exact : ∀ n b, p.N (index n) ^ (-width n b) =
    |Matrix.det ((forest n).Q b)| * (4 : ℝ) ^ (forest n).T ((forest n).lev b)
  width_band : ∀ n b, |width n b - levelWidth n ((forest n).lev b)| ≤ band
  width_lower : ∀ n i, i < m →
    w * r i - (m : ℝ) * (q + 2 * band) ≤ levelWidth n i ∧
    levelWidth n i + w * (r (m - 1) - r i) - (m : ℝ) * (q + 2 * band) ≤
      levelWidth n (m - 1)

/-- A single near-maximizing exact problem supplies homogeneous nested true
sources at every late accuracy. The width-band selection has a fixed cost. -/
theorem exists_homogeneous_sources {ds kr S η w ε q band t ζ : ℝ}
    (hi : initialRaw) (hes : es ds kr S η) (hnb : ¬ widthRaw ds kr S η)
    (hw : 0 ≤ w) (m : ℕ) (s : ℕ → ℝ) (hm : 0 < m)
    (hs : ∀ i, i < m → 0 < s i ∧ s i ≤ 1)
    (hstep : ∀ i, i + 1 < m → s i < s (i + 1))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) (hband : 0 < band)
    (ht : 0 < t) (hζ : 0 < ζ) :
    ∃ p : Data, Near ds kr S η t p ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ 1 → |p.f r - p.f 0 - ds * r| ≤ ζ) ∧
      ∃ (r : ℕ → ℝ) (M D : ℕ),
        (∀ i, i < m → |r i - s i| ≤ ε ∧ 0 < r i ∧ r i ≤ s i) ∧
        Nonempty (HomogeneousSourceSequence p kr w ε q band m M D s r) := by
  classical
  obtain ⟨p, hp, hprofile, r, M, D, hr, φ, a, width, lst, hφ, hcert⟩ :=
    exists_prepared_prefix hi hes hnb hw m s hm hs hstep hε hε1 hq ht hζ
  obtain ⟨B, hB, hselect⟩ := select_source_widths m M band hm hband
  have hsample (n : ℕ) := hselect hp.1 (a n) (width n) (lst n) r w q hq.le
    (hcert n).1.2.1 (hcert n).2.1 (hcert n).1.2.2.2
  choose b vwidth nw hκ hT hcore hprepared hmeas hexact hbin hlower using hsample
  have hNlim : Tendsto (fun n => p.N (φ n)) atTop atTop :=
    hp.1.scale_tendsto.comp hφ.tendsto_atTop
  have hsubpower (loss : ℝ) (hloss : 0 < loss) :
      ∀ᶠ n in atTop, (b n).κ ≤ p.N (φ n) ^ loss := by
    have hhalf : 0 < loss / 2 := by positivity
    have hconst : ∀ᶠ n in atTop, (B : ℝ) ≤ p.N (φ n) ^ (loss / 2) :=
      ((tendsto_rpow_atTop hhalf).comp hNlim).eventually_ge_atTop (B : ℝ)
    have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < loss / 2 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hhalf)
    filter_upwards [hconst, hsmall] with n hconst hsmall
    have hN0 := hp.1.scale_pos (φ n)
    calc
      (b n).κ = (B : ℝ) * (a n).κ := hκ n
      _ ≤ (p.N (φ n) ^ (loss / 2)) * p.N (φ n) ^ (1 / ((n : ℝ) + 1)) :=
        mul_le_mul hconst (hcert n).1.1 (by linarith [(hcert n).1.2.1.1])
          (Real.rpow_nonneg hN0.le _)
      _ ≤ (p.N (φ n) ^ (loss / 2)) * p.N (φ n) ^ (loss / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hp.1.scale_ge_one _) hsmall.le) (by positivity)
      _ = p.N (φ n) ^ loss := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
  refine ⟨p, hp, hprofile, r, M, D, hr, ⟨{
    index := φ
    mono := hφ
    forest := b
    width := vwidth
    levelWidth := nw
    core := hcore
    prepared := hprepared
    subpower := hsubpower
    time := ?_
    width_exact := hexact
    width_band := hbin
    width_lower := hlower }⟩⟩
  intro n i hi
  rw [hT n]
  exact (hcert n).1.2.2.1 i hi

end
end Submission.Obl.k4_raw_localized_native_systems
