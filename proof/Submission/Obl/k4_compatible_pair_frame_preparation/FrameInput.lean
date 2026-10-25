import Submission.Obl.k4_compatible_pair_frame_preparation.NativeSample
import Submission.Obl.k4_compatible_pair_frame_preparation.FrameCoverage
import Submission.Obl.k4_terminal_label_saturation.ChartMonotonicity

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set MvPolynomial
open Construction

namespace NativeSample

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ}
    {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (p : NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

/-- Choose isotropic fitting precisely when the normal condition allows it. -/
noncomputable def toPrep : PrepData where
  W := Wk
  T := p.T
  s := p.s
  C := p.C
  γ := p.γ
  j := p.j
  c := p.c
  u := p.v₀
  Q := p.Q
  R := p.R
  A := p.A
  F := p.F
  lst := p.lst
  B := Bk
  Good := p.Good
  iso := decide (p.R₁ ≤ 8 * Nk ^ a * p.R₂)
  R₁ := p.R₁
  R₂ := p.R₂
  g := min (1 / 8) (Nk ^ a * p.R₂ / p.R₁)
  κ₀ := p.κ
  Kb := ⌈2 * (78 * (4 * p.κ)) + 1⌉₊
  dfl := Nk ^ (-a)

/-- The native chart and format hypotheses supply the frame construction. -/
theorem toPrep_hyp (hN : 2 ≤ Nk) (hB : ∀ γ, 0 < Bk γ) :
    p.toPrep.Hyp Nk M D L Ek := by
  have hR₁ : 0 < p.R₁ := p.hR₂pos.trans_le p.hR21
  have hNp : 0 < Nk := by linarith
  have hR₂ := p.hR₂pos
  refine {
    chart := ?_
    disj := p.hdisj
    r₁lo := fun b => (p.hscales b).1
    r₁hi := fun b => (p.hscales b).2.1
    r₂lo := fun b => (p.hscales b).2.2.1
    r₂hi := fun b => (p.hscales b).2.2.2
    R₁pos := hR₁
    R₂pos := p.hR₂pos
    R21 := p.hR21
    gpos := lt_min (by norm_num) (by positivity)
    g8 := min_le_left _ _
    κ₀one := p.κ_one
    hKb := Nat.le_ceil _
    Bpos := hB
    Good_sub := fun γ => (p.hGood γ).2.1
    Good_meas := fun γ => (p.hGood γ).1
    N2 := hN }
  intro b
  exact Submission.Obl.k4_terminal_label_saturation.chart_mono (by linarith) le_rfl le_rfl (lt_of_lt_of_le zero_lt_one p.κ_one) le_rfl
    (hB (p.γ b)).le (p.hchart b) And.right

/-- Coherent normals ensure that the native witness lists the source frame. -/
theorem pair_compatible (hN : 2 ≤ Nk) (hB : ∀ γ, 0 < Bk γ)
    {b b' : Fin p.C} {z : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ)}
    (hz : z ∈ p.H b b') :
    p.toPrep.src b ∈ p.toPrep.compat b' := by
  classical
  let hp := p.toPrep_hyp hN hB
  obtain ⟨hγ, hJ, hF, hF', hG, hG', hder, halign⟩ := (p.hH b b').2 z hz
  have hcoarse : coarseIdx (p.j b) = coarseIdx (p.j b') := by
    apply Fin.ext
    exact hJ
  have hconf (b₀ : Fin p.C) (hz₀ : z.1 ∈ p.A b₀) :
      OldConfined (p.j b₀) (p.c b₀) (p.v₀ b₀) (p.Q b₀) p.κ z.1 :=
    fun t ht => ((hp.whole b₀ hz₀).2.2 t ht).1
  have hc := srcKey_mem_or_separated p.γ p.j p.c p.v₀ p.Q
    (p.toPrep.iso = true) hp.gpos hp.g8 hp.R₁pos hp.R₂pos hp.R21
    (by linarith [p.κ_one])
    (hp.det b) (hp.r₁lo b) (hp.r₁hi b) (hp.r₂hi b)
    (hp.det b') (hp.r₁lo b') (hp.r₁hi b') (hp.r₂hi b') hγ hcoarse
    (hconf b (hp.sel b hF).2.1) (hconf b' (hp.sel b' hF').2.1) hp.hKb
  rcases hc with hc | ⟨hiso, hsep⟩
  · exact Finset.mem_insert_of_mem hc
  · exfalso
    rcases halign trivial with halign | halign
    · apply hiso
      simpa only [toPrep, decide_eq_true_eq] using halign
    · have hangle : |Submission.Lib.K4VelocityStrips.stripWedge
          (Construction.nrm (p.Q b)) (Construction.nrm (p.Q b'))| ≤ p.toPrep.g := halign
      exact (not_lt_of_ge hangle) hsep

/-- Every native row is retained in the source-entry row, under its original law. -/
theorem pair_retained (hN : 2 ≤ Nk) (hB : ∀ γ, 0 < Bk γ)
    (b : Fin p.C) (z : (ℕ × (Fin 6 → ℝ)) × (ℝ × ℝ))
    (hz : ∃ b', z ∈ p.H b b') :
    ∃ s', z ∈ p.toPrep.H (p.toPrep.srcEnt b) s' := by
  obtain ⟨b', hz⟩ := hz
  obtain ⟨hγ, hJ, hF, hF', hG, hG', hder, halign⟩ := (p.hH b b').2 z hz
  apply (p.toPrep_hyp hN hB).native_pair_mem (p.pair_compatible hN hB hz)
    ⟨hF, p.hhalf b (z.1, z.2.1) hF⟩ ⟨hF', p.hhalf b' (z.1, z.2.2) hF'⟩ hG
  simpa only [toPrep, mul_comm] using hder (p.R b') (Or.inr rfl) z.2.1 (Or.inl rfl)

/-- Native coverage is preserved, with only an enlargement of subpower slack. -/
theorem coverage (hN : 2 ≤ Nk) (hB : ∀ γ, 0 < Bk γ)
    {κ : ℝ} (hκ : p.κ ≤ κ) :
    ENNReal.ofReal (4 * κ⁻¹) ≤
      ∑ s, ENNReal.ofReal (ωk (p.toPrep.fγ (p.toPrep.frame s)) * (2 : ℝ) ^ p.T) *
        ((νk (p.toPrep.fγ (p.toPrep.frame s))).prod (volume.prod volume))
          {z | ∃ s', z ∈ p.toPrep.H s s'} := by
  have hκp : 0 < p.κ := by linarith [p.κ_one]
  calc
    ENNReal.ofReal (4 * κ⁻¹) ≤ ENNReal.ofReal (4 * p.κ⁻¹) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hκp hκ) (by norm_num)
    _ ≤ _ := p.hcoverage.trans (p.toPrep.native_coverage_le νk ωk p.H (p.pair_retained hN hB))

end NativeSample
end Submission.Obl.k4_compatible_pair_frame_preparation
