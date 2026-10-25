-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/WitnessFrame.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). The spanning frame and the qualified witnesses of
`cartesian_whole_state_row`, in its own form: a triple `J`, its inverse
frame `Ainv` with bounded entries, and on a retained state family `Ωst`
a `QualWitness` in every state and every velocity bin of the triple.
-/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.TripleWitnesses
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.QualWitness

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

/-- **The Cartesian witness frame.** -/
theorem cartesian_witness_frame {Λ σ : Type} [MeasurableSpace Λ] [MeasurableSpace σ]
    [MeasurableSingletonClass σ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ] (st : Λ × ℝ → σ) (hst : Measurable st)
    (v : Λ → Fin 2 → ℝ) (hv : Measurable v)
    (Fam : Finset σ) (Q : Set (Λ × ℝ)) (hQm : MeasurableSet Q)
    (Eref : Set (Λ × ℝ)) (Gs : σ → Fin 3 → ℝ) (t0 h : ℝ) (M : ℕ) (K err : ℝ)
    (hQ : ∀ w ∈ Q, w ∈ Eref ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
      QualWitness Eref st Gs t0 h M K err (1 / K) w)
    {Vq : ℝ} (hvQ : ∀ w ∈ Q, ∀ k, |v w.1 k| ≤ Vq)
    {ηq ps : ℝ} (hηq : 0 ≤ ηq) (hps : 0 ≤ ps)
    (hqual : ∀ D ∈ Fam, μ (st ⁻¹' {D} \ Q) ≤ ENNReal.ofReal ηq * μ (st ⁻¹' {D}))
    {wv pv : ℝ} (hwv : 0 < wv) (hpv : 0 < pv) (hpvw : pv ≤ wv / 2)
    (hstrip : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      μ (st ⁻¹' {D} ∩ {x | |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
        ENNReal.ofReal ps * μ (st ⁻¹' {D}))
    (πv : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure πv] {Kr : ℝ}
    (hpal : ∀ D ∈ Fam, ∀ B : Set (Fin 2 → ℝ), MeasurableSet B →
      μ (st ⁻¹' {D} ∩ {x | v x.1 ∈ B}) ≤ ENNReal.ofReal Kr * μ (st ⁻¹' {D}) * πv B) :
    ∃ (J : Fin 3 → Fin 2 → ℝ) (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (Ωst : Finset σ), Ωst ⊆ Fam ∧
      (Ωst.Nonempty → liftMatrix J * Ainv = 1 ∧ (∀ i k, |J i k| ≤ max 1 (Vq + pv)) ∧
        ∀ i k, |Ainv i k| ≤ 2 * (max 1 (Vq + pv)) ^ 2 / (wv / 2) ^ 2) ∧
      (∀ D ∈ (Ωst : Set σ), ∀ axis : Fin 3, ∃ w ∈ Eref, st w = D ∧
        (∀ k, |v w.1 k - J axis k| ≤ pv / 2) ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
        QualWitness Eref st Gs t0 h M K err (1 / K) w) ∧
      ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) * ∑ D ∈ Fam, μ (st ⁻¹' {D}) ≤
        ENNReal.ofReal Kr ^ 3 * ∑ D ∈ Ωst, μ (st ⁻¹' {D}) := by
  obtain ⟨J, Ωst, hsub, hdet, hwit, hmass⟩ := exists_spanning_witness_triple μ st hst v hv Fam Q
    hQm hηq hps hqual hwv hpv hpvw hstrip πv hpal
  refine ⟨J, (liftMatrix J)⁻¹, Ωst, hsub, ?_, ?_, hmass⟩
  · rintro ⟨D, hD⟩
    have hJ : ∀ i k, |J i k| ≤ max 1 (Vq + pv) := by
      intro i k
      obtain ⟨w, hwQ, -, hwv⟩ := hwit D hD i
      have h1 := hwv k
      have h2 := hvQ w hwQ k
      have : |J i k| ≤ Vq + pv := by
        calc |J i k| ≤ |v w.1 k| + |v w.1 k - J i k| := by
              have := abs_sub_abs_le_abs_sub (J i k) (v w.1 k)
              rw [abs_sub_comm (J i k)] at this
              linarith
          _ ≤ Vq + pv / 2 := add_le_add h2 h1
          _ ≤ Vq + pv := by linarith
      exact this.trans (le_max_right _ _)
    obtain ⟨hinv, hbound⟩ := liftMatrix_inverse_bound J (le_max_left 1 (Vq + pv)) hJ
      (by positivity) (hdet ⟨D, hD⟩)
    exact ⟨hinv, hJ, hbound⟩
  · intro D hD axis
    obtain ⟨w, hwQ, hst', hwv'⟩ := hwit D hD axis
    obtain ⟨hE, ht0, ht1, hqw⟩ := hQ w hwQ
    exact ⟨w, hE, hst', hwv', ht0, ht1, hqw⟩

/-- **The Cartesian witness frame, coarse bins only.** The bin laws are
dominated by the uniform law on the bin box of the velocity bound; no
velocity palette is assumed. -/
theorem cartesian_witness_frame_uniform {Λ σ : Type} [MeasurableSpace Λ] [MeasurableSpace σ]
    [MeasurableSingletonClass σ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ] (st : Λ × ℝ → σ) (hst : Measurable st)
    (v : Λ → Fin 2 → ℝ) (hv : Measurable v)
    (Fam : Finset σ) (Q : Set (Λ × ℝ)) (hQm : MeasurableSet Q)
    (Eref : Set (Λ × ℝ)) (Gs : σ → Fin 3 → ℝ) (t0 h : ℝ) (M : ℕ) (K err : ℝ)
    (hQ : ∀ w ∈ Q, w ∈ Eref ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
      QualWitness Eref st Gs t0 h M K err (1 / K) w)
    {Vq : ℝ} (hvQ : ∀ w ∈ Q, ∀ k, |v w.1 k| ≤ Vq)
    {ηq ps : ℝ} (hηq : 0 ≤ ηq) (hps : 0 ≤ ps)
    (hqual : ∀ D ∈ Fam, μ (st ⁻¹' {D} \ Q) ≤ ENNReal.ofReal ηq * μ (st ⁻¹' {D}))
    {wv pv : ℝ} (hwv : 0 < wv) (hpv : 0 < pv) (hpvw : pv ≤ wv / 2)
    (hstrip : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      μ (st ⁻¹' {D} ∩ {x | |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
        ENNReal.ofReal ps * μ (st ⁻¹' {D}))
    (hVq : 0 ≤ Vq) :
    ∃ (J : Fin 3 → Fin 2 → ℝ) (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (Ωst : Finset σ), Ωst ⊆ Fam ∧
      (Ωst.Nonempty → liftMatrix J * Ainv = 1 ∧ (∀ i k, |J i k| ≤ max 1 (Vq + pv)) ∧
        ∀ i k, |Ainv i k| ≤ 2 * (max 1 (Vq + pv)) ^ 2 / (wv / 2) ^ 2) ∧
      (∀ D ∈ (Ωst : Set σ), ∀ axis : Fin 3, ∃ w ∈ Eref, st w = D ∧
        (∀ k, |v w.1 k - J axis k| ≤ pv / 2) ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
        QualWitness Eref st Gs t0 h M K err (1 / K) w) ∧
      ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) * ∑ D ∈ Fam, μ (st ⁻¹' {D}) ≤
        ENNReal.ofReal ((binBox pv Vq).card : ℝ) ^ 3 * ∑ D ∈ Ωst, μ (st ⁻¹' {D}) := by
  obtain ⟨J, Ωst, hsub, hdet, hwit, hmass⟩ := exists_spanning_witness_triple_uniform μ st hst v hv
    Fam Q hQm hηq hps hqual hwv hpv hpvw hstrip hVq hvQ
  refine ⟨J, (liftMatrix J)⁻¹, Ωst, hsub, ?_, ?_, hmass⟩
  · rintro ⟨D, hD⟩
    have hJ : ∀ i k, |J i k| ≤ max 1 (Vq + pv) := by
      intro i k
      obtain ⟨w, hwQ, -, hwv⟩ := hwit D hD i
      have h1 := hwv k
      have h2 := hvQ w hwQ k
      have : |J i k| ≤ Vq + pv := by
        calc |J i k| ≤ |v w.1 k| + |v w.1 k - J i k| := by
              have := abs_sub_abs_le_abs_sub (J i k) (v w.1 k)
              rw [abs_sub_comm (J i k)] at this
              linarith
          _ ≤ Vq + pv / 2 := add_le_add h2 h1
          _ ≤ Vq + pv := by linarith
      exact this.trans (le_max_right _ _)
    obtain ⟨hinv, hbound⟩ := liftMatrix_inverse_bound J (le_max_left 1 (Vq + pv)) hJ
      (by positivity) (hdet ⟨D, hD⟩)
    exact ⟨hinv, hJ, hbound⟩
  · intro D hD axis
    obtain ⟨w, hwQ, hst', hwv'⟩ := hwit D hD axis
    obtain ⟨hE, ht0, ht1, hqw⟩ := hQ w hwQ
    exact ⟨w, hE, hst', hwv', ht0, ht1, hqw⟩

/-- **The Cartesian witness frame, per velocity code.** Only the qualified
velocity CODES at mesh `pv` of each state are dominated by one probability
`π` on codes; no domination inside a code is assumed. -/
theorem cartesian_witness_frame_bins {Λ σ : Type} [MeasurableSpace Λ] [MeasurableSpace σ]
    [MeasurableSingletonClass σ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ] (st : Λ × ℝ → σ) (hst : Measurable st)
    (v : Λ → Fin 2 → ℝ) (hv : Measurable v)
    (Fam : Finset σ) (Q : Set (Λ × ℝ)) (hQm : MeasurableSet Q)
    (Eref : Set (Λ × ℝ)) (Gs : σ → Fin 3 → ℝ) (t0 h : ℝ) (M : ℕ) (K err : ℝ)
    (hQ : ∀ w ∈ Q, w ∈ Eref ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
      QualWitness Eref st Gs t0 h M K err (1 / K) w)
    {Vq : ℝ} (hvQ : ∀ w ∈ Q, ∀ k, |v w.1 k| ≤ Vq)
    {ηq ps : ℝ} (hηq : 0 ≤ ηq) (hps : 0 ≤ ps)
    (hqual : ∀ D ∈ Fam, μ (st ⁻¹' {D} \ Q) ≤ ENNReal.ofReal ηq * μ (st ⁻¹' {D}))
    {wv pv : ℝ} (hwv : 0 < wv) (hpv : 0 < pv) (hpvw : pv ≤ wv / 2)
    (hstrip : ∀ D ∈ Fam, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ s : ℝ,
      μ (st ⁻¹' {D} ∩ {x | |⟪n, (WithLp.toLp 2 (v x.1) : EuclideanSpace ℝ (Fin 2))⟫ - s| ≤ wv}) ≤
        ENNReal.ofReal ps * μ (st ⁻¹' {D}))
    (π : Measure (Fin 2 → ℤ)) [IsProbabilityMeasure π] {Kr : ℝ}
    (hdomBin : ∀ D ∈ Fam, ∀ b : Fin 2 → ℤ,
      μ ({x | velBinOf pv (v x.1) = b} ∩ (st ⁻¹' {D} ∩ Q)) ≤
        ENNReal.ofReal Kr * μ (st ⁻¹' {D}) * π {b}) :
    ∃ (J : Fin 3 → Fin 2 → ℝ) (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (Ωst : Finset σ), Ωst ⊆ Fam ∧
      (Ωst.Nonempty → liftMatrix J * Ainv = 1 ∧ (∀ i k, |J i k| ≤ max 1 (Vq + pv)) ∧
        ∀ i k, |Ainv i k| ≤ 2 * (max 1 (Vq + pv)) ^ 2 / (wv / 2) ^ 2) ∧
      (∀ D ∈ (Ωst : Set σ), ∀ axis : Fin 3, ∃ w ∈ Eref, st w = D ∧
        (∀ k, |v w.1 k - J axis k| ≤ pv / 2) ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
        QualWitness Eref st Gs t0 h M K err (1 / K) w) ∧
      ENNReal.ofReal ((1 - ηq) ^ 3 - 2 * ps) * ∑ D ∈ Fam, μ (st ⁻¹' {D}) ≤
        ENNReal.ofReal Kr ^ 3 * ∑ D ∈ Ωst, μ (st ⁻¹' {D}) := by
  obtain ⟨J, Ωst, hsub, hdet, hwit, hmass⟩ := exists_spanning_witness_triple_of_bins μ st hst v hv
    Fam Q hQm hηq hps hqual hwv hpv hpvw hstrip π hdomBin
  refine ⟨J, (liftMatrix J)⁻¹, Ωst, hsub, ?_, ?_, hmass⟩
  · rintro ⟨D, hD⟩
    have hJ : ∀ i k, |J i k| ≤ max 1 (Vq + pv) := by
      intro i k
      obtain ⟨w, hwQ, -, hwv⟩ := hwit D hD i
      have h1 := hwv k
      have h2 := hvQ w hwQ k
      have : |J i k| ≤ Vq + pv := by
        calc |J i k| ≤ |v w.1 k| + |v w.1 k - J i k| := by
              have := abs_sub_abs_le_abs_sub (J i k) (v w.1 k)
              rw [abs_sub_comm (J i k)] at this
              linarith
          _ ≤ Vq + pv / 2 := add_le_add h2 h1
          _ ≤ Vq + pv := by linarith
      exact this.trans (le_max_right _ _)
    obtain ⟨hinv, hbound⟩ := liftMatrix_inverse_bound J (le_max_left 1 (Vq + pv)) hJ
      (by positivity) (hdet ⟨D, hD⟩)
    exact ⟨hinv, hJ, hbound⟩
  · intro D hD axis
    obtain ⟨w, hwQ, hst', hwv'⟩ := hwit D hD axis
    obtain ⟨hE, ht0, ht1, hqw⟩ := hQ w hwQ
    exact ⟨w, hE, hst', hwv', ht0, ht1, hqw⟩

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
