import Submission.Obl.k4_pair_bin_atlas_assembly.PairData

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_quadratic_atlas_normalization

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev PairPoint := Trajectory × (ℝ × ℝ)

namespace PairData

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε)

def world (s : Fin p.m) : Fin Wk := p.γ (p.frame s)
def timeIndex (s : Fin p.m) : Fin (2 ^ p.T) := p.j (p.frame s)
def block (s : Fin p.m) : Set ℝ :=
  Icc ((p.timeIndex s : ℝ) / (2 : ℝ) ^ p.T)
    (((p.timeIndex s : ℝ) + 1) / (2 : ℝ) ^ p.T)

noncomputable def sourceBase (s : Fin p.m) (v : PairPoint) : EuclideanSpace ℝ (Fin 3) :=
  base p.T (p.timeIndex s : ℝ) p.κ (p.c (p.frame s)) (p.u (p.frame s))
    (p.Q (p.frame s)) v.1 v.2.1

noncomputable def baseLine (s : Fin p.m) (l : Trajectory) (t : ℝ) :
    EuclideanSpace ℝ (Fin 3) :=
  base p.T (p.timeIndex s : ℝ) p.κ (p.c (p.frame s)) (p.u (p.frame s))
    (p.Q (p.frame s)) l t

noncomputable def hiddenLine (s : Fin p.m) (l : Trajectory) (t : ℝ) : ℝ :=
  Bk (p.world s) * (x l t) 3

noncomputable def sourceList (s : Fin p.m) (v : PairPoint) : Finset (Fin p.m) :=
  p.lst (p.world s) (obs (Bk (p.world s)) (δ Nk L) (v.1, v.2.2))

noncomputable def pairLaw (s : Fin p.m) : Measure PairPoint :=
  (νk (p.world s)).prod (volume.prod volume)

noncomputable def incidenceLaw (s : Fin p.m) : Measure Incidence :=
  (νk (p.world s)).prod volume

theorem measurable_sourceBase (s : Fin p.m) : Measurable (p.sourceBase s) := by
  unfold sourceBase base y x
  fun_prop

theorem measurable_sourceList_membership (s s' : Fin p.m) :
    MeasurableSet {v | s' ∈ p.sourceList s v} :=
  (p.list_format (p.world s) s').1.preimage
    (show Measurable (fun v : PairPoint => (v.1, v.2.2)) by fun_prop)

theorem sourceList_size (s : Fin p.m) (v : PairPoint) :
    ((p.sourceList s v).card : ℝ) ≤ p.κ := p.list_size _ _

theorem source_mem (s : Fin p.m) {v : PairPoint} (hv : v ∈ p.H s) :
    (v.1, v.2.1) ∈ p.S s := ((p.pairs s).2 v hv).1

theorem source_time (s : Fin p.m) {v : PairPoint} (hv : v ∈ p.H s) :
    v.2.1 ∈ p.block s :=
  ((p.sources s).2.2 (v.1, v.2.1) (p.source_mem s hv)).2.2.2.1

theorem target_time (s : Fin p.m) {v : PairPoint} (hv : v ∈ p.H s) :
    v.2.2 ∈ p.block s := ((p.pairs s).2 v hv).2.1

theorem sourceBase_norm (s : Fin p.m) {v : PairPoint} (hv : v ∈ p.H s) :
    ‖p.sourceBase s v‖ ≤ 1 / 8 :=
  (((p.sources s).2.2 (v.1, v.2.1) (p.source_mem s hv)).2.2.2.2
    v.2.1 (p.source_time s hv)).2.2.1

theorem source_discriminant (s : Fin p.m) {v : PairPoint} (hv : v ∈ p.H s) :
    Nk ^ (-a) ≤ |MvPolynomial.eval (fun n => p.sourceBase s v n) (disc (p.P s))| := by
  obtain ⟨_, _, _, s', _, _, hlocal⟩ := (p.pairs s).2 v hv
  exact hlocal.1

theorem baseLine_lipschitz (s : Fin p.m) {v : PairPoint} (hv : v ∈ p.H s) :
    ∀ t ∈ p.block s, ‖p.baseLine s v.1 t - p.sourceBase s v‖ ≤
      (2 : ℝ) ^ p.T * |t - v.2.1| := by
  intro t ht
  exact (((p.sources s).2.2 (v.1, v.2.1) (p.source_mem s hv)).2.2.2.2 t ht).2.2.2
    v.2.1 (p.source_time s hv)

theorem localPair_witness (s : Fin p.m) {v : PairPoint} (hv : v ∈ p.H s) :
    ∃ s' ∈ p.sourceList s v, p.frame s' = p.frame s ∧
      localPair Nk a (δ Nk L) ((2 : ℝ) ^ p.T) (p.P s) (p.P s') (p.sourceBase s v)
        (p.baseLine s v.1) (p.hiddenLine s v.1) v.2.1 (p.block s) :=
  ((p.pairs s).2 v hv).2.2.2

theorem pairLaw_finite (hν : ∀ w, IsProbabilityMeasure (νk w)) (s : Fin p.m) :
    p.pairLaw s (p.H s) ≠ ∞ := by
  letI := hν (p.world s)
  have hvol : volume (p.block s) ≠ ∞ := by
    rw [block, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hsub : p.H s ⊆ univ ×ˢ (p.block s ×ˢ p.block s) := by
    intro v hv
    exact ⟨mem_univ _, p.source_time s hv, p.target_time s hv⟩
  apply ne_of_lt
  calc
    _ ≤ p.pairLaw s (univ ×ˢ (p.block s ×ˢ p.block s)) := measure_mono hsub
    _ = volume (p.block s) * volume (p.block s) := by
      simp only [pairLaw, Measure.prod_prod, measure_univ, one_mul]
    _ < ∞ := ENNReal.mul_lt_top hvol.lt_top hvol.lt_top

end PairData
end Submission.Obl.k4_pair_bin_atlas_assembly
