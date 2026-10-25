import Submission.Obl.k4_finite_positive_mixed_cover_realization.Cover

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_forest_width_selection

/-- The analytical witnesses with the two old time endpoints removed. -/
def CoverData.interior {W : ℕ} {p : PathData W} (c : CoverData p) (b : Fin c.n) :
    Set Incidence :=
  c.counted b ∩ {z | z.2 ∈ Ioo ((p.bin (c.old b) : ℝ) / (2 : ℝ) ^ p.T c.level)
    (((p.bin (c.old b) : ℝ) + 1) / (2 : ℝ) ^ p.T c.level)}

section
variable {W m Mg Dg : ℕ} {p : PathData W} {c : CoverData p} {Nk L d₁ ρ gain ε : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory} {B : Fin W → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε)

include hc

lemma CoverData.Valid.old_level (b : Fin c.n) : p.lev (c.old b) = c.level :=
  (hc.2.2.2.2.2.2.1 b).1

lemma CoverData.Valid.assigned_measurable (b : Fin c.n) : MeasurableSet (c.assigned b) :=
  (hc.2.2.2.2.2.2.1 b).2.2.1

lemma CoverData.Valid.assigned_subset (b : Fin c.n) : c.assigned b ⊆ p.assigned (c.old b) :=
  (hc.2.2.2.2.2.2.1 b).2.2.2.1

lemma CoverData.Valid.assigned_format (b : Fin c.n) (q : ℕ) :
    gfmt 6 (Nk ^ Mg) Dg {w | (q, w) ∈ c.assigned b} :=
  (hc.2.2.2.2.2.2.1 b).2.2.2.2.1 q

lemma CoverData.Valid.counted_measurable (b : Fin c.n) : MeasurableSet (c.counted b) :=
  (hc.2.2.2.2.2.2.1 b).2.2.2.2.2.1

lemma CoverData.Valid.counted_support (b : Fin c.n) {z : Incidence} (hz : z ∈ c.counted b) :
    z ∈ TerminalInc W p.C m p.lev p.world p.counted (p.world (c.old b)) ∧
    z.1 ∈ c.assigned b ∧ z.2 ∈ Icc
      ((p.bin (c.old b) : ℝ) / (2 : ℝ) ^ p.T c.level)
      (((p.bin (c.old b) : ℝ) + 1) / (2 : ℝ) ^ p.T c.level) :=
  (hc.2.2.2.2.2.2.1 b).2.2.2.2.2.2.1 hz

lemma CoverData.Valid.assignments_disjoint (b b' : Fin c.n) (hne : b ≠ b')
    (hparent : c.old b = c.old b') : Disjoint (c.assigned b) (c.assigned b') :=
  hc.2.2.2.2.2.2.2.1 b b' hne hparent

lemma CoverData.Valid.interior_measurable (b : Fin c.n) : MeasurableSet (c.interior b) :=
  (hc.counted_measurable b).inter (measurable_snd measurableSet_Ioo)

/-- Endpoint removal costs no mass in any original world. -/
lemma CoverData.Valid.interior_mass (b : Fin c.n) :
    ((ν (p.world (c.old b))).prod volume) (c.interior b) =
      ((ν (p.world (c.old b))).prod volume) (c.counted b) :=
  k4_fixed_menu_density_pruning.measure_trim_to_interior _ _ _ _
    (fun z hz => (hc.counted_support b hz).2.2)

/-- Every retained candidate incidence belongs to a deeper actual label
whose actual old ancestor is the candidate's old parent. -/
lemma CoverData.Valid.interior_deep_coverage
    {Mp Dp : ℕ} {ℓ κ₁ δ₀ σ : ℝ} {E : Fin W → Set Incidence}
    {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    {j : ℕ} (hij : c.level ≤ j) (hjm : j < m)
    (b : Fin c.n) {z : Incidence} (hz : z ∈ c.interior b) :
    ∃ d : Fin p.C, p.lev d = j ∧ p.world d = p.world (c.old b) ∧
      z ∈ p.counted d ∧ forestAncestor p.lev p.par d c.level = c.old b := by
  obtain ⟨t, ht, htw, hzt⟩ := (hc.counted_support b hz.1).1
  have hjt : j ≤ p.lev t := by omega
  let d := forestAncestor p.lev p.par t j
  obtain ⟨hd, hdw, hdsub⟩ := hp.ancestor t j hjt
  have hzd : z ∈ p.counted d := hdsub hzt
  refine ⟨d, hd, hdw.trans htw, hzd, ?_⟩
  have hparent := hp.ancestor_eq_of_interior (old := c.old b)
    (show p.lev (c.old b) ≤ p.lev d by rw [hc.old_level b, hd]; exact hij)
    (hdw.trans htw) hzd (hc.assigned_subset b (hc.counted_support b hz.1).2.1)
    (by
      have hzi : z.2 ∈ Ioo ((p.bin (c.old b) : ℝ) / (2 : ℝ) ^ p.T c.level)
        (((p.bin (c.old b) : ℝ) + 1) / (2 : ℝ) ^ p.T c.level) := hz.2
      simpa only [hc.old_level b] using hzi)
  simpa only [hc.old_level b] using hparent

/-- Every candidate incidence in the old block interior is already counted
by that actual old chart. -/
lemma CoverData.Valid.interior_subset_old
    {Mp Dp : ℕ} {ℓ κ₁ δ₀ σ : ℝ} {E : Fin W → Set Incidence}
    {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (b : Fin c.n) :
    c.interior b ⊆ p.counted (c.old b) := by
  intro z hz
  obtain ⟨d, hd, -, hzd, ha⟩ := hc.interior_deep_coverage hp le_rfl hc.1 b hz
  have hself : forestAncestor p.lev p.par d c.level = d := by
    simpa only [hd] using forestAncestor_self p.lev p.par d
  have heq : d = c.old b := hself.symm.trans ha
  simpa only [heq] using hzd

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
