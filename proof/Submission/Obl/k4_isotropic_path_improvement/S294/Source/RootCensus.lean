-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The two uses of the ancestor census (session x1088, for x1082's root stage).

x1065's `BroadMultiscaleCoreSource.exists_multiscale_ancestor_census_source` gives, on a
`current` set, the occupancy of the codes of `(unshearedPacketBase p child, R_root/δ_child)` for
every child of the root, with shape `Kc^100 base ≤ ((δ_child/δ_root)/(2^T_root/2^T_child)) hidden`.

* `root_census_of_child_eq_root`: at `child = root` the shape factor is `1`, which is the form of
  the MK4 rows' census (`ancestor_velocity_rows`, x1082's `root_slice_full`).
* `child_hocc_of_census`: at a deeper child `b` it is the `hocc` premise of
  `Source.ChildCaps.childCapClauses` (relative shape `a'/h'`, the literal `packetBase` and
  `packetSignal (R a) / δ(N, r_b)`). -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ChildCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open Submission.Lib.K4ParentSignalPreparation.Census

noncomputable section

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}

/-- **The root census in the MK4 form**: at `child = root` the census shape factor is `1`. -/
theorem root_census_of_child_eq_root (a : Fin p.C) (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    {fineMesh Kcensus dimension : ℝ}
    (hcen : ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
      Kcensus ^ (100 : ℕ) * base ≤
        ((ParentSource.δ (d.N k) (p.r (p.lev a)) / ParentSource.δ (d.N k) (p.r (p.lev a))) /
          ((2 : ℝ) ^ p.T (p.lev a) / (2 : ℝ) ^ p.T (p.lev a))) * hidden →
      (occupied S (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) base hidden).Finite ∧
      ((occupied S (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) base hidden).ncard : ℝ) ≤
        Kcensus / (base ^ 3 * hidden ^ dimension)) :
    ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
      Kcensus ^ (100 : ℕ) * base ≤ 1 * hidden →
      (occupied S (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) base hidden).Finite ∧
      ((occupied S (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) base hidden).ncard : ℝ) ≤
        Kcensus / (base ^ 3 * hidden ^ dimension) := by
  intro base hidden h1 h2 h3 h4 hshape
  have hδ : ParentSource.δ (d.N k) (p.r (p.lev a)) ≠ 0 := (O204.Tangent.δ_pos _ _).ne'
  have h2T : (2 : ℝ) ^ p.T (p.lev a) ≠ 0 := by positivity
  apply hcen base hidden h1 h2 h3 h4
  rw [div_self hδ, div_self h2T, div_one]
  exact hshape

/-- **The child census as `childCapClauses`' `hocc`.** -/
theorem child_hocc_of_census (a b : Fin p.C) (hT : p.T (p.lev a) ≤ p.T (p.lev b))
    (S : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) {fineMesh Kcensus dimension : ℝ}
    (hcen : ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
      Kcensus ^ (100 : ℕ) * base ≤
        ((ParentSource.δ (d.N k) (p.r (p.lev b)) / ParentSource.δ (d.N k) (p.r (p.lev a))) /
          ((2 : ℝ) ^ p.T (p.lev a) / (2 : ℝ) ^ p.T (p.lev b))) * hidden →
      (occupied S (fun z j => unshearedPacketBase p b z j)
        (physicalParentSignal (d.N k) p b (p.R a)) base hidden).Finite ∧
      ((occupied S (fun z j => unshearedPacketBase p b z j)
        (physicalParentSignal (d.N k) p b (p.R a)) base hidden).ncard : ℝ) ≤
        Kcensus / (base ^ 3 * hidden ^ dimension)) :
    ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
      Kcensus ^ (100 : ℕ) * base ≤
        (aRelOf (d.N k) (p.r (p.lev a)) (p.r (p.lev b)) /
          hRelOf (p.T (p.lev a)) (p.T (p.lev b))) * hidden →
      (occupied S
        (fun z j => O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z j)
        (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)))
        base hidden).Finite ∧
      ((occupied S
        (fun z j => O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z j)
        (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b)))
        base hidden).ncard : ℝ) ≤ Kcensus / (base ^ 3 * hidden ^ dimension) := by
  intro base hidden h1 h2 h3 h4 hshape
  -- the two signals agree
  have hsig : (fun z => O204.Tangent.packetSignal (p.R a) z / O204.Split.δ (d.N k) (p.r (p.lev b))) =
      physicalParentSignal (d.N k) p b (p.R a) := by
    funext z
    change _ = (O204.Split.δ (d.N k) (p.r (p.lev b)))⁻¹ * _
    rw [div_eq_inv_mul]
    rfl
  have hbase : (fun z j => O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b) z j) =
      (fun z j => unshearedPacketBase p b z j) := rfl
  -- the two shapes agree
  have hshape' : Kcensus ^ (100 : ℕ) * base ≤
      ((ParentSource.δ (d.N k) (p.r (p.lev b)) / ParentSource.δ (d.N k) (p.r (p.lev a))) /
        ((2 : ℝ) ^ p.T (p.lev a) / (2 : ℝ) ^ p.T (p.lev b))) * hidden := by
    have e : hRelOf (p.T (p.lev a)) (p.T (p.lev b)) =
        (2 : ℝ) ^ p.T (p.lev a) / (2 : ℝ) ^ p.T (p.lev b) := by
      unfold hRelOf
      rw [pow_sub₀ (2 : ℝ) (by norm_num) hT]
      field_simp
    have e' : aRelOf (d.N k) (p.r (p.lev a)) (p.r (p.lev b)) =
        ParentSource.δ (d.N k) (p.r (p.lev b)) / ParentSource.δ (d.N k) (p.r (p.lev a)) := rfl
    rw [← e, ← e']
    exact hshape
  rw [hsig, hbase]
  exact hcen base hidden h1 h2 h3 h4 hshape'

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
