-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ModelBase.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelGood

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter
open Submission.Lib.K4ContactNormalization

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem Valid.measurable_base (hp : p.Valid) (k : ℕ) : Measurable (p.base k) := by
  have hb : Measurable (fun u : α × ℝ => p.b k u.1) :=
    (hp.basic k).1.comp measurable_fst
  have hcoord (i : Fin 6) : Measurable (fun u : α × ℝ => p.b k u.1 i) :=
    (measurable_pi_apply i).comp hb
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · simpa [base] using (measurable_snd : Measurable (Prod.snd : α × ℝ → ℝ))
  · change Measurable (fun u : α × ℝ => p.b k u.1 0 + u.2 * p.b k u.1 3)
    exact (hcoord 0).add ((measurable_snd : Measurable (Prod.snd : α × ℝ → ℝ)).mul (hcoord 3))
  · change Measurable (fun u : α × ℝ => p.b k u.1 1 + u.2 * p.b k u.1 4)
    exact (hcoord 1).add ((measurable_snd : Measurable (Prod.snd : α × ℝ → ℝ)).mul (hcoord 4))

theorem GoodPoint.base_bounded (hp : p.Valid) {k : ℕ} {u : α × ℝ}
    (hu : p.GoodPoint k u) : ∀ i, |p.base k u i| ≤ 2 * p.K k := by
  have ht : |u.2| ≤ 1 := by rw [abs_of_nonneg hu.time.1]; exact hu.time.2
  have hsum := hu.coefficients
  have hZ : |p.b k u.1 0 + u.2 * p.b k u.1 3| ≤ p.K k := by
    calc
      _ ≤ |p.b k u.1 0| + |u.2| * |p.b k u.1 3| := by
        simpa only [abs_mul] using abs_add_le (p.b k u.1 0) (u.2 * p.b k u.1 3)
      _ ≤ |p.b k u.1 0| + |p.b k u.1 3| := by
        exact add_le_add le_rfl (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right ht (abs_nonneg (p.b k u.1 3)))
      _ ≤ p.K k := by linarith [abs_nonneg (p.b k u.1 1), abs_nonneg (p.b k u.1 4)]
  have hY : |p.b k u.1 1 + u.2 * p.b k u.1 4| ≤ p.K k := by
    calc
      _ ≤ |p.b k u.1 1| + |u.2| * |p.b k u.1 4| := by
        simpa only [abs_mul] using abs_add_le (p.b k u.1 1) (u.2 * p.b k u.1 4)
      _ ≤ |p.b k u.1 1| + |p.b k u.1 4| := by
        exact add_le_add le_rfl (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right ht (abs_nonneg (p.b k u.1 4)))
      _ ≤ p.K k := by linarith [abs_nonneg (p.b k u.1 0), abs_nonneg (p.b k u.1 3)]
  intro i
  fin_cases i <;> simp only [base, x, point, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
  · linarith [hp.K_ge k]
  · linarith [Valid.K_pos p hp k]
  · linarith [Valid.K_pos p hp k]

theorem Valid.μ_finite (hp : p.Valid) (k : ℕ) : IsFiniteMeasure (p.μ k) :=
  ⟨(Valid.μ_univ_le p hp k).trans_lt ENNReal.ofReal_lt_top⟩

/-- The original base marginal, before any selection or conditioning. -/
noncomputable def baseLaw (k : ℕ) : Measure (Fin 3 → ℝ) :=
  Measure.map (p.base k) (p.μ k)

theorem Valid.baseLaw_finite (hp : p.Valid) (k : ℕ) : IsFiniteMeasure (p.baseLaw k) := by
  have := Valid.μ_finite p hp k
  unfold baseLaw
  infer_instance

theorem Valid.baseLaw_mass (hp : p.Valid) (k : ℕ) :
    ENNReal.ofReal ((p.K k)⁻¹) ≤ p.baseLaw k univ := by
  rw [baseLaw, Measure.map_apply (Valid.measurable_base p hp k) MeasurableSet.univ,
    preimage_univ]
  exact ((hp.basic k).2.2.2.2.2.2.1).trans ((hp.basic k).2.2.2.2.1 _)

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Set MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

theorem measurable_floor_mesh (δ : ℝ) :
    Measurable (fun z : Fin 3 → ℝ => fun i : Fin 3 => ⌊z i / δ⌋) :=
  by
    apply measurable_pi_iff.mpr
    intro i
    exact ((measurable_pi_apply i : Measurable (fun z : Fin 3 → ℝ => z i)).div_const δ).floor

theorem Valid.baseLaw_cell (hp : p.Valid) (k : ℕ) (r : ℝ) (q : Fin 3 → ℤ) :
    p.baseLaw k {z | (fun i : Fin 3 => ⌊z i / (p.N k ^ (-r))⌋) = q} =
      p.μ k {u | p.z k r u = q} := by
  have hm : MeasurableSet {z : Fin 3 → ℝ |
      (fun i : Fin 3 => ⌊z i / (p.N k ^ (-r))⌋) = q} :=
    measurableSet_eq_fun (measurable_floor_mesh (p.N k ^ (-r))) measurable_const
  rw [baseLaw, Measure.map_apply (Valid.measurable_base p hp k) hm]
  rfl

theorem Valid.baseLaw_bounded (hp : p.Valid) (k : ℕ) :
    ∀ᵐ z ∂p.baseLaw k, ∀ i, |z i| ≤ 2 * p.K k := by
  have hset : MeasurableSet {z : Fin 3 → ℝ | ∀ i : Fin 3, |z i| ≤ 2 * p.K k} := by
    convert MeasurableSet.iInter (fun i : Fin 3 =>
      measurableSet_le (measurable_pi_apply i : Measurable (fun z : Fin 3 → ℝ => z i)).abs
        (measurable_const : Measurable (fun _ : Fin 3 → ℝ => 2 * p.K k))) using 1
    ext z
    simp
  apply (ae_map_iff (Valid.measurable_base p hp k).aemeasurable hset).mpr
  filter_upwards [Valid.ae_good p hp k] with u hu
  exact GoodPoint.base_bounded p hp hu

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
