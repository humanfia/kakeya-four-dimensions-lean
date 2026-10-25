/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/TiltedComparison.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
/- Adapted from this LOT tree, obligation o202, session x0698, commit
   af82e6f9c71df56ed963f4a992dea84d0d6d83b5, file
   Submission/Obl/k4_horizontal_subcritical_rate_candidates/TiltedComparison.lean.
   This generic kernel uses original finite cell caps and witness mass only. -/
import Submission.Lib.K4AffineMesh
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.MeshNormalization
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.CoarseMeshCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- A comparison of two affine fits on an event with original mass extends to
its entire tilted box. All density information is a finite native mesh ceiling. -/
lemma tilted_affine_comparison {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (z : Ω → Fin 3 → ℝ) (f : Ω → ℝ)
    (g g' : Fin 3 → ℝ) (c c' t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ η a K M δ m : ℝ)
    {H : ℕ} (hH : 0 < H) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hη : 0 < η) (ha : 0 < a) (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hm : 0 < m)
    (hmass : ENNReal.ofReal m ≤ μ E)
    (hg₀ : η ≤ 2 * r₀ / H) (hg₁ : (|l₁| + 1) * η ≤ 2 * r₁ / H)
    (hg₂ : (|l₂| + |l₃| + 1) * η ≤ 2 * r₂ / H)
    (hresolve : η * ∑ j, |g j| ≤ a)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {ω | (fun i => ⌊z ω i / η⌋) = q ∧ ⌊f ω / a⌋ = j} ≤ ENNReal.ofReal (M * η ^ 3))
    (hbox : ∀ ω ∈ E, |z ω 0 - t₀| ≤ r₀ ∧
      |z ω 1 - z₀ - l₁ * (z ω 0 - t₀)| ≤ r₁ ∧
      |z ω 2 - y₀ - l₂ * (z ω 0 - t₀) - l₃ * (z ω 1 - z₀)| ≤ r₂)
    (hfit : ∀ ω ∈ E, |f ω - (c + ∑ j, g j * z ω j)| ≤ K * a)
    (hcomparison : ∀ ω ∈ E, |c' + ∑ j, g' j * z ω j| ≤ δ)
    (hfine : 30 * (512 * (2 * K + 7) * M * r₀ * r₁ * r₂) ≤ m * H)
    (z' : Fin 3 → ℝ)
    (hz' : |z' 0 - t₀| ≤ r₀ ∧
      |z' 1 - z₀ - l₁ * (z' 0 - t₀)| ≤ r₁ ∧
      |z' 2 - y₀ - l₂ * (z' 0 - t₀) - l₃ * (z' 1 - z₀)| ≤ r₂) :
    |c' + ∑ j, g' j * z' j| ≤
      δ + 48 * (512 * (2 * K + 7) * M * r₀ * r₁ * r₂) * δ / m := by
  let u := fun ω => triangularCoordinates t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ (z ω)
  let tag : Ω → Fin 3 → Fin H := fun ω j => unitGridTag H hH (u ω j)
  let C := 512 * (2 * K + 7) * M * r₀ * r₁ * r₂
  let L := triangularAffineCoefficients t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ c' g'
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hu (ω : Ω) (hω : ω ∈ E) (j : Fin 3) : u ω j ∈ Icc (0 : ℝ) 1 :=
    triangularCoordinates_mem_unit hr₀ hr₁ hr₂ (z ω) (hbox ω hω) j
  have hround (ω : Ω) (hω : ω ∈ E) (j : Fin 3) :
      |(tag ω j : ℕ) - (H : ℝ) * u ω j| ≤ 1 := unitGridTag_round hH (hu ω hω j)
  have hc (p : Fin 3 → Fin H) :
      μ {ω | ω ∈ E ∧ tag ω = p} ≤ ENNReal.ofReal (C / (H : ℝ) ^ 3) :=
    normalized_cell_affine_cap μ z f g c t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ η a K M
      hH hr₀ hr₁ hr₂ hη ha hK hM hg₀ hg₁ hg₂ hresolve hcap tag hround hfit p
  have hpoint (v : Fin 3 → ℝ) : c' + ∑ j, g' j * v j =
      L 0 + ∑ j, L j.succ * triangularCoordinates t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ v j :=
    triangular_affine_identity t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ c' g' v hr₀.ne' hr₁.ne' hr₂.ne'
  have hfu (ω : Ω) (hω : ω ∈ E) : |L 0 + ∑ j, L j.succ * u ω j| ≤ δ := by
    change |L 0 + ∑ j, L j.succ * triangularCoordinates _ _ _ _ _ _ _ _ _ (z ω) j| ≤ δ
    rw [← hpoint]
    exact hcomparison ω hω
  have huz := triangularCoordinates_mem_unit hr₀ hr₁ hr₂ z' hz'
  have huabs (ω : Ω) (hω : ω ∈ E) (j : Fin 3) : |u ω j| ≤ 1 := by
    rw [abs_of_nonneg (hu ω hω j).1]
    exact (hu ω hω j).2
  have hzabs (j : Fin 3) :
      |triangularCoordinates t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ z' j| ≤ 1 := by
    rw [abs_of_nonneg (huz j).1]
    exact (huz j).2
  have hb := Submission.Lib.K4AffineMesh.affine_box_bound_from_event μ hH E tag u
    (fun j => L j.succ) hδ hC hm hmass hc hfine huabs hround hfu
    (triangularCoordinates t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ z') hzabs
  rw [← hpoint] at hb
  exact hb

end Submission.Obl.k4_horizontal_strict_parameter_step
