import Submission.Obl.k4_general_parent_wide_layer_candidates.ProjectedSlicing
import Submission.Obl.k4_general_parent_wide_layer_candidates.NormalizedSourceCaps

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set

noncomputable section

def domainTime (h : ℝ) (d : ℤ × ℤ × ℤ) : ℝ := (d.1 : ℝ) * h

def domainVelocity (g : ℝ) (d : ℤ × ℤ × ℤ) : ℝ := (d.2.1 : ℝ) * g

def domainIntercept (h g b : ℝ) (d : ℤ × ℤ × ℤ) : ℝ :=
  (d.2.2 : ℝ) * b - domainTime h d * domainVelocity g d

/-- Normalized coordinates determined by the actual original domain code.
They do not depend on any later projected-label selector. -/
def domainCoordinates (h g b : ℝ) (a w t : ℝ) : Fin 2 → ℝ :=
  let d := movingDomainCode h g b a w t
  ![(t - domainTime h d) / (32 * h),
    (a + t * w - domainIntercept h g b d - t * domainVelocity g d) / (32 * b)]

theorem domainCoordinates_inner {h g b : ℝ} (hh : 0 < h) (hg : 0 < g) (hb : 0 < b)
    (hmove : h * g ≤ b) (a w t : ℝ) : ∀ i, |domainCoordinates h g b a w t i| ≤ 1 / 8 := by
  obtain ⟨ht, hy⟩ := moving_domain_geometry hh hg hb a w t
  let d := movingDomainCode h g b a w t
  have hty : |a + t * w - domainIntercept h g b d - t * domainVelocity g d| ≤ b + h * g := by
    convert hy using 1 <;> dsimp [d, domainIntercept, domainTime, domainVelocity] <;> congr 1 <;> ring
  intro i
  fin_cases i
  · change |(t - domainTime h d) / (32 * h)| ≤ 1 / 8
    rw [abs_div, abs_of_pos (by positivity : 0 < 32 * h), div_le_iff₀ (by positivity : 0 < 32 * h)]
    change |t - (d.1 : ℝ) * h| ≤ _
    change |t - (d.1 : ℝ) * h| ≤ h at ht
    linarith
  · change |(a + t * w - domainIntercept h g b d - t * domainVelocity g d) / (32 * b)| ≤ 1 / 8
    rw [abs_div, abs_of_pos (by positivity : 0 < 32 * b), div_le_iff₀ (by positivity : 0 < 32 * b)]
    linarith

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

def normalizedDomainBase (k : ℕ) (h g b : ℝ) (ω : α × ℝ) : Fin 2 → ℝ :=
  domainCoordinates h g b (p.b k ω.1 1) (p.b k ω.1 4) ω.2

theorem measurable_normalizedDomainBase (hbase : p.Basic) (k : ℕ) (h g b : ℝ) :
    Measurable (p.normalizedDomainBase k h g b) := by
  have hb := (hbase k).1
  unfold normalizedDomainBase domainCoordinates domainIntercept domainTime domainVelocity movingDomainCode
  fun_prop

theorem normalizedDomainBase_inner {k : ℕ} {h g b : ℝ}
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g ≤ b)
    (ω : α × ℝ) : ∀ i, |p.normalizedDomainBase k h g b ω i| ≤ 1 / 8 :=
  domainCoordinates_inner hh hg hb hmove _ _ _

/-- On a stored domain the actual normalized base is exactly the affine
chart used to pull that domain's projected polynomial into matching. -/
theorem normalizedDomainBase_on_code {k : ℕ} {h g b : ℝ} {ω : α × ℝ}
    {d : ℤ × ℤ × ℤ} (hcode : p.domainCode k h g b ω = d) :
    p.normalizedDomainBase k h g b ω =
      projectedDomainCoordinates (domainTime h d) (32 * h)
        (domainIntercept h g b d) (domainVelocity g d) (32 * b)
        ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] := by
  change movingDomainCode h g b (p.b k ω.1 1) (p.b k ω.1 4) ω.2 = d at hcode
  ext i
  fin_cases i <;> dsimp [normalizedDomainBase, domainCoordinates, projectedDomainCoordinates]
  · rw [hcode]
  · rw [hcode]
    rfl

end Parent
end
end Submission.Obl.k4_general_parent_wide_layer_candidates
