import Submission.Obl.k4_scalar_capped_heavy_potential.BoundedBase
import Submission.Obl.k4_scalar_capped_heavy_potential.HeavyPacket
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Geometry

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Set MeasureTheory

noncomputable section

def scalarPhysical (p : (ℕ × (Fin 5 → ℝ)) × ℝ) : Fin 3 → ℝ :=
  ![p.2, Cons.yL p.1 p.2, Cons.xL p.1 p.2]

theorem measurable_scalarPhysical : Measurable scalarPhysical := by
  unfold scalarPhysical Cons.yL Cons.xL
  fun_prop

theorem scalarPhysical_time (p : (ℕ × (Fin 5 → ℝ)) × ℝ) :
    scalarPhysical p 0 = p.2 := rfl

theorem scalarPhysical_hidden (p : (ℕ × (Fin 5 → ℝ)) × ℝ) :
    scalarPhysical p 2 = Cons.xL p.1 p.2 := rfl

theorem scalarPhysical_base (p : (ℕ × (Fin 5 → ℝ)) × ℝ) (i : Fin 2) :
    scalarPhysical p i.castSucc = (![p.2, Cons.yL p.1 p.2] : Fin 2 → ℝ) i := by
  fin_cases i <;> rfl

theorem normalized_scalarPhysical (h : ℝ) (z : Fin 2 → ℝ)
    (p : (ℕ × (Fin 5 → ℝ)) × ℝ) :
    normalizedPhysicalBase h z scalarPhysical p = Cons.ubase z h p.1 p.2 := by
  ext i
  fin_cases i <;> rfl

theorem scalarPhysical_code (b : ℝ) :
    finePhysicalCode b scalarPhysical = Cons.physState b := rfl

theorem measurable_scalar_joint_code (h ξ w : ℝ) (z : Fin 2 → ℝ) :
    Measurable (jointPhysicalCode h ξ w z scalarPhysical) := by
  have hp := measurable_scalarPhysical
  unfold jointPhysicalCode normalizedPhysicalBase
  fun_prop

theorem scalar_joint_code_fiber (h ξ w : ℝ) (z : Fin 2 → ℝ)
    (q : (Fin 2 → ℤ) × ℤ) :
    jointPhysicalCode h ξ w z scalarPhysical ⁻¹' {q} =
      {p | (fun i => (⌊Cons.ubase z h p.1 p.2 i / ξ⌋ : ℤ)) = q.1 ∧
        (⌊Cons.xL p.1 p.2 / w⌋ : ℤ) = q.2} := by
  ext p
  simp only [mem_preimage, mem_singleton_iff, jointPhysicalCode,
    normalized_scalarPhysical, scalarPhysical_hidden, Prod.ext_iff, mem_ofPred_eq]

theorem scalar_base_affine (h : ℝ) (z : Fin 2 → ℝ) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    Cons.ubase z h l t = ![(t - z 0) / h,
      (Cons.yL l (z 0) - z 1) / h + ((t - z 0) / h) * l.2 1] := by
  ext i
  fin_cases i
  · rfl
  · change (Cons.yL l t - z 1) / h =
      (Cons.yL l (z 0) - z 1) / h + ((t - z 0) / h) * l.2 1
    unfold Cons.yL
    ring

/-- The actual scalar packet has a bounded measurable affine frame on
a measurable set carrying its original incidence law. Only the coordinate
maps are extended; the original prior is kept unchanged. -/
theorem scalar_bounded_frame
    (ν : Measure (ℕ × (Fin 5 → ℝ)))
    (μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (K : ENNReal)
    (hdom : μ ≤ K • ν.prod volume) {H h : ℝ} (hH : 0 ≤ H)
    (z : Fin 2 → ℝ) (I : Set ℝ) (ht₀ : z 0 ∈ I)
    (hcoeff : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ H)
    (hbox : ∀ᵐ p ∂μ, ∀ t ∈ I, ∀ e, |Cons.ubase z h p.1 t e| ≤ H) :
    ∃ (Λ : Set (ℕ × (Fin 5 → ℝ))) (u v : (ℕ × (Fin 5 → ℝ)) → ℝ),
      MeasurableSet Λ ∧ (∀ᵐ p ∂μ, p.1 ∈ Λ) ∧
      Measurable u ∧ Measurable v ∧ (∀ l, |u l| ≤ H) ∧ (∀ l, |v l| ≤ H) ∧
      (∀ p, p.1 ∈ Λ → normalizedPhysicalBase h z scalarPhysical p =
        ![(p.2 - z 0) / h, u p.1 + ((p.2 - z 0) / h) * v p.1]) ∧
      (∀ᵐ p ∂μ, v p.1 = p.1.2 1) := by
  let u₀ : (ℕ × (Fin 5 → ℝ)) → ℝ := fun l => (Cons.yL l (z 0) - z 1) / h
  let v₀ : (ℕ × (Fin 5 → ℝ)) → ℝ := fun l => l.2 1
  have hu₀ : Measurable u₀ := by dsimp [u₀, Cons.yL]; fun_prop
  have hv₀ : Measurable v₀ := by dsimp [v₀]; fun_prop
  have hcoeffμ := line_property_of_product_domination ν μ K hdom _ hcoeff
  have hbound : ∀ᵐ p ∂μ, |u₀ p.1| ≤ H ∧ |v₀ p.1| ≤ H := by
    filter_upwards [hbox, hcoeffμ] with p hp hc
    refine ⟨?_, hc 1⟩
    simpa only [u₀, Cons.ubase_one] using hp (z 0) ht₀ 1
  obtain ⟨Λ, u, v, hΛ, hΛμ, hu, hv, hbu, hbV, heq⟩ :=
    bounded_base_extension μ u₀ v₀ hu₀ hv₀ hH hbound
  refine ⟨Λ, u, v, hΛ, hΛμ, hu, hv, hbu, hbV, ?_, ?_⟩
  · intro p hp
    rw [normalized_scalarPhysical, scalar_base_affine]
    rw [(heq p.1 hp).1, (heq p.1 hp).2]
  · filter_upwards [hΛμ] with p hp
    exact (heq p.1 hp).2

end
end Submission.Obl.k4_scalar_capped_heavy_potential
