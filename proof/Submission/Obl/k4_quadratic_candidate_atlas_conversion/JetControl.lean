import Submission.Obl.k4_quadratic_candidate_atlas_conversion.Certificates
import Submission.Obl.k4_algebraic_real_jet_comparison

namespace Submission.Obl.k4_quadratic_candidate_atlas_conversion

/-- The accepted comparison against the zero sheet gives the same-centre
finite-jet rule needed by the atlas constructor. -/
theorem algebraicJets_available : algebraicJets := by
  intro D hD
  obtain ⟨K, hK, V, hV, c, hc, B, hB, hcompare⟩ :=
    Submission.k4_algebraic_real_jet_comparison D
  refine ⟨K, hK, V, hV, c, hc, B, hB, ?_⟩
  intro f P hP hPD hf hroot hreal
  let Z : MvPolynomial (Fin 4) ℂ := MvPolynomial.X (3 : Fin 4)
  have hZ : Z ≠ 0 := by simp [Z]
  have hZD : Z.totalDegree ≤ D := by simpa [Z] using hD
  have hZroot : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (0 : ℂ)) Z = 0 := by
    intro z _
    simp [Z, Fin.snoc]
  obtain ⟨_, _, hupper, hlower⟩ := hcompare f (fun _ => 0) P Z hP hZ hPD hZD
    hf (differentiableOn_const (0 : ℂ)) hroot hZroot (fun x hx => ⟨hreal x hx, rfl⟩)
  constructor
  · intro A hA hbase v hv m _hm
    have hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 →
        ‖f (WithLp.toLp 2 (fun j => (x j : ℂ))) - 0‖ ≤ A := by
      simpa only [sub_zero] using hbase
    simpa only [sub_zero, zero_add] using
      hupper A hA hb v hv m 0 (by norm_num)
  · intro x hx
    simpa only [sub_zero, zero_add] using hlower 0 x (by norm_num) hx

end Submission.Obl.k4_quadratic_candidate_atlas_conversion
