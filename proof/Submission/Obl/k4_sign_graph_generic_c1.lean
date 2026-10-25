import Mathlib
import ChallengeDeps
import Submission.Obl.k4_sign_graph_generic_c1.AnalyticCover
import Submission.Obl.k4_sign_graph_generic_c1.GraphCoordinates
set_option linter.unusedVariables false

/-!
# `Submission.k4_sign_graph_generic_c1`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_sign_graph_generic_c1`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_sign_graph_generic_c1/`
belong to this obligation.
-/

theorem Submission.k4_sign_graph_generic_c1 : ∀ (m : ℕ) (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ) (B : Set (Fin m → SignType)) (Sigma : Set (EuclideanSpace ℝ (Fin 3))) (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)), (∀ s y : EuclideanSpace ℝ (Fin 3), (fun i => SignType.sign (MvPolynomial.eval (Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => y k)) (p i))) ∈ B ↔ s ∈ Sigma ∧ b s = y) → ∃ S : Set (EuclideanSpace ℝ (Fin 3)), IsOpen S ∧ ContDiffOn ℝ 1 b S ∧ S ⊆ Sigma ∧ MeasureTheory.volume (Sigma \ S) = 0 := by
  classical
  intro m p B Sigma b hgraph
  let f : Fin m → (Fin 6 → ℝ) → ℝ := fun i x =>
    MvPolynomial.eval (fun j => x (Submission.Obl.k4_sign_graph_generic_c1.graphIndex j)) (p i)
  obtain ⟨C, hC, hcover⟩ :=
    Submission.Obl.k4_sign_graph_generic_c1.hasAnalyticCover_signRegion 6 m Set.univ
      isOpen_univ f
      (fun i => Submission.Obl.k4_sign_graph_generic_c1.analyticOnNhd_graph_polynomial (p i)) B
  let : Countable C := hC.to_subtype
  apply Submission.Obl.k4_sign_graph_generic_c1.exists_open_c1_of_coordinate_sign_graph_cover
    hgraph (fun c : C => c.1.dim) (fun c => c.1.domain) (fun c => c.1.toFun)
    (fun c => c.1.isOpen_domain)
  · intro c
    exact c.1.analyticOnNhd_toFun.contDiffOn_of_completeSpace
  · intro c x hx
    have hmem : c.1.toFun x ∈
        Submission.Obl.k4_sign_graph_generic_c1.signRegion Set.univ f B := by
      rw [hcover]
      exact Set.mem_iUnion.mpr ⟨c.1, Set.mem_iUnion.mpr ⟨c.2, x, hx, rfl⟩⟩
    exact hmem.2
  · intro x hx
    have hmem : x ∈ Submission.Obl.k4_sign_graph_generic_c1.signRegion Set.univ f B :=
      ⟨Set.mem_univ _, hx⟩
    rw [hcover] at hmem
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨hc, z, hz, heq⟩ := Set.mem_iUnion.mp hc
    exact ⟨⟨c, hc⟩, z, hz, heq⟩
